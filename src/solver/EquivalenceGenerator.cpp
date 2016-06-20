/*
 * VariableOptimizer.cpp
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#include "EquivalenceGenerator.h"

#include <glog/logging.h>
#include <glog/vlog_is_on.h>
#include <iostream>
#include <string>
#include <utility>

#include "smt/Visitor.h"
#include "Counter.h"
#include "Ast2Dot.h"

#include "EquivClassRuleRunner.h"


namespace Vlab {
namespace Solver {

using namespace SMT;

const int EquivalenceGenerator::VLOG_LEVEL = 15;

EquivalenceGenerator::EquivalenceGenerator(Script_ptr script, SymbolTable_ptr symbol_table)
  : AstTraverser(script), symbol_table_(symbol_table) {
  setCallbacks();
}

EquivalenceGenerator::~EquivalenceGenerator() {
}

void EquivalenceGenerator::start() {
  Counter counter(root, symbol_table_);
  DVLOG(VLOG_LEVEL) << "Starting the EquivalenceGenerator";
  counter.start();
  symbol_table_->push_scope(root);
  visitScript(root);
  bool is_false = make_substitution_rules();
  if (is_false) {
    set_to_false_.insert(root);
  }
  symbol_table_->pop_scope();
  clear_mappings();
  end();
}

void EquivalenceGenerator::end() {
  for (auto& map_pair : substitution_map_) {
    SubstitutionMap vmap = substitution_map_[map_pair.first];
    for (auto& pair : vmap) {
      DVLOG(VLOG_LEVEL) << "In scope " << map_pair.first;
      if (Term::Type::TERMCONSTANT == pair.second->type()) {
        DVLOG(VLOG_LEVEL) << "Replacing " << pair.first->getName() << " with " << dynamic_cast<TermConstant_ptr>(pair.second)->getValue();
      } else if (Term::Type::QUALIDENTIFIER == pair.second->type()) {
        DVLOG(VLOG_LEVEL) << "Replacing " << pair.first->getName() << " with " << (symbol_table_->getVariable(pair.second))->getName();
      } else {
        DVLOG(VLOG_LEVEL) << "UNEXPECTED TERM IN REPLACEMENT MAP!";
      }
    }
  }
  EquivClassRuleRunner rule_runner(root, symbol_table_, substitution_map_, set_to_false_);
  rule_runner.start();

  reset_substitution_rules();
}

void EquivalenceGenerator::setCallbacks() {
  auto term_callback = [] (Term_ptr term) -> bool {
    return false;
  };

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  setCommandPreCallback(command_callback);
  setTermPreCallback(term_callback);
}

void EquivalenceGenerator::visitAnd(And_ptr and_term) {
  visit_children_of(and_term);
}

void EquivalenceGenerator::visitOr(Or_ptr or_term) {
  for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
    symbol_table_->push_scope(*iter);
    visit(*iter);
    bool is_false = make_substitution_rules();
    if (is_false) {
      set_to_false_.insert(*iter);
    }
    clear_mappings();
    symbol_table_->pop_scope();
    iter++;
  }
}

void EquivalenceGenerator::visitEq(Eq_ptr eq_term) {
  //DVLOG(VLOG_LEVEL) << "Visiting an eq";
  std::string rep_left = get_string_rep(eq_term->left_term);
  std::string rep_right = get_string_rep(eq_term->right_term);

  if (term_to_component_map_.find(rep_left) != term_to_component_map_.end()) {
    if (term_to_component_map_.find(rep_right) != term_to_component_map_.end()) {
      if (term_to_component_map_[rep_right] != term_to_component_map_[rep_left]) {
        merge(term_to_component_map_[rep_right], term_to_component_map_[rep_left]);
      }
    } else {
      extend_equiv_class(rep_right, rep_left);
    }
  } else if (term_to_component_map_.find(rep_right) != term_to_component_map_.end()) {
    extend_equiv_class(rep_left, rep_right);
  } else {
    //Make a new equivalence class. Insert both the left and right terms.
    term_to_component_map_[rep_left] = sub_components_.size();
    term_to_component_map_[rep_right] = sub_components_.size();
    std::set<std::string> component;
    component.insert(rep_left);
    component.insert(rep_right);
    sub_components_.push_back(component);
  }
}

bool EquivalenceGenerator::make_substitution_rules() {
  //First make a set containing the unique equivalence classes
  std::set<std::set<std::string>> unique_components_;
  for (auto& entry : term_to_component_map_) {
    unique_components_.insert(sub_components_[entry.second]);
  }
  //For each equivalence class, choose a variable representative and when appropriate, a constant representative
  Term_ptr rep_variable;
  Term_ptr rep_constant;
  for (auto& s : unique_components_) {
    rep_variable = nullptr;
    rep_constant = nullptr;
    //Currently no procedure in place for choosing the variable representive.
    for (auto& e : s) {
      if (variables_.find(e) != variables_.end()) {
        rep_variable = variables_[e];
      }
      if (constants_.find(e) != constants_.end()) {
        rep_constant = constants_[e];
      }
    }
    //Check and see if there is a contradiction based on two non-equivalent constants being in the same equivalence class.
    if (rep_constant != nullptr) {
      for (auto& e : s) {
        if (constants_.find(e) != constants_.end()) {
          if (dynamic_cast<TermConstant_ptr>(rep_constant)->getValue() != e) {
            //DVLOG(VLOG_LEVEL) << "CONTRADICTION IN THIS SCOPE!";
            return true;
          }
        }
      }
    }
    if (rep_constant != nullptr && rep_variable != nullptr) {
      //Uncomment the below line in order to allow the variable representative to be replaced by the constant representative.
      //add_variable_substitution_rule(symbol_table_->getVariable(rep_variable), rep_constant);
    }
    //Add the substituion rules for variables
    if (rep_variable != nullptr) {
      for (auto& e : s) {
        if (variables_.find(e) != variables_.end() && symbol_table_->getVariable(e) != symbol_table_->getVariable(rep_variable)) {
          add_variable_substitution_rule(symbol_table_->getVariable(e), rep_variable);
        }
      }
    }
  }
  return false;
}


bool EquivalenceGenerator::add_variable_substitution_rule(Variable_ptr variable, Term_ptr target_term) {
  auto result = substitution_map_[symbol_table_->top_scope()].insert(std::make_pair(variable, target_term));
  return result.second;
}

//Update an equivalence class
void EquivalenceGenerator::extend_equiv_class(std::string to_add, std::string to_add_to) {
  term_to_component_map_[to_add] = term_to_component_map_[to_add_to];
  sub_components_[term_to_component_map_[to_add]].insert(to_add);
}

//Generate a string representation of a term!
std::string EquivalenceGenerator::get_string_rep(Term_ptr term) {
  std::string rep = Ast2Dot::toString(term);
  if (Term::Type::QUALIDENTIFIER == term->type()) {
    rep = (symbol_table_->getVariable(term))->getName();
    variables_[rep] = term;
  }
  if (Term::Type::TERMCONSTANT == term->type()) {
    rep = dynamic_cast<TermConstant_ptr>(term)->getValue();
    constants_[rep] = term;
  }
  return rep;
}

//Merge two equivalence classes
void EquivalenceGenerator::merge(int a, int b) {
  int to_merge_to = b;
  int to_merge = a;
  if (sub_components_[a].size() > sub_components_[b].size()) {
    to_merge_to = a;
    to_merge = b;
  }
  for (auto& e : sub_components_[to_merge]) {
    sub_components_[to_merge_to].insert(e);
    term_to_component_map_[e] = to_merge_to;
  }
}


void EquivalenceGenerator::reset_substitution_rules() {
  substitution_map_.clear();
}


void EquivalenceGenerator::clear_mappings() {
  term_to_component_map_.clear();
  sub_components_.clear();
}

} /* namespace Solver */
} /* namespace Vlab */

