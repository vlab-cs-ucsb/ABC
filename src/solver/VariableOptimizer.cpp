/*
 * VariableOptimizer.cpp
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#include "VariableOptimizer.h"

#include <glog/logging.h>
#include <glog/vlog_is_on.h>
#include <iostream>
#include <string>
#include <utility>

#include "smt/Visitor.h"
#include "Counter.h"
#include "OptimizationRuleRunner.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int VariableOptimizer::VLOG_LEVEL = 15;

VariableOptimizer::VariableOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
        : AstTraverser(script), symbol_table(symbol_table), target_type(Variable::Type::NONE),
          existential_elimination_phase(true) {
  setCallbacks();
}

VariableOptimizer::~VariableOptimizer() {
}

/**
 * Apply the following sequentially for Bool, Int, String variables
 * 1 - Collect existential elimination rules and apply them
 * 2 - Collect variable reduction rules and apply them
 */
void VariableOptimizer::start() {
  Counter counter(root, symbol_table);

  DVLOG(VLOG_LEVEL) << "Bool existential elimination";
  existential_elimination_phase = true;

  counter.start();
  target_type = Variable::Type::BOOL;
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();
  DVLOG(VLOG_LEVEL) << "Bool variable reduction";
  existential_elimination_phase = false;

  counter.start();
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();

  end();

  DVLOG(VLOG_LEVEL) << "Int existential elimination";
  existential_elimination_phase = true;

  counter.start();
  target_type = Variable::Type::INT;
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();

  DVLOG(VLOG_LEVEL) << "String existential elimination";
  counter.start();
  target_type = Variable::Type::STRING;
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();
}

void VariableOptimizer::end() {
  if (VLOG_IS_ON(VLOG_LEVEL)) {
    for (auto& rule_map : get_substitution_table()) {
      DVLOG(VLOG_LEVEL) << "Substitution map for scope: " << rule_map.first;
      for (auto& rule : rule_map.second) {
        if (QualIdentifier_ptr qid = dynamic_cast<QualIdentifier_ptr>(rule.second)) {
          DVLOG(VLOG_LEVEL) << "\t" << *rule.first << " (" << rule.first << ") -> " << qid->getVarName() << " ("
                                   << qid << " )";
        } else {
          DVLOG(VLOG_LEVEL) << "\t" << *rule.first << " (" << rule.first << ") -> " << *rule.second << " ("
                                   << rule.second << " )";
        }
      }
    }
  }

  OptimizationRuleRunner rule_runner(root, symbol_table, substitution_table);
  rule_runner.start();

  eq_constraint_count.clear();
  reset_substitution_rules();
//  Ast2Dot dot(&std::cout);
//  dot.inspectAST(root);
}

void VariableOptimizer::setCallbacks() {
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

void VariableOptimizer::visitAnd(And_ptr and_term) {
  visit_children_of(and_term);
}

void VariableOptimizer::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void VariableOptimizer::visitEq(Eq_ptr eq_term) {
  if (existential_elimination_phase) {
    if (Term::Type::QUALIDENTIFIER == eq_term->left_term->type()
            and Term::Type::QUALIDENTIFIER == eq_term->right_term->type()) {

      Variable_ptr left_var = symbol_table->getVariable(eq_term->left_term);
      Variable_ptr right_var = symbol_table->getVariable(eq_term->right_term);
//			std::cout << "rule add = " << *left_var << " " << *right_var << std::endl;
//			std::cout << *left_var << ": " << symbol_table -> get_local_count(left_var->getName()) << ", " << symbol_table -> get_total_count(left_var->getName()) << std::endl;
//			std::cout << *right_var << ": " << symbol_table -> get_local_count(right_var->getName()) << ", " << symbol_table -> get_total_count(right_var->getName()) << std::endl;

      if (left_var->getType() == target_type) {
        int left_var_local_count = symbol_table->get_local_count(left_var);
        int right_var_local_count = symbol_table->get_local_count(right_var);
        if (left_var_local_count <= right_var_local_count) {
          add_variable_substitution_rule(left_var, right_var, eq_term->right_term);
        } else {
          add_variable_substitution_rule(right_var, left_var, eq_term->left_term);
        }
      }
    }
  }
  /**
   * We can eliminate boolean variables that are used for asserting some other constraints
   * Following are the conditions to do reduction. Reduction rules are applied in add_variable_substitution_rule function
   * 1 - Variable may appear in only at most one constraint with other theories
   * 2 - Variable may appear in other places with some other boolean variables
   */
  else if (Variable::Type::BOOL == target_type) {
    if ((Term::Type::QUALIDENTIFIER == eq_term->left_term->type()
            or Term::Type::QUALIDENTIFIER == eq_term->right_term->type())
            and (Term::Type::QUALIDENTIFIER != eq_term->left_term->type()
                    or Term::Type::QUALIDENTIFIER != eq_term->right_term->type())) {

      Variable_ptr target_variable =
              (Term::Type::QUALIDENTIFIER == eq_term->left_term->type()) ?
                      symbol_table->getVariable(eq_term->left_term) : symbol_table->getVariable(eq_term->right_term);

      if (target_variable->getType() == target_type) {
        Term_ptr target_term =
                (Term::Type::QUALIDENTIFIER == eq_term->left_term->type()) ?
                        eq_term->right_term : eq_term->left_term;

//       std::cout << "rule add = " << *target_variable << " " << *target_term << std::endl;

        add_variable_substitution_rule(target_variable, target_term);

      }
    }
  }
}

void VariableOptimizer::add_variable_substitution_rule(Variable_ptr subject_var, Variable_ptr target_var,
        Term_ptr target_term) {
  if (subject_var->isSymbolic()) {
    return;
  }

  bool iterate_substitution = true;
  while (iterate_substitution) {
    iterate_substitution = false;
    /* 1 - Update the target if the target variable is already a subject in the substitution map (rule transition) */
    auto substitution_rules = get_substitution_map();
    auto it = substitution_rules.find(target_var);
    if (it != substitution_rules.end()) {
      target_term = it->second;
    }

    /* 2 - Insert substitution rule */
    auto target_term_clone = target_term->clone();
    if (not add_substitution_rule(subject_var, target_term_clone)) {
      delete target_term_clone; target_term_clone = nullptr;
      // 2a - if there is a duplicated rule, a -> b, a -> c, add a rule for for c -> b instead of a -> c
      if (QualIdentifier_ptr qid = dynamic_cast<QualIdentifier_ptr>(target_term)) {
        auto current_target = substitution_rules[subject_var];
        auto new_subject = symbol_table->getVariable(qid->getVarName());
        if (QualIdentifier_ptr current_target_qid = dynamic_cast<QualIdentifier_ptr>(current_target)) {
          subject_var = new_subject;
          target_var = symbol_table->getVariable(current_target_qid->getVarName());
          target_term = current_target;
          iterate_substitution = true;
          DVLOG(VLOG_LEVEL) << "Substitution rule iterates one more time with new parameters to handle transitive substitutions...";
          continue;
        }
      }
      LOG(FATAL)<< "A variable cannot have multiple substitution rule: " << *subject_var << " -> " << *target_var << " (updated to: " << *target_term << ")";
    }

    /* 3 - Update a rule with the target if the subject variable is already a target */
    for (auto& substitution_rule : get_substitution_map()) {
      if (Term::Type::QUALIDENTIFIER == substitution_rule.second->type()) {
        if (subject_var == symbol_table->getVariable(substitution_rule.second)) {
          Term_ptr tmp_term = substitution_rule.second;
          substitution_rule.second = target_term->clone();
          delete tmp_term;
        }
      }
    }

  }
}

/**
 * Adds substitution rule if it is only in one equality
 */
void VariableOptimizer::add_variable_substitution_rule(Variable_ptr subject_var, Term_ptr target_term) {
  if (subject_var->isSymbolic()) {
    return;
  }
  eq_constraint_count[subject_var]++;
  switch (eq_constraint_count[subject_var]) {
  case 1:
    add_substitution_rule(subject_var, target_term->clone());
    break;
  case 2:
    remove_substitution_rule(subject_var);
    break;
  default:
    break;
  }
}

bool VariableOptimizer::add_substitution_rule(Variable_ptr variable, Term_ptr target_term) {
  auto result = substitution_table[symbol_table->top_scope()].insert(std::make_pair(variable, target_term));
  return result.second;
}

bool VariableOptimizer::remove_substitution_rule(Variable_ptr variable) {
  auto current_scope = symbol_table->top_scope();
  auto it = substitution_table[current_scope].find(variable);
  if (it != substitution_table[current_scope].end()) {
    substitution_table[current_scope].erase(it);
    return true;
  }
  return false;
}

Term_ptr VariableOptimizer::get_substitution_term(Variable_ptr variable) {
  auto current_scope = symbol_table->top_scope();
  auto it = substitution_table[current_scope].find(variable);
  if (it == substitution_table[current_scope].end()) {
    return nullptr;
  }
  return it->second;
}

/**
 * Returns rules for the current scope
 */
SubstitutionMap& VariableOptimizer::get_substitution_map() {
  return substitution_table[symbol_table->top_scope()];
}

/**
 * Returns rules within all scopes
 */
SubstitutionTable& VariableOptimizer::get_substitution_table() {
  return substitution_table;
}

void VariableOptimizer::reset_substitution_rules() {
  for (auto& map_pair : substitution_table) {
    for (auto& rule_pair : map_pair.second) {
      delete rule_pair.second;
    }
  }
  substitution_table.clear();
}

} /* namespace Solver */
} /* namespace Vlab */

