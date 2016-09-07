/*
 * ArithmeticConstraintSolver.cpp
 *
 *  Created on: Nov 1, 2015
 *      Author: baki
 */

#include "ArithmeticConstraintSolver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int ArithmeticConstraintSolver::VLOG_LEVEL = 11;

ArithmeticConstraintSolver::ArithmeticConstraintSolver(Script_ptr script, SymbolTable_ptr symbol_table,
                                                       ConstraintInformation_ptr constraint_information,
                                                       bool is_natural_numbers_only)
    : AstTraverser(script),
      is_natural_numbers_only_ { is_natural_numbers_only },
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      arithmetic_formula_generator_(script, symbol_table, constraint_information) {
  setCallbacks();
}

ArithmeticConstraintSolver::~ArithmeticConstraintSolver() {
}

/**
 * Used to solve local arithmetic constraints
 */
void ArithmeticConstraintSolver::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint solving starts at node: " << node;
  arithmetic_formula_generator_.start(node);
  if (arithmetic_formula_generator_.has_arithmetic_formula()) {
    string_terms_map_ = arithmetic_formula_generator_.get_string_terms_map();
    this->Visitor::visit(node);
  }
  end();
}

void ArithmeticConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint solving starts at root";
  arithmetic_formula_generator_.start();
  if (arithmetic_formula_generator_.has_arithmetic_formula()) {
    string_terms_map_ = arithmetic_formula_generator_.get_string_terms_map();
    visitScript(root);
  }
  end();
}

void ArithmeticConstraintSolver::end() {
  arithmetic_formula_generator_.end();
}

/**
 * TODO move group updating inside AND and OR
 */
void ArithmeticConstraintSolver::setCallbacks() {
  auto term_callback =
      [this] (Term_ptr term) -> bool {
        switch (term->type()) {
          case Term::Type::NOT:
          case Term::Type::EQ:
          case Term::Type::NOTEQ:
          case Term::Type::GT:
          case Term::Type::GE:
          case Term::Type::LT:
          case Term::Type::LE:
          case Term::Type::QUALIDENTIFIER: {
            auto formula = arithmetic_formula_generator_.get_term_formula(term);
            if (formula != nullptr) {
              DVLOG(VLOG_LEVEL) << "Linear Arithmetic Equation: " << *formula << "@" << term;
              auto binary_int_auto = BinaryIntAutomaton::MakeAutomaton(formula->clone(), is_natural_numbers_only_);
              auto result = new Value(binary_int_auto);
              set_term_value(term, result);
            }
            break;
          }
          default:
          break;
        }
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

void ArithmeticConstraintSolver::visitScript(Script_ptr script) {
  symbol_table_->push_scope(script);
  visit_children_of(script);
  symbol_table_->pop_scope();  // global scope, it is reachable via script pointer all the time
}

void ArithmeticConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;
  AstTraverser::visit(assert_command->term);
}

/**
 * TODO Add a cache in case there are multiple ands
 */
void ArithmeticConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;

  //if this is not a component descent into children and do not create result automaton
  if (not constraint_information_->is_component(and_term)) {
    visit_children_of(and_term);
    return;
  }

  bool is_satisfiable = true;

  for (auto& term : *(and_term->term_list)) {
    auto formula = arithmetic_formula_generator_.get_term_formula(term);
    if (formula != nullptr) {
      visit(term);
      auto param = get_term_value(term);
      is_satisfiable = is_satisfiable and param->isSatisfiable();
      std::string group_name = arithmetic_formula_generator_.get_term_group_name(term);
      IntersectGroupValue(group_name, param->clone());
      clear_term_value(term);
      arithmetic_formula_generator_.add_group_to_component(group_name, and_term);
      if (not is_satisfiable) {
        break;
      }
    }
  }

  /**
   * We may need to compute an automaton for the and_term that combines all groups
   */
  if (symbol_table_->top_scope() != root) {
    LOG(FATAL)<< "implement me";
    std::string group_name = arithmetic_formula_generator_.generate_group_for_component(and_term);
    auto groups = arithmetic_formula_generator_.get_groups_in_component(and_term);
    LOG(FATAL)<< "Remap all groups to one";
    LOG(FATAL)<< "In case of mixed constraints may need to keep original automata";
    // if there is a one group replace it with new group
    // if there is more combine them into one
    if (is_satisfiable) {
      auto it = groups.begin();
      set_group_value(group_name, symbol_table_->get_value(*it)->clone());
      while (++it != groups.end()) {
        LOG(FATAL) << "this intersection require updates on automaton tracks";
        IntersectGroupValue(group_name, symbol_table_->get_value(*it)->clone());
      }
    } else {
      auto formula = arithmetic_formula_generator_.get_group_formula(group_name);
      auto value = new Value(Theory::BinaryIntAutomaton::MakePhi(formula, is_natural_numbers_only_));
      set_group_value(group_name, value);
    }

  } else {
    // Update all group automaton
    if (not is_satisfiable) {
      for (const auto& group_name : arithmetic_formula_generator_.get_groups_in_component(and_term)) {
        auto formula = arithmetic_formula_generator_.get_group_formula(group_name);
        auto value = new Value(Theory::BinaryIntAutomaton::MakePhi(formula, is_natural_numbers_only_));
        set_group_value(group_name, value);
      }
    }
    set_term_value(and_term, new Value(is_satisfiable));
  }
}

void ArithmeticConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
  LOG(FATAL) << "implement me";
  for (auto& term : *(or_term->term_list)) {
    symbol_table_->push_scope(term);
    visit(term);
    symbol_table_->pop_scope();
  }
}

std::string ArithmeticConstraintSolver::get_int_variable_name(SMT::Term_ptr term) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  return symbol_table_->get_var_name_for_node(key, Variable::Type::INT);
}

Value_ptr ArithmeticConstraintSolver::get_term_value(Term_ptr term) {
  auto it = term_values_.find(term);
  if (it != term_values_.end()) {
    return it->second;
  }
//  std::string group_name = arithmetic_formula_generator_.get_term_group_name(term);
//  if(!group_name.empty()) {
//    return symbol_table_->get_value(group_name);
//  } else {
//
//  }
  return nullptr;
}

bool ArithmeticConstraintSolver::set_term_value(Term_ptr term, Value_ptr value) {
  auto result = term_values_.insert({term, value});
  if (result.second == false) {
    LOG(FATAL) << "Term automaton is already computed: " << *term << "@" << term;
  }
//  std::string group_name = arithmetic_formula_generator_.get_term_group_name(term);
//  if(!group_name.empty()) {
//    symbol_table_->set_value(group_name,value);
//    return true;
//  }
  return result.second;
}

bool ArithmeticConstraintSolver::UpdateTermValue(Term_ptr term, Value_ptr value) {
LOG(FATAL) << "fix me";
//  std::string group_name = arithmetic_formula_generator_.get_term_group_name(term);
//  if(!group_name.empty()) {
//    symbol_table_->UpdateValue(group_name,value);
//    return true;
//  }
  return false;
}

void ArithmeticConstraintSolver::clear_term_values() {
  for (auto& entry : term_values_) {
    delete entry.second;
  }

  term_values_.clear();
}

void ArithmeticConstraintSolver::clear_term_value(Term_ptr term) {
  auto it = term_values_.find(term);
  if (it != term_values_.end()) {
    delete it->second;
    term_values_.erase(it);
  }
}

bool ArithmeticConstraintSolver::has_string_terms(Term_ptr term) {
  return (string_terms_map_.find(term) != string_terms_map_.end());
}

TermList& ArithmeticConstraintSolver::get_string_terms_in(Term_ptr term) {
  return string_terms_map_[term];
}

std::map<SMT::Term_ptr, SMT::TermList>& ArithmeticConstraintSolver::get_string_terms_map() {
  return string_terms_map_;
}

void ArithmeticConstraintSolver::assign(std::map<SMT::Term_ptr, SMT::Term_ptr>& term_value_index,
                                        TermValueMap& term_values,
                                        std::map<SMT::Term_ptr, SMT::TermList>& string_terms_map) {
  term_value_index = this->term_value_index_;
  term_values = this->term_values_;
  string_terms_map = this->string_terms_map_;
}

bool ArithmeticConstraintSolver::set_group_value(std::string group_name, Value_ptr value) {
  if (symbol_table_->get_variable_unsafe(group_name) == nullptr) {
    symbol_table_->add_variable(new Variable(group_name, Variable::Type::INT));
    return symbol_table_->set_value(group_name, value);
  } else {
    auto old_value = symbol_table_->get_value(group_name);
    auto result = symbol_table_->set_value(group_name, value);
    delete old_value;
    return result;
  }
}

bool ArithmeticConstraintSolver::IntersectGroupValue(std::string group_name, Value_ptr value) {
  if (symbol_table_->get_variable_unsafe(group_name) == nullptr) {
    symbol_table_->add_variable(new Variable(group_name, Variable::Type::INT));
    return symbol_table_->set_value(group_name, value);
  } else {
    auto result = symbol_table_->IntersectValue(group_name, value);
    delete value;
    return result;
  }
}

bool ArithmeticConstraintSolver::UnionGroupValue(std::string group_name, Value_ptr value) {
  if (symbol_table_->get_variable_unsafe(group_name) == nullptr) {
    symbol_table_->add_variable(new Variable(group_name, Variable::Type::INT));
    return symbol_table_->set_value(group_name, value);
  } else {
    auto result = symbol_table_->UnionValue(group_name, value);
    delete value;
    return result;
  }
}

} /* namespace Solver */
} /* namespace Vlab */
