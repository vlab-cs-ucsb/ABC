/*
 * ArithmeticConstraintSolver.cpp
 *
 *  Created on: Nov 1, 2015
 *      Author: baki
 */

#include "ArithmeticConstraintSolver.h"

#include <glog/logging.h>
#include <iostream>
#include <utility>

#include "smt/ast.h"
#include "smt/Visitor.h"
#include "theory/ArithmeticFormula.h"
#include "theory/BinaryIntAutomaton.h"

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
      arithmetic_formula_generator_(script, symbol_table) {
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
  string_terms_map_ = arithmetic_formula_generator_.get_string_terms_map();
  this->Visitor::visit(node);
  end();
}

void ArithmeticConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint solving starts at root";
  arithmetic_formula_generator_.start();
  string_terms_map_ = arithmetic_formula_generator_.get_string_terms_map();
  visitScript(root);
  end();
}

void ArithmeticConstraintSolver::end() {
  arithmetic_formula_generator_.end();
}

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
            DVLOG(VLOG_LEVEL) << "visit: " << *term;
            ArithmeticFormula_ptr formula = arithmetic_formula_generator_.get_term_formula(term);
            if (formula == nullptr) {
              return false;
            }

            DVLOG(VLOG_LEVEL) << "Linear Arithmetic Equation: " << *formula;
            BinaryIntAutomaton_ptr binary_int_auto = BinaryIntAutomaton::makeAutomaton(formula->clone(), is_natural_numbers_only_);
            Value_ptr result = new Value(binary_int_auto);

            setTermValue(term, result);
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
    setTermValue(and_term, nullptr);
    return;
  }

  bool is_satisfiable = true;
  ArithmeticFormula_ptr formula = nullptr;
  Value_ptr automaton_result = nullptr, param = nullptr, and_value = nullptr;

  for (auto& term : *(and_term->term_list)) {
    formula = arithmetic_formula_generator_.get_term_formula(term);
    if (formula != nullptr) {
      visit(term);
      param = getTermValue(term);
      is_satisfiable = is_satisfiable and param->isSatisfiable();
      if (is_satisfiable) {
        if (automaton_result == nullptr) {
          automaton_result = param->clone();
        } else {
          and_value = automaton_result->intersect(param);
          delete automaton_result;
          automaton_result = and_value;
        }
      } else {
        automaton_result = new Value(BinaryIntAutomaton::makePhi(formula->clone(), is_natural_numbers_only_));
        break;
      }
      clearTermValue(term);
    }
  }

  for (auto& term : *(and_term->term_list)) {
    formula = arithmetic_formula_generator_.get_term_formula(term);
    if (formula != nullptr) {
      term_value_index_[term] = and_term;
      clearTermValue(term);
    }
  }

  // Add a variable to symbol table to represent binary integer automaton
  // Binary automaton is added to symbol table in constraint solver
  if (automaton_result != nullptr) {
    std::string name = symbol_table_->get_var_name_for_node(and_term, Variable::Type::INT);
    symbol_table_->addVariable(new Variable(name, Variable::Type::INT));
  }

  setTermValue(and_term, automaton_result);
}

void ArithmeticConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
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

Value_ptr ArithmeticConstraintSolver::getTermValue(Term_ptr term) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  auto it2 = term_values_.find(key);
  if (it2 != term_values_.end()) {
    return it2->second;
  }

  return nullptr;
}

bool ArithmeticConstraintSolver::setTermValue(Term_ptr term, Value_ptr value) {
  auto result = term_values_.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL)<< "value is already computed for term: " << *term;
  }
  term_value_index_[term] = term;
  return result.second;
}

/**
 * Only updates pointer value, memory management should be done in the calling context
 */
bool ArithmeticConstraintSolver::update_term_value_pointer(SMT::Term_ptr term, Value_ptr value) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  auto it2 = term_values_.find(key);
  if (it2 != term_values_.end()) {
    it2->second = value;
    return true;
  }

  return false;
}

void ArithmeticConstraintSolver::clearTermValues() {
  for (auto& entry : term_values_) {
    delete entry.second;
  }

  term_values_.clear();
}

void ArithmeticConstraintSolver::clearTermValue(Term_ptr term) {
  auto it = term_values_.find(term);
  if (it != term_values_.end()) {
    delete it->second;
    term_values_.erase(it);
  }
}

bool ArithmeticConstraintSolver::hasStringTerms(Term_ptr term) {
  return (string_terms_map_.find(term) != string_terms_map_.end());
}

TermList& ArithmeticConstraintSolver::getStringTermsIn(Term_ptr term) {
  return string_terms_map_[term];
}

std::map<SMT::Term_ptr, SMT::Term_ptr>& ArithmeticConstraintSolver::getTermValueIndex() {
  return term_value_index_;
}

ArithmeticConstraintSolver::TermValueMap& ArithmeticConstraintSolver::getTermValues() {
  return term_values_;
}

std::map<SMT::Term_ptr, SMT::TermList>& ArithmeticConstraintSolver::getStringTermsMap() {
  return string_terms_map_;
}

void ArithmeticConstraintSolver::assign(std::map<SMT::Term_ptr, SMT::Term_ptr>& term_value_index,
                                        TermValueMap& term_values,
                                        std::map<SMT::Term_ptr, SMT::TermList>& string_terms_map) {
  term_value_index = this->term_value_index_;
  term_values = this->term_values_;
  string_terms_map = this->string_terms_map_;
}

} /* namespace Solver */
} /* namespace Vlab */
