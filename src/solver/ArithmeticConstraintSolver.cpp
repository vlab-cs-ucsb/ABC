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

ArithmeticConstraintSolver::ArithmeticConstraintSolver(Script_ptr script,
    SymbolTable_ptr symbol_table) :
    AstTraverser(script), symbol_table(symbol_table),
    arithmetic_formula_generator(script, symbol_table) {
  setCallbacks();
}

ArithmeticConstraintSolver::~ArithmeticConstraintSolver() {
}

void ArithmeticConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "start";
  arithmetic_formula_generator.visit(root);
  string_terms_map = arithmetic_formula_generator.getStringTermsMap();
  visitScript(root);
  end();
}

void ArithmeticConstraintSolver::end() {
}

void ArithmeticConstraintSolver::setCallbacks() {
  auto term_callback = [this] (Term_ptr term) -> bool {
    switch (term->getType()) {
      case Term::Type::NOT:
      case Term::Type::EQ:
      case Term::Type::NOTEQ:
      case Term::Type::GT:
      case Term::Type::GE:
      case Term::Type::LT:
      case Term::Type::LE: {
        DVLOG(VLOG_LEVEL) << "visit: " << *term;
        ArithmeticFormula_ptr formula = arithmetic_formula_generator.getTermFormula(term);
        if (formula == nullptr) {
          return false;
        }

        DVLOG(VLOG_LEVEL) << "Linear Arithmetic Equation: " << *formula;
        BinaryIntAutomaton_ptr binary_int_auto = BinaryIntAutomaton::makeAutomaton(formula->clone());

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
  symbol_table->push_scope(script);
  visit_children_of(script);
  symbol_table->pop_scope(); // global scope, it is reachable via script pointer all the time
}

void ArithmeticConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL)<< "visit: " << *assert_command;
  AstTraverser::visit(assert_command->term);
}

/**
 * TODO Add a cache in case there are multiple ands
 */
void ArithmeticConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
  bool is_satisfiable = true;
  ArithmeticFormula_ptr formula = nullptr;
  Value_ptr result = nullptr, param = nullptr, and_value = nullptr;
  for (auto& term : *(and_term->term_list)) {
    formula = arithmetic_formula_generator.getTermFormula(term);
    if (formula != nullptr) {
      visit(term);
      param = getTermValue(term);
      is_satisfiable = is_satisfiable and param->isSatisfiable();
      if (is_satisfiable) {
        if (result == nullptr) {
          result = param->clone();
        } else {
          and_value = result->intersect(param);
          delete result;
          result = and_value;
        }
      } else {
        result = new Value(BinaryIntAutomaton::makePhi(formula->clone()));
        break;
      }
      clearTermValue(term);
    }
  }

  for (auto& term : *(and_term->term_list)) {
    formula = arithmetic_formula_generator.getTermFormula(term);
    if (formula != nullptr) {
      term_value_index[term] = and_term;
      clearTermValue(term);
    }
  }

  setTermValue(and_term, result);
}

void ArithmeticConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

Value_ptr ArithmeticConstraintSolver::getTermValue(Term_ptr term) {
  Term_ptr key = term;
  auto it1 = term_value_index.find(term);
  if (it1 != term_value_index.end()) {
    key = it1->second;
  }

  auto it2 = term_values.find(key);
  if (it2 != term_values.end()) {
    return it2->second;
  }

  return nullptr;
}

bool ArithmeticConstraintSolver::setTermValue(Term_ptr term, Value_ptr value) {
  auto result = term_values.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL)<< "value is already computed for term: " << *term;
  }
  term_value_index[term] = term;
  return result.second;
}

void ArithmeticConstraintSolver::clearTermValues() {
  for (auto& entry : term_values) {
    delete entry.second;
  }

  term_values.clear();
}

void ArithmeticConstraintSolver::clearTermValue(Term_ptr term) {
  auto it = term_values.find(term);
  if (it != term_values.end()) {
    delete it->second;
    term_values.erase(it);
  }
}


bool ArithmeticConstraintSolver::hasStringTerms(Term_ptr term) {
  return (string_terms_map.find(term) != string_terms_map.end());
}

TermList& ArithmeticConstraintSolver::getStringTermsIn(Term_ptr term) {
  return string_terms_map[term];
}

std::map<SMT::Term_ptr, SMT::Term_ptr>& ArithmeticConstraintSolver::getTermValueIndex() {
  return term_value_index;
}

ArithmeticConstraintSolver::TermValueMap& ArithmeticConstraintSolver::getTermValues() {
  return term_values;
}

std::map<SMT::Term_ptr, SMT::TermList>& ArithmeticConstraintSolver::getStringTermsMap() {
  return string_terms_map;
}

void ArithmeticConstraintSolver::assign(std::map<SMT::Term_ptr, SMT::Term_ptr>& term_value_index,
        TermValueMap& term_values,
        std::map<SMT::Term_ptr, SMT::TermList>& string_terms_map) {
  term_value_index = this->term_value_index;
  term_values = this->term_values;
  string_terms_map = this->string_terms_map;
}


} /* namespace Solver */
} /* namespace Vlab */
