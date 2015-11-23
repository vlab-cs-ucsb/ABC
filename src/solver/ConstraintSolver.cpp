/*
 * ConstraintSolver.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "ConstraintSolver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int ConstraintSolver::VLOG_LEVEL = 11;

ConstraintSolver::ConstraintSolver(Script_ptr script,
    SymbolTable_ptr symbol_table) :
    root(script), symbol_table(symbol_table), arithmetic_constraint_solver(script, symbol_table) {
}

ConstraintSolver::~ConstraintSolver() {
}

void ConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "start";
  arithmetic_constraint_solver.start();
  visit(root);
  end();
}

void ConstraintSolver::end() {
}

void ConstraintSolver::visitScript(Script_ptr script) {
  symbol_table->push_scope(script);
  Visitor::visit_children_of(script);
  symbol_table->pop_scope(); // global scope, it is reachable via script pointer all the time
}

void ConstraintSolver::visitCommand(Command_ptr command) {
  LOG(ERROR)<< "'" << *command<< "' is not expected.";
}

void ConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;
  check_and_visit(assert_command->term);

  Value_ptr result = getTermValue(assert_command->term);
  bool is_satisfiable = result->isSatisfiable();
  symbol_table->updateSatisfiability(is_satisfiable);
  symbol_table->setScopeSatisfiability(is_satisfiable);
  if ((Term::Type::OR not_eq assert_command->term->getType()) and
          (Term::Type::AND not_eq assert_command->term->getType())) {

    if (is_satisfiable) {
      update_variables();
    }
  }
  clearTermValues();
}

void ConstraintSolver::visitTerm(Term_ptr term) {
}

void ConstraintSolver::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ConstraintSolver::visitExists(Exists_ptr exists_term) {
}

void ConstraintSolver::visitForAll(ForAll_ptr for_all_term) {
}

void ConstraintSolver::visitLet(Let_ptr let_term) {
}

/**
 * TODO Add a cache in case there are multiple ands
 */
void ConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
  bool is_satisfiable = true;
  Value_ptr result = nullptr, param = nullptr;
  for (auto& term : *(and_term->term_list)) {
    check_and_visit(term);
    param = getTermValue(term);
    is_satisfiable = is_satisfiable and param->isSatisfiable();
    if (is_satisfiable) {
      update_variables();
    } else {
      clearTermValues();
      break;
    }
    clearTermValues();
  }

  result = new Value(is_satisfiable);

  setTermValue(and_term, result);
}

void ConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;

  bool is_satisfiable = false;
  Value_ptr result = nullptr, param = nullptr;

  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    check_and_visit(term);

    param = getTermValue(term);

    if (Term::Type::AND not_eq term->getType()) {
      if (param->isSatisfiable()) {
        update_variables();
      }
      clearTermValues();
    }
    bool is_scope_satisfiable = param->isSatisfiable();
    symbol_table->setScopeSatisfiability(is_scope_satisfiable);
    is_satisfiable = is_satisfiable or is_scope_satisfiable;
    symbol_table->pop_scope();
    if (is_satisfiable) { //TODO for model counting we need to continue to calculate each term in disjunction
      LOG(INFO)<< "TODO: CONTINUE CALCULATION FOR MODEL COUNTING, PARAMETIRIZED THAT";
      break;
    }
  }

  result = new Value(is_satisfiable);

  setTermValue(or_term, result);
}

void ConstraintSolver::visitNot(Not_ptr not_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(not_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(not_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(not_term)) {
        path_trace.push_back(not_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in arithmetic automaton
      }
    }
    return;
  }

  visit_children_of(not_term);
  Value_ptr result = nullptr, param = getTermValue(not_term->term);

  switch (param->getType()) {
  case Value::Type::BOOl_CONSTANT: {
    result = param->complement();
    break;
  }
  case Value::Type::BOOL_AUTOMATON: {
    // 1- if singleton do not
    // 2- else over-approximate
    LOG(FATAL) << "implement me";
    break;
  }
  case Value::Type::INT_AUTOMATON: {
    if (param->getIntAutomaton()->isAcceptingSingleInt()) {
      result = param->complement();
    } else {
      result = param->clone();
    }
    break;
  }
  case Value::Type::INTBOOL_AUTOMATON: {
    // 1- if singleton do not
    // 2- else over-approximate
    LOG(FATAL) << "implement me";
    break;
  }
  case Value::Type::STRING_AUTOMATON: {
    // TODO multi-track automaton solves over-approximation problem in most cases
    if (param->getStringAutomaton()->isAcceptingSingleString()) {
      result = param->complement();
    } else {
      result = param->clone();
    }
    break;
  }
  default:
    result = param->complement();
  break;
}

  setTermValue(not_term, result);
}

void ConstraintSolver::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *u_minus_term;

  Value_ptr result = nullptr, param = getTermValue(u_minus_term->term);

  switch (param->getType()) {
  case Value::Type::INT_CONSTANT: {
    int data = (- param->getIntConstant());
    result = new Value(data);
    break;
  }
  case Value::Type::INT_AUTOMATON: {
    if (param->getIntAutomaton()->isAcceptingSingleInt()) {
      int value = (- param->getIntAutomaton()->getAnAcceptingInt());
      result = new Value(value);
    } else {
      result = new Value(param->getIntAutomaton()->uminus());
    }
    break;
  }
  case Value::Type::INTBOOL_AUTOMATON: {
    // do minus operation on automaton
    LOG(FATAL) << "implement me";
    break;
  }
  default:
  LOG(FATAL) << "unary minus term child is not computed properly: " << *(u_minus_term->term);
  break;
}

  setTermValue(u_minus_term, result);
}

void ConstraintSolver::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *minus_term;

  Value_ptr result = nullptr, param_left = getTermValue(minus_term->left_term),
      param_right = getTermValue(minus_term->right_term);

  result = param_left->minus(param_right);

  setTermValue(minus_term, result);
}

void ConstraintSolver::visitPlus(Plus_ptr plus_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *plus_term << " ...";

  Value_ptr result = nullptr, plus_value = nullptr, param = nullptr;
  path_trace.push_back(plus_term);
  for (auto& term_ptr : *(plus_term->term_list)) {
    visit(term_ptr);
    param = getTermValue(term_ptr);
    if (result == nullptr) {
      result = param->clone();
    } else {
      plus_value = result->plus(param);
      delete result;
      result = plus_value;
    }
  }
  path_trace.pop_back();
  setTermValue(plus_term, result);
}

void ConstraintSolver::visitTimes(Times_ptr times_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *times_term << " ...";

  Value_ptr result = nullptr, times_value = nullptr, param = nullptr;
  path_trace.push_back(times_term);
  for (auto& term_ptr : *(times_term->term_list)) {
    visit(term_ptr);
    param = getTermValue(term_ptr);
    if (result == nullptr) {
      result = param->clone();
    } else {
      times_value = result->times(param);
      delete result;
      result = times_value;
    }
  }
  path_trace.pop_back();
  setTermValue(times_term, result);
}

void ConstraintSolver::visitEq(Eq_ptr eq_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(eq_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(eq_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(eq_term)) {
        path_trace.push_back(eq_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in airhtmetic automaton
      }
    }
    return;
  }

  visit_children_of(eq_term);
  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(eq_term->left_term);
  param_right = getTermValue(eq_term->right_term);

  if (Value::Type::BOOl_CONSTANT == param_left->getType() and
          Value::Type::BOOl_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getBoolConstant() == param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType() and
          Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getIntConstant() == param_right->getIntConstant());
  } else {
    result = param_left->intersect(param_right);
  }

  setTermValue(eq_term, result);
}

void ConstraintSolver::visitNotEq(NotEq_ptr not_eq_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(not_eq_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(not_eq_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(not_eq_term)) {
        path_trace.push_back(not_eq_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in airhtmetic automaton
      }
    }
    return;
  }

  visit_children_of(not_eq_term);

  Value_ptr result = nullptr, param_left = nullptr,
          param_right = nullptr, intersection = nullptr;

  param_left = getTermValue(not_eq_term->left_term);
  param_right = getTermValue(not_eq_term->right_term);


  if (Value::Type::BOOl_CONSTANT == param_left->getType() and
          Value::Type::BOOl_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getBoolConstant() not_eq param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType() and
          Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getIntConstant() not_eq param_right->getIntConstant());
  } else {
    intersection = param_left->intersect(param_right);
    if (not intersection->isSatisfiable()) {
      result = new Value(true);
      delete intersection;
    } else {
      result = intersection;
    }
  }

  setTermValue(not_eq_term, result);
}

void ConstraintSolver::visitGt(Gt_ptr gt_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(gt_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(gt_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(gt_term)) {
        path_trace.push_back(gt_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in airhtmetic automaton
      }
    }
    return;
  }

  visit_children_of(gt_term);

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(gt_term->left_term);
  param_right = getTermValue(gt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isLessThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isGreaterThan(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *gt_term;
  }

  setTermValue(gt_term, result);
}

void ConstraintSolver::visitGe(Ge_ptr ge_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(ge_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(ge_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(ge_term)) {
        path_trace.push_back(ge_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in airhtmetic automaton
      }
    }
    return;
  }

  visit_children_of(ge_term);

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(ge_term->left_term);
  param_right = getTermValue(ge_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isLessThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isGreaterThanOrEqual(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *ge_term;
  }

  setTermValue(ge_term, result);
}

void ConstraintSolver::visitLt(Lt_ptr lt_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(lt_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(lt_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(lt_term)) {
        path_trace.push_back(lt_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in airhtmetic automaton
      }
    }
    return;
  }

  visit_children_of(lt_term);

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(lt_term->left_term);
  param_right = getTermValue(lt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isGreaterThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isLessThan(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *lt_term;
  }

  setTermValue(lt_term, result);
}

void ConstraintSolver::visitLe(Le_ptr le_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;
  Value_ptr arith_value = arithmetic_constraint_solver.getTermValue(le_term);
  if (arith_value != nullptr) {
    DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
    // TODO handle string terms in arithmetic constraint if any
    if (arithmetic_constraint_solver.hasStringTerms(le_term)) {
      for (auto& term : arithmetic_constraint_solver.getStringTermsIn(le_term)) {
        path_trace.push_back(le_term);
        visit(term);
        path_trace.pop_back();

        // TODO save that path trace to update variables in airhtmetic automaton
      }
    }
    return;
  }

  visit_children_of(le_term);

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(le_term->left_term);
  param_right = getTermValue(le_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isGreaterThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isLessThanOrEqual(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *le_term;
  }

  setTermValue(le_term, result);
}

void ConstraintSolver::visitConcat(Concat_ptr concat_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *concat_term << " ...";

  Value_ptr result = nullptr, concat_value = nullptr, param = nullptr;
  path_trace.push_back(concat_term);
  for (auto& term_ptr : *(concat_term->term_list)) {
    visit(term_ptr);
    param = getTermValue(term_ptr);
    if (result == nullptr) {
      result = param->clone();
    } else {
      concat_value = result->concat(param);
      delete result;
      result = concat_value;
    }
  }
  path_trace.pop_back();
  setTermValue(concat_term, result);
}

void ConstraintSolver::visitIn(In_ptr in_term) {
  visit_children_of(in_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *in_term;

  Value_ptr result = nullptr, param_left = getTermValue(in_term->left_term),
      param_right = getTermValue(in_term->right_term);

  if (Value::Type::STRING_AUTOMATON == param_left->getType()
      and Value::Type::STRING_AUTOMATON == param_right->getType()) {
    result = param_left->intersect(param_right);
  } else {
    LOG(FATAL) << "unexpected parameter(s) of '" << *in_term << "' term"; // handle cases in a better way
  }

  setTermValue(in_term, result);
}

/**
 * TODO check all boolean string functions right hand side
 * if there is no variable involved we can do precise calculation
 * otherwise discuss?? if it is problem
 */


void ConstraintSolver::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_in_term;

  Value_ptr result = nullptr, param_left = getTermValue(not_in_term->left_term),
      param_right = getTermValue(not_in_term->right_term);

  if (Value::Type::STRING_AUTOMATON == param_left->getType()
      and Value::Type::STRING_AUTOMATON == param_right->getType()) {
    result = param_left->difference(param_right);
  } else {
    LOG(FATAL) << "unexpected parameter(s) of '" << *not_in_term << "' term"; // handle cases in a better way
  }

  setTermValue(not_in_term, result);
}

void ConstraintSolver::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;

  Value_ptr result = nullptr, param = getTermValue(len_term->term);

  Theory::IntAutomaton_ptr int_auto = param->getStringAutomaton()->length();

  if (int_auto->isAcceptingSingleInt()) {
    result = new Value(int_auto->getAnAcceptingInt());
    delete int_auto; int_auto = nullptr;
  } else {
    result = new Value(int_auto);
  }

  setTermValue(len_term, result);
}

void ConstraintSolver::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *contains_term;

  Value_ptr result = nullptr, param_subject = getTermValue(contains_term->subject_term),
      param_search = getTermValue(contains_term->search_term);

  result = new Value(param_subject->getStringAutomaton()->contains(param_search->getStringAutomaton()));

  setTermValue(contains_term, result);
}

void ConstraintSolver::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_contains_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_contains_term->subject_term),
      param_search = getTermValue(not_contains_term->search_term);

  Theory::StringAutomaton_ptr contains_auto = param_subject->getStringAutomaton()->contains(param_search->getStringAutomaton());
  result = new Value(param_subject->getStringAutomaton()->difference(contains_auto));
  delete contains_auto; contains_auto = nullptr;

  setTermValue(not_contains_term, result);
}

void ConstraintSolver::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *begins_term;

  Value_ptr result = nullptr, param_left = getTermValue(begins_term->subject_term),
      param_right = getTermValue(begins_term->search_term);

  result = new Value(param_left->getStringAutomaton()->begins(param_right->getStringAutomaton()));

  setTermValue(begins_term, result);
}

void ConstraintSolver::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_begins_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_begins_term->subject_term),
      param_search = getTermValue(not_begins_term->search_term);

  Theory::StringAutomaton_ptr begins_auto = param_subject->getStringAutomaton()->begins(param_search->getStringAutomaton());
  result = new Value(param_subject->getStringAutomaton()->difference(begins_auto));
  delete begins_auto; begins_auto = nullptr;

  setTermValue(not_begins_term, result);
}

void ConstraintSolver::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ends_term;

  Value_ptr result = nullptr, param_left = getTermValue(ends_term->subject_term),
      param_right = getTermValue(ends_term->search_term);

  result = new Value(param_left->getStringAutomaton()->ends(param_right->getStringAutomaton()));

  setTermValue(ends_term, result);
}

void ConstraintSolver::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_ends_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_ends_term->subject_term),
      param_search = getTermValue(not_ends_term->search_term);

  Theory::StringAutomaton_ptr ends_auto = param_subject->getStringAutomaton()->ends(param_search->getStringAutomaton());
  result = new Value(param_subject->getStringAutomaton()->difference(ends_auto));
  delete ends_auto; ends_auto = nullptr;

  setTermValue(not_ends_term, result);
}

void ConstraintSolver::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);

  DVLOG(VLOG_LEVEL) << "visit: " << *index_of_term;

  Value_ptr result = nullptr, param_left = getTermValue(index_of_term->subject_term),
      param_right = getTermValue(index_of_term->search_term);

  Theory::IntAutomaton_ptr index_of_auto = param_left->getStringAutomaton()->indexOf(param_right->getStringAutomaton());
  if (index_of_auto->isAcceptingSingleInt()) {
    result = new Value(index_of_auto->getAnAcceptingInt());
    delete index_of_auto; index_of_auto = nullptr;
  } else {
    result = new Value(index_of_auto);
  }

  setTermValue(index_of_term, result);
}

void ConstraintSolver::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  Value_ptr result = nullptr, param_left = getTermValue(last_index_of_term->subject_term),
        param_right = getTermValue(last_index_of_term->search_term);

  Theory::IntAutomaton_ptr last_index_of_auto = param_left->getStringAutomaton()->lastIndexOf(param_right->getStringAutomaton());

  if (last_index_of_auto->isAcceptingSingleInt()) {
    result = new Value(last_index_of_auto->getAnAcceptingInt());
    delete last_index_of_auto; last_index_of_auto = nullptr;
  } else {
    result = new Value(last_index_of_auto);
  }
  setTermValue(last_index_of_term, result);
}

void ConstraintSolver::visitCharAt(CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *char_at_term;

  Value_ptr result = nullptr, param_subject = getTermValue(char_at_term->subject_term),
      param_index = getTermValue(char_at_term->index_term);

  result = new Value(param_subject->getStringAutomaton()->charAt(param_index->getIntConstant()));

  setTermValue(char_at_term, result);
}

void ConstraintSolver::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *sub_string_term;

  Value_ptr result = nullptr, param_subject = getTermValue(sub_string_term->subject_term),
      param_start_index = getTermValue(sub_string_term->start_index_term);

  if (Value::Type::INT_CONSTANT == param_start_index->getType()) {
    if (sub_string_term->end_index_term == nullptr) {
      result = new Value(param_subject->getStringAutomaton()->subString(param_start_index->getIntConstant()));
    } else {
      Value_ptr param_end_index = getTermValue(sub_string_term->end_index_term);
      if (Value::Type::INT_CONSTANT == param_end_index->getType()) {
        result = new Value(param_subject->getStringAutomaton()->subString(
                    param_start_index->getIntConstant(),
                    param_end_index->getIntConstant()));
      } else {
        LOG(FATAL)<< "end index of a subString operation must be an integer constant";
      }
    }
  } else {
    LOG(FATAL)<< "start index of a subString operation must be an integer constant";
  }

  setTermValue(sub_string_term, result);
}

void ConstraintSolver::visitSubStringFirstOf(SubStringFirstOf_ptr sub_string_first_of_term) {
  visit_children_of(sub_string_first_of_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *sub_string_first_of_term;

  Value_ptr result = nullptr, param_subject = getTermValue(sub_string_first_of_term->subject_term),
      param_start_index = getTermValue(sub_string_first_of_term->start_index_term);

  LOG(FATAL)<< "implement me";

  result = new Value(param_subject->getStringAutomaton()->subString(param_start_index->getIntConstant()));


  setTermValue(sub_string_first_of_term, result);
}

void ConstraintSolver::visitSubStringLastOf(SubStringLastOf_ptr sub_string_last_of_term) {
  visit_children_of(sub_string_last_of_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *sub_string_last_of_term;

  Value_ptr result = nullptr, param_subject = getTermValue(sub_string_last_of_term->subject_term),
      param_start_index = getTermValue(sub_string_last_of_term->start_index_term);

  result = new Value(param_subject->getStringAutomaton()->subStringLastOf(param_start_index->getStringAutomaton()));

  setTermValue(sub_string_last_of_term, result);
}

void ConstraintSolver::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_upper_term;

  Value_ptr result = nullptr, param = getTermValue(to_upper_term->subject_term);

  result = new Value(param->getStringAutomaton()->toUpperCase());

  setTermValue(to_upper_term, result);
}

void ConstraintSolver::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_lower_term;

  Value_ptr result = nullptr, param = getTermValue(to_lower_term->subject_term);

  result = new Value(param->getStringAutomaton()->toLowerCase());

  setTermValue(to_lower_term, result);
}

void ConstraintSolver::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *trim_term;

  Value_ptr result = nullptr, param = getTermValue(trim_term->subject_term);

  result = new Value(param->getStringAutomaton()->trim());

  setTermValue(trim_term, result);

}

void ConstraintSolver::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *replace_term;

  Value_ptr result = nullptr, param_subject = getTermValue(replace_term->subject_term),
      param_search = getTermValue(replace_term->search_term),
      param_replace = getTermValue(replace_term->replace_term);

  result = new Value(param_subject->getStringAutomaton()->replace(
          param_search->getStringAutomaton(),
          param_replace->getStringAutomaton()));

  setTermValue(replace_term, result);
}

void ConstraintSolver::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
  LOG(FATAL)<< "implement me";
}

void ConstraintSolver::visitIte(Ite_ptr ite_term) {
}

void ConstraintSolver::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstraintSolver::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstraintSolver::visitUnknownTerm(Unknown_ptr unknown_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *unknown_term;
  LOG(WARNING) << "operation is not known, over-approximate params: " << *(unknown_term->term);

  Value_ptr result = nullptr;
  path_trace.push_back(unknown_term);
  for (auto& term_ptr : *(unknown_term->term_list)) {
    visit(term_ptr);
  }
  path_trace.pop_back();
  result = new Value(Theory::StringAutomaton::makeAnyString());

  setTermValue(unknown_term, result);
}

void ConstraintSolver::visitAsQualIdentifier(
    AsQualIdentifier_ptr as_qid_term) {
}

void ConstraintSolver::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  Value_ptr result = nullptr, variable_value = symbol_table->getValue(variable);

  result = variable_value->clone();

  setTermValue(qi_term, result);
  setVariablePath(qi_term);
}

void ConstraintSolver::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  Value_ptr result = nullptr;

  switch (term_constant->getValueType()) {
  case Primitive::Type::BOOL: {
    bool b;
    std::istringstream(term_constant->getValue()) >> std::boolalpha >> b;
    result = new Value(b);
    break;
  }
  case Primitive::Type::BINARY:
    LOG(FATAL)<< "implement me";
    break;
  case Primitive::Type::HEXADECIMAL:
    LOG(FATAL) << "implement me";
    break;
  case Primitive::Type::DECIMAL:
    LOG(FATAL) << "implement me";
    break;
  case Primitive::Type::NUMERAL:
    // TODO we may get rid of constants if the automaton implementation is good enough
    result = new Value(std::stoi(term_constant->getValue()));
    break;
  case Primitive::Type::STRING:
    // TODO instead we may use string constants before going into automaton
    // and keep it unless we need automaton
    // this may complicate the code with a perf gain ??
    result = new Value(Theory::StringAutomaton::makeString(term_constant->getValue()));
    break;
  case Primitive::Type::REGEX:
    result = new Value(Theory::StringAutomaton::makeRegexAuto(term_constant->getValue()));
    break;
  default:
    LOG(FATAL) << "unhandled term constant: " << *term_constant;
    break;
  }

  setTermValue(term_constant, result);
}

void ConstraintSolver::visitIdentifier(Identifier_ptr identifier) {
}

void ConstraintSolver::visitPrimitive(Primitive_ptr primitive) {
}

void ConstraintSolver::visitTVariable(TVariable_ptr t_variable) {
}

void ConstraintSolver::visitTBool(TBool_ptr t_bool) {
}

void ConstraintSolver::visitTInt(TInt_ptr t_int) {
}

void ConstraintSolver::visitTString(TString_ptr t_string) {
}

void ConstraintSolver::visitVariable(Variable_ptr variable) {
}

void ConstraintSolver::visitSort(Sort_ptr sort) {
}

void ConstraintSolver::visitAttribute(Attribute_ptr attribute) {
}

void ConstraintSolver::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ConstraintSolver::visitVarBinding(VarBinding_ptr var_binding) {
}

Value_ptr ConstraintSolver::getTermValue(Term_ptr term) {
  Value_ptr value = arithmetic_constraint_solver.getTermValue(term);
  if (value != nullptr) {
    return value;
  }

  auto iter = term_values.find(term);
  if (iter != term_values.end()) {
    return iter->second;
  }

  DVLOG(VLOG_LEVEL)<< "value is not computed for term: " << *term;
  return nullptr;
}

bool ConstraintSolver::setTermValue(Term_ptr term, Value_ptr value) {
  auto result = term_values.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL)<< "value is already computed for term: " << *term;
  }
  return result.second;
}

void ConstraintSolver::clearTermValue(SMT::Term_ptr term) {
  auto pair = term_values.find(term);
  if (pair != term_values.end()) {
    delete pair->second;
    term_values.erase(pair);
  }
}

void ConstraintSolver::clearTermValues() {
  for (auto& entry : term_values) {
    delete entry.second;
  }

  term_values.clear();
}

void ConstraintSolver::setVariablePath(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  auto iter = variable_path_table[variable].begin();
  iter = variable_path_table[variable].insert(iter, qi_term);
  variable_path_table[variable].insert(iter + 1, path_trace.rbegin(), path_trace.rend());
}

void ConstraintSolver::update_variables() {
  if (variable_path_table.size() == 0) {
    return;
  }

  VariableValueComputer value_updater(symbol_table, variable_path_table, term_values);
  value_updater.start();

  variable_path_table.clear();
}

void ConstraintSolver::visit_children_of(Term_ptr term) {
  path_trace.push_back(term);
  Visitor::visit_children_of(term);
  path_trace.pop_back();
}

bool ConstraintSolver::check_and_visit(Term_ptr term) {
  if ((Term::Type::OR not_eq term->getType()) and
            (Term::Type::AND not_eq term->getType())) {

    Value_ptr result = getTermValue(term);
    if (result != nullptr) {
      DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
      if (arithmetic_constraint_solver.hasStringTerms(term) and result->isSatisfiable()) {
        Value_ptr string_term_result = nullptr;
        UnaryAutomaton_ptr string_term_unary_auto = nullptr;
        BinaryIntAutomaton_ptr string_term_binary_auto = nullptr,
                updated_arith_auto = nullptr;
        IntAutomaton_ptr updated_int_auto = nullptr;

        for (auto& string_term : arithmetic_constraint_solver.getStringTermsIn(term)) {
          visit(string_term);
          string_term_result = getTermValue(string_term);
          std::string string_term_var_name = Ast2Dot::toString(string_term);
          bool has_minus_one = string_term_result->getIntAutomaton()->hasNegative1();

//          result->getBinaryIntAutomaton()->inspectAuto();

          // 1- update arithmetic automaton
          string_term_unary_auto = string_term_result->getIntAutomaton()->toUnaryAutomaton();

//          string_term_unary_auto->inspectAuto(false);

          string_term_binary_auto = string_term_unary_auto->
                  toBinaryIntAutomaton(string_term_var_name,
                          result->getBinaryIntAutomaton()->getFormula()->clone(),
                          has_minus_one);
          delete string_term_unary_auto; string_term_unary_auto = nullptr;

//          string_term_binary_auto->inspectAuto();

          updated_arith_auto = result->getBinaryIntAutomaton()->intersect(string_term_binary_auto);
          delete string_term_binary_auto; string_term_binary_auto = nullptr;
          delete result; result = nullptr;

          result = new Value(updated_arith_auto);
          if (not result->isSatisfiable()) {
            break;
          }

//          updated_arith_auto->inspectAuto();

          // 2- update string term result
          string_term_binary_auto = updated_arith_auto->getBinaryAutomatonFor(string_term_var_name);
          if (has_minus_one) {
            has_minus_one = string_term_binary_auto->hasNegative1();
            BinaryIntAutomaton_ptr positive_values_auto = string_term_binary_auto->getPositiveValuesFor(string_term_var_name);
            delete string_term_binary_auto;
            string_term_binary_auto = positive_values_auto;
            delete positive_values_auto; positive_values_auto = nullptr;
          }

          string_term_unary_auto = string_term_binary_auto->toUnaryAutomaton();

          delete string_term_binary_auto; string_term_binary_auto = nullptr;
          updated_int_auto = string_term_unary_auto->toIntAutomaton(string_term_result->getIntAutomaton()->getNumberOfVariables(), has_minus_one);

          clearTermValue(string_term);
          string_term_result = new Value(updated_int_auto);
          setTermValue(string_term, string_term_result);

          // 3 - update variables involved in string term
          update_variables();
        }
        arithmetic_constraint_solver.updateTermValue(term, result);
      }

      symbol_table->setValue(SymbolTable::ARITHMETIC, result);
      return false;
    }
  }

  visit(term);
  return true;
}

} /* namespace Solver */
} /* namespace Vlab */
