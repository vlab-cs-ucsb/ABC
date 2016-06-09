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
    root(script), symbol_table(symbol_table),
    arithmetic_constraint_solver(script, symbol_table, Option::Solver::LIA_NATURAL_NUMBERS_ONLY),
    string_constraint_solver(script, symbol_table) {
}

ConstraintSolver::~ConstraintSolver() {
}

void ConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "start";
  if (Option::Solver::LIA_ENGINE_ENABLED) {
    arithmetic_constraint_solver.start();
    string_constraint_solver.start();
  }
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
  if (assert_command->component!= nullptr){
    current_component = assert_command->component;
  }

  check_and_visit(assert_command->term);
  Value_ptr result = getTermValue(assert_command->term);
  bool is_satisfiable = result->isSatisfiable();

  symbol_table->updateSatisfiability(is_satisfiable);
  symbol_table->setScopeSatisfiability(is_satisfiable);
  if ((Term::Type::OR not_eq assert_command->term->type()) and
          (Term::Type::AND not_eq assert_command->term->type())) {

    if (is_satisfiable) {
      update_variables();
    }
  }
  clearTermValuesAndLocalLetVars();
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
  DVLOG(VLOG_LEVEL) << "visit: " << *let_term;

  symbol_table->push_scope(let_term);

  Value_ptr param = nullptr;
  for (auto& var_binding : *(let_term->var_binding_list)) {
    path_trace.push_back(let_term);
    check_and_visit(var_binding->term);
    path_trace.pop_back();
    param = getTermValue(var_binding->term);
    symbol_table->setValue(var_binding->symbol->getData(), param->clone());

    // TEST: inspect params
//    if (param->getType() == Value::Type::STRING_AUTOMATON) {
//      param->getStringAutomaton()->inspectAuto();
//    } else {
//      param->getIntAutomaton()->inspectAuto();
//    }
  }

  path_trace.push_back(let_term);
  check_and_visit(let_term->term);
  path_trace.pop_back();
  param = getTermValue(let_term->term);
  symbol_table->pop_scope();

  Value_ptr result = param->clone();
  setTermValue(let_term, result);
//  result->getStringAutomaton()->inspectAuto();

//  LOG(FATAL) << "I am here" << std::endl;
}

/**
 * TODO Add a cache in case there are multiple ands
 */
void ConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
  bool is_satisfiable = true;
  Value_ptr param = nullptr;
  if (and_term->component!=nullptr){
    current_component= and_term->component;
  }

  for (auto& term : *(and_term->term_list)) {
    check_and_visit(term);
    param = getTermValue(term);
    is_satisfiable = is_satisfiable and param->isSatisfiable();
    if (is_satisfiable) {
      // update variables, but if any relational variables were updated, we need to
      // reupdate satisfiability, as it may change
      still_sat = true;
      update_variables();
      is_satisfiable = is_satisfiable and still_sat;
    }
    if (not is_satisfiable){
      clearTermValuesAndLocalLetVars();
      break;
    }
    clearTermValuesAndLocalLetVars();
  }

  Value_ptr result = new Value(is_satisfiable);

  setTermValue(and_term, result);
}

void ConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;

  bool is_satisfiable = false;
  Value_ptr param = nullptr;
  if (or_term->component!=nullptr){
    current_component= or_term->component;
  }

  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    check_and_visit(term);

    param = getTermValue(term);
    bool is_scope_satisfiable = param->isSatisfiable();

    if (Term::Type::AND not_eq term->type()) {
      if (is_scope_satisfiable) {
        update_variables();
      }
      clearTermValuesAndLocalLetVars();
    }

    symbol_table->setScopeSatisfiability(is_scope_satisfiable);
    is_satisfiable = is_satisfiable or is_scope_satisfiable;

    symbol_table->pop_scope();
    if (is_satisfiable and (not Option::Solver::MODEL_COUNTER_ENABLED)) {
      break;
    }
  }

  Value_ptr result = new Value(is_satisfiable);
  setTermValue(or_term, result);
}

void ConstraintSolver::visitNot(Not_ptr not_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;

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

  visit_children_of(eq_term);

  Value_ptr result = nullptr,
          param_left = getTermValue(eq_term->left_term),
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

  visit_children_of(not_eq_term);

  Value_ptr result = nullptr,
          param_left = getTermValue(not_eq_term->left_term),
          param_right = getTermValue(not_eq_term->right_term);

  if (Value::Type::BOOl_CONSTANT == param_left->getType() and
          Value::Type::BOOl_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getBoolConstant() not_eq param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType() and
          Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getIntConstant() not_eq param_right->getIntConstant());
  } else if (not (param_left->isSatisfiable() and param_right->isSatisfiable())) {
    result = new Value(false);
  } else {
    Value_ptr intersection = param_left->intersect(param_right);
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

  visit_children_of(gt_term);

  Value_ptr result = nullptr,
          param_left = getTermValue(gt_term->left_term),
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
      result = new Value(param_left->getIntAutomaton()->isGreaterThan(param_right->getIntAutomaton()));
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

  visit_children_of(ge_term);

  Value_ptr result = nullptr,
          param_left = getTermValue(ge_term->left_term),
          param_right = getTermValue(ge_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() >= param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isLessThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThanOrEqual(param_right->getIntAutomaton()));
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

  visit_children_of(lt_term);

  Value_ptr result = nullptr,
          param_left = getTermValue(lt_term->left_term),
          param_right = getTermValue(lt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() < param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isGreaterThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThan(param_right->getIntAutomaton()));
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

  visit_children_of(le_term);

  Value_ptr result = nullptr,
          param_left = getTermValue(le_term->left_term),
          param_right = getTermValue(le_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() <= param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(param_right->getIntAutomaton()->isGreaterThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThanOrEqual(param_right->getIntAutomaton()));
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

  Value_ptr result = nullptr,
          param_left = getTermValue(in_term->left_term),
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

  Value_ptr result = nullptr,
          param_left = getTermValue(not_in_term->left_term),
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

  Value_ptr result = nullptr,
          param = getTermValue(len_term->term);

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

  Value_ptr result = nullptr,
          param_subject = getTermValue(contains_term->subject_term),
          param_search = getTermValue(contains_term->search_term);

  result = new Value(param_subject->getStringAutomaton()->contains(param_search->getStringAutomaton()));
  setTermValue(contains_term, result);
}

void ConstraintSolver::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_contains_term;

  Value_ptr result = nullptr,
          param_subject = getTermValue(not_contains_term->subject_term),
          param_search = getTermValue(not_contains_term->search_term);

  if (not (param_subject->isSatisfiable() and param_search->isSatisfiable())) {
    result = new Value(false);
  } else if (param_search->isSingleValue()) {
    Theory::StringAutomaton_ptr contains_auto = param_subject->getStringAutomaton()->contains(param_search->getStringAutomaton());
    result = new Value(param_subject->getStringAutomaton()->difference(contains_auto));
    delete contains_auto; contains_auto = nullptr;
  } else if (param_subject->isSingleValue()) {
    Theory::StringAutomaton_ptr sub_strings_auto = param_subject->getStringAutomaton()->subStrings();
    Theory::StringAutomaton_ptr difference_auto = param_search->getStringAutomaton()->difference(sub_strings_auto);
    delete sub_strings_auto; sub_strings_auto = nullptr;
    if (difference_auto->isEmptyLanguage()) {
      result = new Value(Theory::StringAutomaton::makePhi());
    } else {
      result = param_subject->clone();
    }
    delete difference_auto; difference_auto = nullptr;
  } else {
    // TODO if param_subject is a suffix automaton (all the strings accepted is actually substrings of largest length string),
    // there can be a more precise calculation instead of just cloning the subject
    result = param_subject->clone();
  }

  setTermValue(not_contains_term, result);
}

void ConstraintSolver::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *begins_term;

  Value_ptr result = nullptr,
          param_left = getTermValue(begins_term->subject_term),
          param_right = getTermValue(begins_term->search_term);

  result = new Value(param_left->getStringAutomaton()->begins(param_right->getStringAutomaton()));

  setTermValue(begins_term, result);
}

void ConstraintSolver::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_begins_term;

  Value_ptr result = nullptr,
          param_subject = getTermValue(not_begins_term->subject_term),
          param_search = getTermValue(not_begins_term->search_term);

  if (param_search->isSingleValue()) {
    Theory::StringAutomaton_ptr begins_auto = param_subject->getStringAutomaton()->begins(param_search->getStringAutomaton());
    result = new Value(param_subject->getStringAutomaton()->difference(begins_auto));
    delete begins_auto; begins_auto = nullptr;
  } else if (param_subject->isSingleValue()) {
    Theory::StringAutomaton_ptr prefixes_auto = param_subject->getStringAutomaton()->prefixes();
    Theory::StringAutomaton_ptr difference_auto = param_search->getStringAutomaton()->difference(prefixes_auto);
    delete prefixes_auto; prefixes_auto = nullptr;
    if (difference_auto->isEmptyLanguage()) {
      result = new Value(Theory::StringAutomaton::makePhi());
    } else {
      result = param_subject->clone();
    }
    delete difference_auto; difference_auto = nullptr;
  } else {
    result = param_subject->clone();
  }

  setTermValue(not_begins_term, result);
}

void ConstraintSolver::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ends_term;

  Value_ptr result = nullptr,
          param_left = getTermValue(ends_term->subject_term),
          param_right = getTermValue(ends_term->search_term);

  result = new Value(param_left->getStringAutomaton()->ends(param_right->getStringAutomaton()));

  setTermValue(ends_term, result);
}

void ConstraintSolver::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_ends_term;

  Value_ptr result = nullptr,
          param_subject = getTermValue(not_ends_term->subject_term),
          param_search = getTermValue(not_ends_term->search_term);

  if (param_search->isSingleValue()) {
    Theory::StringAutomaton_ptr ends_auto = param_subject->getStringAutomaton()->ends(param_search->getStringAutomaton());
    result = new Value(param_subject->getStringAutomaton()->difference(ends_auto));
    delete ends_auto; ends_auto = nullptr;
  } else if (param_subject->isSingleValue()) {
    Theory::StringAutomaton_ptr suffixes_auto = param_subject->getStringAutomaton()->suffixes();
    Theory::StringAutomaton_ptr difference_auto = param_search->getStringAutomaton()->difference(suffixes_auto);
    delete suffixes_auto; suffixes_auto = nullptr;
    if (difference_auto->isEmptyLanguage()) {
      result = new Value(Theory::StringAutomaton::makePhi());
    } else {
      result = param_subject->clone();
    }
    delete difference_auto; difference_auto = nullptr;
  } else {
    result = param_subject->clone();
  }

  setTermValue(not_ends_term, result);
}

void ConstraintSolver::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);

  DVLOG(VLOG_LEVEL) << "visit: " << *index_of_term;

  Value_ptr result = nullptr,
          param_left = getTermValue(index_of_term->subject_term),
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

  Value_ptr result = nullptr,
          param_left = getTermValue(last_index_of_term->subject_term),
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

  Value_ptr result = nullptr,
          param_subject = getTermValue(char_at_term->subject_term),
          param_index = getTermValue(char_at_term->index_term);
  result = new Value(param_subject->getStringAutomaton()->charAt(param_index->getIntConstant()));

  setTermValue(char_at_term, result);
}

void ConstraintSolver::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *sub_string_term;
  Value_ptr result = nullptr,
          param_subject = getTermValue(sub_string_term->subject_term),
          param_start_index = getTermValue(sub_string_term->start_index_term),
          param_end_index = nullptr;

  switch (sub_string_term->getMode()) {
    case SubString::Mode::FROMINDEX: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMINDEX";
//      CHECK_EQ(Value::Type::INT_CONSTANT, param_start_index->getType())
//              << "start index of a subString is expected to be an integer constant";
      result = new Value(param_subject->getStringAutomaton()->subString(param_start_index->getIntConstant()));
      break;
    }
    case SubString::Mode::FROMFIRSTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMFIRSTOF";
      result = new Value(param_subject->getStringAutomaton()->subStringFirstOf(param_start_index->getStringAutomaton()));
      break;
    }
    case SubString::Mode::FROMLASTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMLASTOF";
      result = new Value(param_subject->getStringAutomaton()->subStringLastOf(param_start_index->getStringAutomaton()));
      break;
    }
    case SubString::Mode::FROMINDEXTOINDEX: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMINDEXTOINDEX";
      param_end_index = getTermValue(sub_string_term->end_index_term);

      if (Value::Type::INT_AUTOMATON == param_end_index->getType()) {
        if (param_end_index->getIntAutomaton()->isEmptyLanguage()) {
          result = new Value(StringAutomaton::makePhi());
        } else if (Value::Type::INT_CONSTANT == param_start_index->getType()) {
          result = new Value(param_subject->getStringAutomaton()->subString(
                  param_start_index->getIntConstant(),
                  param_end_index->getIntAutomaton()));
        } else {
          LOG (FATAL) << "Fully implement substring for symbolic ints";
        }
      } else {

//      CHECK_EQ(Value::Type::INT_CONSTANT, param_start_index->getType())
//                    << "start index of a subString is expected to be an integer constant";
//      CHECK_EQ(Value::Type::INT_CONSTANT, param_end_index->getType())
//                    << "start index of a subString is expected to be an integer constant";
        result = new Value(param_subject->getStringAutomaton()->subString(
                param_start_index->getIntConstant(),
                param_end_index->getIntConstant()));
      }
      break;
    }
    case SubString::Mode::FROMINDEXTOFIRSTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMINDEXTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMINDEXTOLASTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMINDEXTOLASTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMFIRSTOFTOINDEX: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMFIRSTOFTOINDEX";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMFIRSTOFTOFIRSTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMFIRSTOFTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMFIRSTOFTOLASTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMFIRSTOFTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMLASTOFTOINDEX: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMLASTOFTOINDEX";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMLASTOFTOFIRSTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMLASTOFTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMLASTOFTOLASTOF: {
      DVLOG(VLOG_LEVEL) << "subString mode: FROMLASTOFTOLASTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    default:
      LOG(FATAL)<< "Undefined subString semantic";
      break;
  }

//  result->getStringAutomaton()->inspectAuto();
  setTermValue(sub_string_term, result);
}

void ConstraintSolver::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_upper_term;

  Value_ptr param = getTermValue(to_upper_term->subject_term);
  Value_ptr result = new Value(param->getStringAutomaton()->toUpperCase());

  setTermValue(to_upper_term, result);
}

void ConstraintSolver::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_lower_term;

  Value_ptr param = getTermValue(to_lower_term->subject_term);
  Value_ptr result = new Value(param->getStringAutomaton()->toLowerCase());

  setTermValue(to_lower_term, result);
}

void ConstraintSolver::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *trim_term;

  Value_ptr param = getTermValue(trim_term->subject_term);
  Value_ptr result = new Value(param->getStringAutomaton()->trim());

  setTermValue(trim_term, result);

}

void ConstraintSolver::visitToString(ToString_ptr to_string_term) {
  visit_children_of(to_string_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_string_term;

  Value_ptr param = getTermValue(to_string_term->subject_term);
  Value_ptr result = nullptr;
  if (Value::Type::INT_CONSTANT == param->getType()) {
    std::stringstream ss;
    ss << param->getIntConstant();
    result = new Value(StringAutomaton::makeString(ss.str()));
  } else {
    auto unary_auto = param->getIntAutomaton()->toUnaryAutomaton();
    result = new Value(unary_auto->toStringAutomaton());
    delete unary_auto;
  }

  setTermValue(to_string_term, result);
}

void ConstraintSolver::visitToInt(ToInt_ptr to_int_term) {
  visit_children_of(to_int_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_int_term;

  Value_ptr param = getTermValue(to_int_term->subject_term);
  Theory::IntAutomaton_ptr int_auto = param->getStringAutomaton()->parseToIntAutomaton();

  Value_ptr result = nullptr;
  if (int_auto->isAcceptingSingleInt()) {
    result = new Value(int_auto->getAnAcceptingInt());
  } else {
    result = new Value(int_auto);
  }

  setTermValue(to_int_term, result);
}

void ConstraintSolver::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *replace_term;

  Value_ptr param_subject = getTermValue(replace_term->subject_term),
          param_search = getTermValue(replace_term->search_term),
          param_replace = getTermValue(replace_term->replace_term);

  Value_ptr result = new Value(param_subject->getStringAutomaton()->replace(
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

  path_trace.push_back(unknown_term);
  for (auto& term_ptr : *(unknown_term->term_list)) {
    visit(term_ptr);
  }
  path_trace.pop_back();
  Value_ptr result = new Value(Theory::StringAutomaton::makeAnyString());

  setTermValue(unknown_term, result);
}

void ConstraintSolver::visitAsQualIdentifier(
    AsQualIdentifier_ptr as_qid_term) {
}

void ConstraintSolver::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  Value_ptr variable_value = nullptr, result = nullptr;
  // check if variable is relational first. if so, since we're storing
  // multitrack values in the string constraint solver, get the variable's value
  // from there and clone it into the symbol table, so the variable value computer has
  // the most recent value
  variable_value = string_constraint_solver.get_variable_value(variable);
  if(variable_value != nullptr) {
    // variable relational, put in symbol table and tag for later update
    symbol_table->setValue(variable,variable_value);
    tagged_variables.push_back(variable);
  } else {
    // variable not relational, just get normally from symbol table
    variable_value = symbol_table->getValue(variable);
  }
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

/**
 * TODO improve integration with arithmetic solver,
 * store arithmetic solver values via shared_ptr
 */
Value_ptr ConstraintSolver::getTermValue(Term_ptr term) {
  // never read values for and_term and or_term from arithmetic automaton
  // we do not need binary automaton value for them, term_values will return
  // satisfiability result for them
  if ((not dynamic_cast<And_ptr> (term)) and (not dynamic_cast<Or_ptr>(term))) {
    Value_ptr value = arithmetic_constraint_solver.getTermValue(term);
    if (value != nullptr) {
      return value;
    }
    value = string_constraint_solver.get_term_value(term);
    if(value != nullptr) {
      return value;
    }
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

void ConstraintSolver::clearTermValuesAndLocalLetVars() {
  for (auto& entry : term_values) {
    delete entry.second;
  }
  term_values.clear();
  symbol_table->clearLetScopes();
}

void ConstraintSolver::setVariablePath(QualIdentifier_ptr qi_term) {
  path_trace.push_back(qi_term);
  variable_path_table.push_back(std::vector<Term_ptr>());
  auto iter = variable_path_table.back().begin();
  variable_path_table.back().insert(iter, path_trace.rbegin(), path_trace.rend());
  path_trace.pop_back();
}

void ConstraintSolver::update_variables() {
  if (variable_path_table.size() == 0) {
    return;
  }
  VariableValueComputer value_updater(symbol_table, variable_path_table, term_values);
  value_updater.start();
  variable_path_table.clear();
  // update any relational variables tagged prior to variable value computer
  // and update any changes in satisfiability
  for(auto& var : tagged_variables) {
    Value_ptr value = symbol_table->getValue(var);
    if(value == nullptr) {
      DVLOG(VLOG_LEVEL) << "Inconsistent value for variable: " << var->getName();
      continue;
    }
    string_constraint_solver.update_variable_value(var,value);
    still_sat = still_sat and value->isSatisfiable();
    delete value;
    symbol_table->setValue(var,nullptr);
  }
  tagged_variables.clear();
}

void ConstraintSolver::visit_children_of(Term_ptr term) {
  path_trace.push_back(term);
  Visitor::visit_children_of(term);
  path_trace.pop_back();
}

bool ConstraintSolver::check_and_visit(Term_ptr term) {
  if ((Term::Type::OR not_eq term->type()) and
            (Term::Type::AND not_eq term->type())) {

    Value_ptr result = getTermValue(term);
    if (result != nullptr) {
      if(string_constraint_solver.get_term_value(term) != nullptr) {
        result = string_constraint_solver.get_term_value(term);
        setTermValue(term,new Value(current_component->is_sat()));
        return true;
      }

      DVLOG(VLOG_LEVEL) << "Linear Arithmetic Constraint";
      if (arithmetic_constraint_solver.hasStringTerms(term) and result->isSatisfiable()) {

        Value_ptr string_term_result = nullptr;
        UnaryAutomaton_ptr string_term_unary_auto = nullptr;
        BinaryIntAutomaton_ptr string_term_binary_auto = nullptr,
                updated_arith_auto = nullptr;
        IntAutomaton_ptr updated_int_auto = nullptr;
        bool has_minus_one = false;
        int number_of_variables_for_int_auto;
        for (auto& string_term : arithmetic_constraint_solver.getStringTermsIn(term)) {
          visit(string_term);
          string_term_result = getTermValue(string_term);
          std::string string_term_var_name = Ast2Dot::toString(string_term);

          if (Value::Type::INT_AUTOMATON == string_term_result->getType()) {
            has_minus_one = string_term_result->getIntAutomaton()->hasNegative1();
            number_of_variables_for_int_auto = string_term_result->getIntAutomaton()->getNumberOfVariables();
  //          result->getBinaryIntAutomaton()->inspectAuto();
            // 1- update arithmetic automaton
            string_term_unary_auto = string_term_result->getIntAutomaton()->toUnaryAutomaton();

//            string_term_unary_auto->inspectAuto(false);

            string_term_binary_auto = string_term_unary_auto->
                    toBinaryIntAutomaton(string_term_var_name,
                            result->getBinaryIntAutomaton()->getFormula()->clone(),
                            has_minus_one);
            delete string_term_unary_auto; string_term_unary_auto = nullptr;
          } else if (Value::Type::INT_CONSTANT == string_term_result->getType()) {
            int value = string_term_result->getIntConstant();
            has_minus_one = (value < 0);
            string_term_binary_auto = Theory::BinaryIntAutomaton::makeAutomaton(value,
                    string_term_var_name, result->getBinaryIntAutomaton()->getFormula()->clone(), true);
            number_of_variables_for_int_auto = Theory::IntAutomaton::DEFAULT_NUM_OF_VARIABLES;
          } else {
            LOG(FATAL) << "unexpected type";
          }

          updated_arith_auto = result->getBinaryIntAutomaton()->intersect(string_term_binary_auto);
          delete string_term_binary_auto; string_term_binary_auto = nullptr;
          delete result; result = nullptr;

          result = new Value(updated_arith_auto);
          if (not result->isSatisfiable()) {
            break;
          }

//          updated_arith_auto->inspectAuto();

          // 2- update string term result, since we first update binary binary automaton it may only contain
          // numbers >= -1 (values a string constraint can return as an integer)
          string_term_binary_auto = updated_arith_auto->getBinaryAutomatonFor(string_term_var_name);

          if (has_minus_one) {
            has_minus_one = string_term_binary_auto->hasNegative1();
            BinaryIntAutomaton_ptr positive_values_auto = string_term_binary_auto->getPositiveValuesFor(string_term_var_name);
            delete string_term_binary_auto;
            string_term_binary_auto = positive_values_auto;
          }

          string_term_unary_auto = string_term_binary_auto->toUnaryAutomaton();
          delete string_term_binary_auto; string_term_binary_auto = nullptr;
          updated_int_auto = string_term_unary_auto->toIntAutomaton(number_of_variables_for_int_auto, has_minus_one);
          clearTermValue(string_term);
          string_term_result = new Value(updated_int_auto);
          setTermValue(string_term, string_term_result);

          // 3 - update variables involved in string term
          update_variables();
        }
        arithmetic_constraint_solver.updateTermValue(term, result);
      }
      //
      symbol_table->setValue(SymbolTable::ARITHMETIC+std::to_string(current_component->get_id()), result);
      return false;
    }
  }

  visit(term);
  return true;
}

} /* namespace Solver */
} /* namespace Vlab */
