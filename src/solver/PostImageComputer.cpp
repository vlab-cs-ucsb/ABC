/*
 * PostImageComputer.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "PostImageComputer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int PostImageComputer::VLOG_LEVEL = 11;

PostImageComputer::PostImageComputer(Script_ptr script,
    SymbolTable_ptr symbol_table) :
    root(script), symbol_table(symbol_table) {
}

PostImageComputer::~PostImageComputer() {
}

void PostImageComputer::start() {
  DVLOG(VLOG_LEVEL) << "start";
  visit(root);
  end();
}

void PostImageComputer::end() {
}

void PostImageComputer::visitScript(Script_ptr script) {
  symbol_table->push_scope(script);
  visit_children_of(script);
  symbol_table->pop_scope(); // global scope, it is reachable via script pointer all the time
}

void PostImageComputer::visitCommand(Command_ptr command) {
  LOG(ERROR)<< "'" << *command<< "' is not expected.";
}

void PostImageComputer::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
  Value_ptr result = getTermValue(assert_command->term);
  symbol_table->updateSatisfiability(result->isSatisfiable());

  if ((Term::Type::OR not_eq assert_command->term->getType()) and
          (Term::Type::AND not_eq assert_command->term->getType())) {
    if (symbol_table->isSatisfiable()) {
      update_variables();
    }
  }
  clearTermValues();
}

void PostImageComputer::visitTerm(Term_ptr term) {
}

void PostImageComputer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void PostImageComputer::visitExists(Exists_ptr exists_term) {
}

void PostImageComputer::visitForAll(ForAll_ptr for_all_term) {
}

void PostImageComputer::visitLet(Let_ptr let_term) {
}

/**
 * TODO Add a cache in case there are multiple ands
 */
void PostImageComputer::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;

  bool is_satisfiable = true;
  Value_ptr result = nullptr, param = nullptr;
  for (auto& term : *(and_term->term_list)) {
    visit(term);
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

  result = new Value(Value::Type::BOOl_CONSTANT, is_satisfiable);

  setTermValue(and_term, result);
}

void PostImageComputer::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;

  bool is_satisfiable = false;
  Value_ptr result = nullptr, param = nullptr;
  std::map<Visitable_ptr, bool> is_scope_satisfiable;

  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);

    param = getTermValue(term);

    if (Term::Type::AND not_eq term->getType()) {
      if (param->isSatisfiable()) {
        update_variables();
      }
      clearTermValues();
    }
    is_scope_satisfiable[term] = param->isSatisfiable();
    is_satisfiable = is_satisfiable or is_scope_satisfiable[term]; // if only doing satisfiability we can termina whenever it is true
    symbol_table->pop_scope();
  }

  result = new Value(Value::Type::BOOl_CONSTANT, is_satisfiable);

  setTermValue(or_term, result);

  // update symbolic variablee
  Variable_ptr symbolic_var = symbol_table->getSymbolicVariable();
  Value_ptr symbolic_var_result = nullptr, tmp_result = nullptr;
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    if (symbolic_var_result) {
      if (is_scope_satisfiable[term]) {
        tmp_result = symbolic_var_result;
        symbolic_var_result = symbol_table->getValue(symbolic_var)->union_(tmp_result);
        delete tmp_result;
      }
    } else {
      if (is_scope_satisfiable[term]) {
        symbolic_var_result = symbol_table->getValue(symbolic_var)->clone();
      } else {
        switch (symbolic_var->getType()) {
          case Variable::Type::BOOL:
            symbolic_var_result = new Value(Value::Type::BOOl_CONSTANT, false);
            break;
          case Variable::Type::INT:
            symbolic_var_result = new Value(Value::Type::INT_AUTOMATON, Theory::IntAutomaton::makePhi());
            break;
          case Variable::Type::STRING:
            symbolic_var_result = new Value(Value::Type::STRING_AUTOMATON, Theory::StringAutomaton::makePhi());
            break;
          default:
            break;
        }
      }
    }
    symbol_table->pop_scope();
  }
}

void PostImageComputer::visitNot(Not_ptr not_term) {
  __visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;

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

void PostImageComputer::visitUMinus(UMinus_ptr u_minus_term) {
  __visit_children_of(u_minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *u_minus_term;

  Value_ptr result = nullptr, param = getTermValue(u_minus_term->term);

  switch (param->getType()) {
  case Value::Type::INT_CONSTANT: {
    int data = (- param->getIntConstant());
    result = new Value(Value::Type::INT_CONSTANT, data);
    break;
  }
  case Value::Type::INT_AUTOMATON: {
    if (param->getIntAutomaton()->isAcceptingSingleInt()) {
      int value = (- param->getIntAutomaton()->getAnAcceptingInt());
      result = new Value(Value::Type::INT_CONSTANT,
              value);
    } else {
      result = new Value(Value::Type::INT_AUTOMATON,
              param->getIntAutomaton()->uminus());
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

void PostImageComputer::visitMinus(Minus_ptr minus_term) {
  __visit_children_of(minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *minus_term;

  Value_ptr result = nullptr, param_left = getTermValue(minus_term->left_term),
      param_right = getTermValue(minus_term->right_term);

  result = param_left->minus(param_right);

  setTermValue(minus_term, result);
}

void PostImageComputer::visitPlus(Plus_ptr plus_term) {
  __visit_children_of(plus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *plus_term;

  Value_ptr result = nullptr, param_left = getTermValue(plus_term->left_term),
      param_right = getTermValue(plus_term->right_term);

  result = param_left->plus(param_right);

  setTermValue(plus_term, result);
}

void PostImageComputer::visitEq(Eq_ptr eq_term) {
  __visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term;

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(eq_term->left_term);
  param_right = getTermValue(eq_term->right_term);

  if (Value::Type::BOOl_CONSTANT == param_left->getType() and
          Value::Type::BOOl_CONSTANT == param_right->getType()) {
    result = new Value(Value::Type::BOOl_CONSTANT,
            param_left->getBoolConstant() == param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType() and
          Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(Value::Type::BOOl_CONSTANT,
            param_left->getIntConstant() == param_right->getIntConstant());
  } else {
    result = param_left->intersect(param_right);
  }

  setTermValue(eq_term, result);
}

void PostImageComputer::visitNotEq(NotEq_ptr not_eq_term) {
  __visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;

  Value_ptr result = nullptr, param_left = nullptr,
          param_right = nullptr, intersection = nullptr;

  param_left = getTermValue(not_eq_term->left_term);
  param_right = getTermValue(not_eq_term->right_term);


  if (Value::Type::BOOl_CONSTANT == param_left->getType() and
          Value::Type::BOOl_CONSTANT == param_right->getType()) {
    result = new Value(Value::Type::BOOl_CONSTANT,
            param_left->getBoolConstant() not_eq param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType() and
          Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(Value::Type::BOOl_CONSTANT,
            param_left->getIntConstant() not_eq param_right->getIntConstant());
  } else {
    intersection = param_left->intersect(param_right);
    if (not intersection->isSatisfiable()) {
      result = new Value(Value::Type::BOOl_CONSTANT, true);
      delete intersection;
    } else {
      result = intersection;
    }
  }

  setTermValue(not_eq_term, result);
}

void PostImageComputer::visitGt(Gt_ptr gt_term) {
  __visit_children_of(gt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(gt_term->left_term);
  param_right = getTermValue(gt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              (param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(Value::Type::BOOl_CONSTANT,
                param_right->getIntAutomaton()->isLessThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_left->getIntAutomaton()->isGreaterThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_right->getIntAutomaton()->isGreaterThan(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *gt_term;
  }

  setTermValue(gt_term, result);
}

void PostImageComputer::visitGe(Ge_ptr ge_term) {
  __visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(ge_term->left_term);
  param_right = getTermValue(ge_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              (param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(Value::Type::BOOl_CONSTANT,
                param_right->getIntAutomaton()->isLessThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_left->getIntAutomaton()->isGreaterThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_right->getIntAutomaton()->isGreaterThanOrEqual(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *ge_term;
  }

  setTermValue(ge_term, result);
}

void PostImageComputer::visitLt(Lt_ptr lt_term) {
  __visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(lt_term->left_term);
  param_right = getTermValue(lt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              (param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(Value::Type::BOOl_CONSTANT,
                param_right->getIntAutomaton()->isGreaterThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_left->getIntAutomaton()->isLessThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_right->getIntAutomaton()->isLessThan(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *lt_term;
  }

  setTermValue(lt_term, result);
}

void PostImageComputer::visitLe(Le_ptr le_term) {
  __visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(le_term->left_term);
  param_right = getTermValue(le_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              (param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
        result = new Value(Value::Type::BOOl_CONSTANT,
                param_right->getIntAutomaton()->isGreaterThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_left->getIntAutomaton()->isLessThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(Value::Type::BOOl_CONSTANT,
              param_right->getIntAutomaton()->isLessThanOrEqual(param_left->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *le_term;
  }

  setTermValue(le_term, result);
}

void PostImageComputer::visitConcat(Concat_ptr concat_term) {
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

void PostImageComputer::visitIn(In_ptr in_term) {
  __visit_children_of(in_term);
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


void PostImageComputer::visitNotIn(NotIn_ptr not_in_term) {
  __visit_children_of(not_in_term);
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

void PostImageComputer::visitLen(Len_ptr len_term) {
  __visit_children_of(len_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;

  Value_ptr result = nullptr, param = getTermValue(len_term->term);

  Theory::IntAutomaton_ptr int_auto = param->getStringAutomaton()->length();

  if (int_auto->isAcceptingSingleInt()) {
    result = new Value(Value::Type::INT_CONSTANT, int_auto->getAnAcceptingInt());
    delete int_auto; int_auto = nullptr;
  } else {
    result = new Value(Value::Type::INT_AUTOMATON, int_auto);
  }

  setTermValue(len_term, result);
}

void PostImageComputer::visitContains(Contains_ptr contains_term) {
  __visit_children_of(contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *contains_term;

  Value_ptr result = nullptr, param_subject = getTermValue(contains_term->subject_term),
      param_search = getTermValue(contains_term->search_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param_subject->getStringAutomaton()->contains(param_search->getStringAutomaton()));

  setTermValue(contains_term, result);
}

void PostImageComputer::visitNotContains(NotContains_ptr not_contains_term) {
  __visit_children_of(not_contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_contains_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_contains_term->subject_term),
      param_search = getTermValue(not_contains_term->search_term);

  Theory::StringAutomaton_ptr contains_auto = param_subject->getStringAutomaton()->contains(param_search->getStringAutomaton());
  result = new Value(Value::Type::STRING_AUTOMATON,
      param_subject->getStringAutomaton()->difference(contains_auto));
  delete contains_auto; contains_auto = nullptr;

  setTermValue(not_contains_term, result);
}

void PostImageComputer::visitBegins(Begins_ptr begins_term) {
  __visit_children_of(begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *begins_term;

  Value_ptr result = nullptr, param_left = getTermValue(begins_term->subject_term),
      param_right = getTermValue(begins_term->search_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param_left->getStringAutomaton()->begins(param_right->getStringAutomaton()));

  setTermValue(begins_term, result);
}

void PostImageComputer::visitNotBegins(NotBegins_ptr not_begins_term) {
  __visit_children_of(not_begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_begins_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_begins_term->subject_term),
      param_search = getTermValue(not_begins_term->search_term);

  Theory::StringAutomaton_ptr begins_auto = param_subject->getStringAutomaton()->begins(param_search->getStringAutomaton());
  result = new Value(Value::Type::STRING_AUTOMATON,
      param_subject->getStringAutomaton()->difference(begins_auto));
  delete begins_auto; begins_auto = nullptr;

  setTermValue(not_begins_term, result);
}

void PostImageComputer::visitEnds(Ends_ptr ends_term) {
  __visit_children_of(ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ends_term;

  Value_ptr result = nullptr, param_left = getTermValue(ends_term->subject_term),
      param_right = getTermValue(ends_term->search_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param_left->getStringAutomaton()->ends(param_right->getStringAutomaton()));

  setTermValue(ends_term, result);
}

void PostImageComputer::visitNotEnds(NotEnds_ptr not_ends_term) {
  __visit_children_of(not_ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_ends_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_ends_term->subject_term),
      param_search = getTermValue(not_ends_term->search_term);

  Theory::StringAutomaton_ptr ends_auto = param_subject->getStringAutomaton()->ends(param_search->getStringAutomaton());
  result = new Value(Value::Type::STRING_AUTOMATON,
      param_subject->getStringAutomaton()->difference(ends_auto));
  delete ends_auto; ends_auto = nullptr;

  setTermValue(not_ends_term, result);
}

void PostImageComputer::visitIndexOf(IndexOf_ptr index_of_term) {
  __visit_children_of(index_of_term);

  DVLOG(VLOG_LEVEL) << "visit: " << *index_of_term;

  Value_ptr result = nullptr, param_left = getTermValue(index_of_term->subject_term),
      param_right = getTermValue(index_of_term->search_term);

  Theory::IntAutomaton_ptr index_of_auto = param_left->getStringAutomaton()->indexOf(param_right->getStringAutomaton());
  if (index_of_auto->isAcceptingSingleInt()) {
    result = new Value(Value::Type::INT_CONSTANT, index_of_auto->getAnAcceptingInt());
    delete index_of_auto; index_of_auto = nullptr;
  } else {
    result = new Value(Value::Type::INT_AUTOMATON, index_of_auto);
  }

  setTermValue(index_of_term, result);
}

void PostImageComputer::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  __visit_children_of(last_index_of_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  Value_ptr result = nullptr, param_left = getTermValue(last_index_of_term->subject_term),
        param_right = getTermValue(last_index_of_term->search_term);

  Theory::IntAutomaton_ptr last_index_of_auto = param_left->getStringAutomaton()->lastIndexOf(param_right->getStringAutomaton());
  if (last_index_of_auto->isAcceptingSingleInt()) {
    result = new Value(Value::Type::INT_CONSTANT, last_index_of_auto->getAnAcceptingInt());
    delete last_index_of_auto; last_index_of_auto = nullptr;
  } else {
    result = new Value(Value::Type::INT_AUTOMATON, last_index_of_auto);
  }

  setTermValue(last_index_of_term, result);
}

void PostImageComputer::visitCharAt(SMT::CharAt_ptr char_at_term) {
  __visit_children_of(char_at_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *char_at_term;

  Value_ptr result = nullptr, param_subject = getTermValue(char_at_term->subject_term),
      param_index = getTermValue(char_at_term->index_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param_subject->getStringAutomaton()->charAt(param_index->getIntConstant()));

  setTermValue(char_at_term, result);
}

void PostImageComputer::visitSubString(SMT::SubString_ptr sub_string_term) {
  __visit_children_of(sub_string_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *sub_string_term;

  Value_ptr result = nullptr, param_subject = getTermValue(sub_string_term->subject_term),
      param_start_index = getTermValue(sub_string_term->start_index_term);

  if (sub_string_term->end_index_term == nullptr) {
    param_subject->getStringAutomaton();
    result = new Value(Value::Type::STRING_AUTOMATON,
        param_subject->getStringAutomaton()->substring(param_start_index->getIntConstant()));
  } else {
    Value_ptr param_end_index = getTermValue(sub_string_term->end_index_term);
    result = new Value(Value::Type::STRING_AUTOMATON,
            param_subject->getStringAutomaton()->substring(
                param_start_index->getIntConstant(),
                param_end_index->getIntConstant()));
  }

  setTermValue(sub_string_term, result);
}

void PostImageComputer::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  __visit_children_of(to_upper_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_upper_term;

  Value_ptr result = nullptr, param = getTermValue(to_upper_term->subject_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param->getStringAutomaton()->toUpperCase());

  setTermValue(to_upper_term, result);
}

void PostImageComputer::visitToLower(SMT::ToLower_ptr to_lower_term) {
  __visit_children_of(to_lower_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_lower_term;

  Value_ptr result = nullptr, param = getTermValue(to_lower_term->subject_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param->getStringAutomaton()->toLowerCase());

  setTermValue(to_lower_term, result);
}

void PostImageComputer::visitTrim(SMT::Trim_ptr trim_term) {
  __visit_children_of(trim_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *trim_term;

  Value_ptr result = nullptr, param = getTermValue(trim_term->subject_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
        param->getStringAutomaton()->trim());

  setTermValue(trim_term, result);

}

void PostImageComputer::visitReplace(Replace_ptr replace_term) {
  __visit_children_of(replace_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *replace_term;

  Value_ptr result = nullptr, param_subject = getTermValue(replace_term->subject_term),
      param_search = getTermValue(replace_term->search_term),
      param_replace = getTermValue(replace_term->replace_term);

  result = new Value(Value::Type::STRING_AUTOMATON,
      param_subject->getStringAutomaton()->replace(
          param_search->getStringAutomaton(),
          param_replace->getStringAutomaton()));

  setTermValue(replace_term, result);
}

void PostImageComputer::visitCount(Count_ptr count_term) {
  __visit_children_of(count_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitIte(Ite_ptr ite_term) {
}

void PostImageComputer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void PostImageComputer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void PostImageComputer::visitUnknownTerm(Unknown_ptr unknown_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *unknown_term;
  LOG(WARNING) << "operation is not known, over-approximate params: " << *(unknown_term->term);

  Value_ptr result = nullptr;
  path_trace.push_back(unknown_term);
  for (auto& term_ptr : *(unknown_term->term_list)) {
    visit(term_ptr);
  }
  path_trace.pop_back();
  result = new Value(Value::Type::STRING_AUTOMATON, Theory::StringAutomaton::makeAnyString());

  setTermValue(unknown_term, result);
}

void PostImageComputer::visitAsQualIdentifier(
    AsQualIdentifier_ptr as_qid_term) {
}

void PostImageComputer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  Value_ptr result = nullptr, variable_value = symbol_table->getValue(variable);

  result = variable_value->clone();

  setTermValue(qi_term, result);
  setVariablePath(qi_term);
}

void PostImageComputer::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  Value_ptr result = nullptr;

  switch (term_constant->getValueType()) {
  case SMT::Primitive::Type::BOOL:
    bool b;
    std::istringstream(term_constant->getValue()) >> std::boolalpha >> b;
    result = new Value(Value::Type::BOOl_CONSTANT, b);
    break;
  case SMT::Primitive::Type::BINARY:
    LOG(FATAL)<< "implement me";
    break;
  case SMT::Primitive::Type::HEXADECIMAL:
    LOG(FATAL) << "implement me";
    break;
  case SMT::Primitive::Type::DECIMAL:
    LOG(FATAL) << "implement me";
    break;
  case SMT::Primitive::Type::NUMERAL:
    // TODO we may get rid of constants if the automaton implementation is good enough
    result = new Value(Value::Type::INT_CONSTANT, std::stoi(term_constant->getValue()));
    break;
  case SMT::Primitive::Type::STRING:
    // TODO instead we may use string constants before going into automaton
    // and keep it unless we need automaton
    // this may complicate the code with a perf gain ??
    result = new Value(Value::Type::STRING_AUTOMATON, Theory::StringAutomaton::makeString(term_constant->getValue()));
    break;
  case SMT::Primitive::Type::REGEX:
    result = new Value(Value::Type::STRING_AUTOMATON, Theory::StringAutomaton::makeRegexAuto(term_constant->getValue()));
    break;
  default:
    LOG(FATAL) << "unhandled term constant: " << *term_constant;
    break;
  }

  setTermValue(term_constant, result);
}

void PostImageComputer::visitIdentifier(Identifier_ptr identifier) {
}

void PostImageComputer::visitPrimitive(Primitive_ptr primitive) {
}

void PostImageComputer::visitTVariable(TVariable_ptr t_variable) {
}

void PostImageComputer::visitTBool(TBool_ptr t_bool) {
}

void PostImageComputer::visitTInt(TInt_ptr t_int) {
}

void PostImageComputer::visitTString(TString_ptr t_string) {
}

void PostImageComputer::visitVariable(Variable_ptr variable) {
}

void PostImageComputer::visitSort(Sort_ptr sort) {
}

void PostImageComputer::visitAttribute(Attribute_ptr attribute) {
}

void PostImageComputer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void PostImageComputer::visitVarBinding(VarBinding_ptr var_binding) {
}

Value_ptr PostImageComputer::getTermValue(SMT::Term_ptr term) {
  auto iter = post_images.find(term);
  if (iter == post_images.end()) {
    LOG(FATAL)<< "value is not computed for term: " << *term;
  }
  return iter->second;
}

bool PostImageComputer::setTermValue(SMT::Term_ptr term, Value_ptr value) {
  auto result = post_images.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL)<< "value is already computed for term: " << *term;
  }
  return result.second;
}

void PostImageComputer::clearTermValues() {
  for (auto& entry : post_images) {
    delete entry.second;
  }

  post_images.clear();
}

void PostImageComputer::setVariablePath(SMT::QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  auto iter = variable_path_table[variable].begin();
  iter = variable_path_table[variable].insert(iter, qi_term);
  variable_path_table[variable].insert(iter + 1, path_trace.rbegin(), path_trace.rend());
}

void PostImageComputer::update_variables() {
  if (variable_path_table.size() == 0) {
    return;
  }

  PreImageComputer pre_image_computer(symbol_table, variable_path_table, post_images);
  pre_image_computer.start();

  variable_path_table.clear();
}

void PostImageComputer::__visit_children_of(SMT::Term_ptr term) {
  path_trace.push_back(term);
  visit_children_of(term);
  path_trace.pop_back();
}

} /* namespace Solver */
} /* namespace Vlab */
