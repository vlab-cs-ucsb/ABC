/*
 * VariableValueComputer.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "VariableValueComputer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int VariableValueComputer::VLOG_LEVEL = 12;
// TODO Intersect with result post
VariableValueComputer::VariableValueComputer(SymbolTable_ptr symbol_table, VariablePathTable& variable_path_table, const TermValueMap& post_images)
        : is_satisfiable_{true}, symbol_table(symbol_table), variable_path_table (variable_path_table),
          post_images (post_images), current_path (nullptr) {
}

VariableValueComputer::~VariableValueComputer() {
}

void VariableValueComputer::start() {
  Value_ptr initial_value = nullptr;
  Term_ptr root_term = nullptr;
  DVLOG(VLOG_LEVEL) << "Variable value computation start";

  // update variables starting from right side of the ast tree of the term
  // this is especially important for let terms

  for (auto it = variable_path_table.rbegin(); it != variable_path_table.rend(); ++it) {
    current_path = &(*it);
    root_term = current_path->back();

    initial_value = getTermPreImage(root_term);

    if (initial_value == nullptr) {
      initial_value = getTermPostImage(root_term);
      setTermPreImage(root_term, initial_value->clone());
    }

    visit(root_term);
    if (not is_satisfiable_) {
      break;
    }
  }

  end();
}

void VariableValueComputer::end() {
  DVLOG(VLOG_LEVEL) << "end variable value computation";
  current_path = nullptr;
  for (auto entry : pre_images) {
    delete entry.second;
  }
  pre_images.clear();
}

void VariableValueComputer::visitScript(Script_ptr script) {
}

void VariableValueComputer::visitCommand(Command_ptr command) {
}

void VariableValueComputer::visitAssert(Assert_ptr assert_command) {
}

void VariableValueComputer::visitTerm(Term_ptr term) {
}

void VariableValueComputer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void VariableValueComputer::visitExists(Exists_ptr exists_term) {
}

void VariableValueComputer::visitForAll(ForAll_ptr for_all_term) {
}

void VariableValueComputer::visitLet(Let_ptr let_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *let_term;
  popTerm(let_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    symbol_table->push_scope(let_term);
    visit(child_term);
    symbol_table->pop_scope();
    return;
  }

  Value_ptr term_value = getTermPreImage(let_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  Variable_ptr variable_to_update = symbol_table->get_variable( *(current_path->begin()) );
  Value_ptr value_to_move_upper_scope = nullptr;

  symbol_table->push_scope(let_term);

  if (child_term == let_term->term) {
    child_value = term_value->clone();
  } else {
    for (auto var_bind : *let_term->var_binding_list) {
      if (child_term == var_bind->term) {
        Value_ptr local_var_value = symbol_table->get_value(var_bind->symbol->getData());
        child_value = local_var_value->clone();
        break;
      }
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);

  if (not variable_to_update->isLocalLetVar()) {
    value_to_move_upper_scope = symbol_table->get_value(variable_to_update);
  }

  symbol_table->pop_scope();

  if (value_to_move_upper_scope) {
    symbol_table->IntersectValue(variable_to_update, value_to_move_upper_scope);
  }

}

void VariableValueComputer::visitAnd(And_ptr and_term) {
  LOG(ERROR) << "Unexpected term: " << *and_term;
}

void VariableValueComputer::visitOr(Or_ptr or_term) {
  LOG(ERROR) << "Unexpected term: " << *or_term;
}

void VariableValueComputer::visitNot(Not_ptr not_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *not_term;
  popTerm(not_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(not_term);
  child_value = term_value->clone();
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitUMinus(UMinus_ptr u_minus_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *u_minus_term;
  popTerm(u_minus_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(u_minus_term);
  switch (term_value->getType()) {
  case Value::Type::INT_CONSTANT: {
    int value = - term_value->getIntConstant();
    child_value = new Value(value);
    break;
  }
  case Value::Type::INT_AUTOMATON: {
    if (term_value->getIntAutomaton()->isAcceptingSingleInt()) {
      int value = (- term_value->getIntAutomaton()->getAnAcceptingInt());
      child_value = new Value(value);
    } else {
      child_value = new Value(term_value->getIntAutomaton()->uminus());
    }
    break;
  }
  default:
  break;
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitMinus(Minus_ptr minus_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *minus_term;
  popTerm(minus_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  Value_ptr result = nullptr;

  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(minus_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  if (child_term == minus_term->left_term) {
    Value_ptr right_child = getTermPostImage(minus_term->right_term);
    result = term_value->plus(right_child);
  } else {
    Value_ptr left_child = getTermPostImage(minus_term->left_term);
    result = left_child->minus(term_value);
  }

  child_value = child_post_value->intersect(result);
  delete result; result = nullptr;

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

/**
 * TODO may need to intersect with post image values after
 */
void VariableValueComputer::visitPlus(Plus_ptr plus_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *plus_term;
  popTerm(plus_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(plus_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  // Figure out position of the variable in plus list
  Value_ptr left_of_child = nullptr;
  Value_ptr right_of_child = nullptr;
  Value_ptr current_value = nullptr;
  for (auto& term_ptr : *(plus_term->term_list)) {
    if (child_term == term_ptr) {
      left_of_child = current_value;
      current_value = nullptr;
    } else {
      Value_ptr post_value = getTermPostImage(term_ptr);
      if (current_value == nullptr) {
        current_value = post_value->clone();
      } else {
        Value_ptr tmp = current_value;
        current_value = current_value->plus(post_value);
        delete tmp;
      }
    }
  }
  right_of_child = current_value;
  // do the preplus operations
  Value_ptr tmp_parent = term_value;
  Value_ptr child_result = nullptr;

  if (left_of_child != nullptr) {
    child_result = tmp_parent->minus(left_of_child);
    tmp_parent = child_result;
  }

  if (right_of_child != nullptr) {
    if (left_of_child != nullptr) { // // that means our variable is in between some other variables, make the pre plus precise (this can be avoided if preconcat used in minus works perfect)
      Value_ptr tmp_2 = child_post_value->plus(right_of_child);
      Value_ptr tmp_3 = tmp_parent;
      tmp_parent = tmp_3->intersect(tmp_2);
      child_result = tmp_parent;
      delete tmp_2; tmp_2 = nullptr;
      delete tmp_3; tmp_3 = nullptr;
    }
    Value_ptr tmp = child_result;
    child_result = tmp_parent->minus(right_of_child);
    delete tmp; tmp = nullptr;
  }

  delete left_of_child; left_of_child = nullptr;
  delete right_of_child; right_of_child = nullptr;

  child_value = child_post_value->intersect(child_result);
  delete child_result; child_result = nullptr;

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitTimes(Times_ptr times_term) {
//  LOG(FATAL)<< "Implement me with binary integer automaton";
  DVLOG(VLOG_LEVEL) << "pop: " << *times_term;
  popTerm(times_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(times_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  // Figure out position of the variable in times list
  Value_ptr left_of_child = nullptr;
  Value_ptr right_of_child = nullptr;
  Value_ptr current_value = nullptr;
  for (auto& term_ptr : *(times_term->term_list)) {
    if (child_term == term_ptr) {
      left_of_child = current_value;
      current_value = nullptr;
    } else {
      Value_ptr post_value = getTermPostImage(term_ptr);
      if (current_value == nullptr) {
        current_value = post_value->clone();
      } else {
        Value_ptr tmp = current_value;
        current_value = current_value->times(post_value);
        delete tmp;
      }
    }
  }
  right_of_child = current_value;
  // do the pretimes operations
  Value_ptr tmp_parent = term_value->clone();
  Value_ptr child_result = nullptr;
  Value_ptr multiplicator = nullptr;

  if (left_of_child != nullptr and right_of_child != nullptr) {
    multiplicator = left_of_child->times(right_of_child);
  } else if (left_of_child != nullptr) {
    multiplicator = left_of_child;
  } else {
    multiplicator = right_of_child;
  }

  int value = 0;
  if (Value::Type::INT_CONSTANT == multiplicator->getType()) {
    value = multiplicator->getIntConstant();

  } else if (Value::Type::INT_AUTOMATON == multiplicator->getType()) {
    if (multiplicator->getIntAutomaton()->isAcceptingSingleInt()) {
      value = multiplicator->getIntAutomaton()->getAnAcceptingInt();
    }else {
      LOG(FATAL)<< "Linear Integer Arithmetic does not support multiplication of multiple variables";
    }
  }

  int bound = (value > 0) ? value : -value;
  if (value < 0) {
  // TODO baki here handle case
  }
  for (int i = value; i > 1; i--) {
    Value_ptr tmp_1 = tmp_parent;
    child_result = tmp_1->minus(child_post_value);
    tmp_parent = child_result;
    delete tmp_1; tmp_1 = nullptr;
  }

  delete left_of_child; left_of_child = nullptr;
  delete right_of_child; right_of_child = nullptr;

  child_value = child_post_value->intersect(child_result);
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitDiv(Div_ptr div_term) {
  LOG(FATAL) << "Implement me";
}

void VariableValueComputer::visitEq(Eq_ptr eq_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *eq_term << "@" << eq_term;
  popTerm(eq_term);

  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(eq_term);

  if (Value::Type::BOOL_CONSTANT == term_value->getType()){
    child_value = getTermPostImage(child_term)->clone();
  } else {
    child_value = term_value->clone();
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}


void VariableValueComputer::visitNotEq(NotEq_ptr not_eq_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *not_eq_term;



  popTerm(not_eq_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }


  Value_ptr term_value = getTermPreImage(not_eq_term);

  // if the result is a single value AND only one of either left or right is a single value,
  // then we can safely remove the result value from whichever side is NOT a single value
  auto left_val = getTermPostImage(not_eq_term->left_term);
  auto right_val = getTermPostImage(not_eq_term->right_term);

  if(left_val->isSingleValue() or right_val->isSingleValue()) {
    if (Value::Type::BOOL_CONSTANT == term_value->getType()) {
      CHECK_EQ(true, term_value->getBoolConstant());
      child_value = getTermPostImage(child_term)->clone();
    } else {
      if (term_value->isSingleValue() and not getTermPostImage(child_term)->isSingleValue()) {
        child_value = getTermPostImage(child_term)->difference(term_value);
      } else {
        child_value = getTermPostImage(child_term)->clone();
      }
    }
  } else {
    child_value = getTermPostImage(child_term)->clone();
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitGt(Gt_ptr gt_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *gt_term;
  popTerm(gt_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr child_post_value = getTermPostImage(child_term);

  if (Value::Type::INT_CONSTANT == child_post_value->getType()) {
    child_value = child_post_value->clone();
  } else {
    if (child_term == gt_term->left_term) {
      Value_ptr param_right = getTermPostImage(gt_term->right_term);
      if (Value::Type::INT_CONSTANT == param_right->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanTo(param_right->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanTo(param_right->getIntAutomaton()));
      }
    } else {
      Value_ptr param_left = getTermPostImage(gt_term->left_term);
      if (Value::Type::INT_CONSTANT == param_left->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanTo(param_left->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanTo(param_left->getIntAutomaton()));
      }
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitGe(Ge_ptr ge_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *ge_term;
  popTerm(ge_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr child_post_value = getTermPostImage(child_term);

  if (Value::Type::INT_CONSTANT == child_post_value->getType()) {
    child_value = child_post_value->clone();
  } else {
    if (child_term == ge_term->left_term) {
      Value_ptr param_right = getTermPostImage(ge_term->right_term);
      if (Value::Type::INT_CONSTANT == param_right->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanOrEqualTo(param_right->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanOrEqualTo(param_right->getIntAutomaton()));
      }
    } else {
      Value_ptr param_left = getTermPostImage(ge_term->left_term);
      if (Value::Type::INT_CONSTANT == param_left->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanOrEqualTo(param_left->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanOrEqualTo(param_left->getIntAutomaton()));
      }
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitLt(Lt_ptr lt_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *lt_term;
  popTerm(lt_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr child_post_value = getTermPostImage(child_term);

  if (Value::Type::INT_CONSTANT == child_post_value->getType()) {
    child_value = child_post_value->clone();
  } else {
    if (child_term == lt_term->left_term) {
      Value_ptr param_right = getTermPostImage(lt_term->right_term);
      if (Value::Type::INT_CONSTANT == param_right->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanTo(param_right->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanTo(param_right->getIntAutomaton()));
      }
    } else {
      Value_ptr param_left = getTermPostImage(lt_term->left_term);
      if (Value::Type::INT_CONSTANT == param_left->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanTo(param_left->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanTo(param_left->getIntAutomaton()));
      }
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitLe(Le_ptr le_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *le_term;
  popTerm(le_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }


  Value_ptr child_post_value = getTermPostImage(child_term);

  if (Value::Type::INT_CONSTANT == child_post_value->getType()) {
    child_value = child_post_value->clone();
  } else {
    if (child_term == le_term->left_term) {
      Value_ptr param_right = getTermPostImage(le_term->right_term);
      if (Value::Type::INT_CONSTANT == param_right->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanOrEqualTo(param_right->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictLessThanOrEqualTo(param_right->getIntAutomaton()));
      }
    } else {
      Value_ptr param_left = getTermPostImage(le_term->left_term);
      if (Value::Type::INT_CONSTANT == param_left->getType()) {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanOrEqualTo(param_left->getIntConstant()));
      } else {
        child_value = new Value(child_post_value->getIntAutomaton()->restrictGreaterThanOrEqualTo(param_left->getIntAutomaton()));
      }
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitConcat(Concat_ptr concat_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *concat_term;
  popTerm(concat_term);
  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }
  Value_ptr term_value = getTermPreImage(concat_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  // Figure out position of the variable in concat list
  Theory::StringAutomaton_ptr left_of_child = nullptr;
  Theory::StringAutomaton_ptr right_of_child = nullptr;
  Theory::StringAutomaton_ptr current_auto = nullptr;
  for (auto& term_ptr : *(concat_term->term_list)) {
    if (child_term == term_ptr) {
      left_of_child = current_auto;
      current_auto = nullptr;
    } else {
      Value_ptr post_value = getTermPostImage(term_ptr);
      if (current_auto == nullptr) {
        current_auto = post_value->getStringAutomaton()->clone();
      } else {
        Theory::StringAutomaton_ptr tmp = current_auto;
        current_auto = current_auto->Concat(post_value->getStringAutomaton());
        delete tmp;
      }
    }
  }
  right_of_child = current_auto;
  // do the preconcat operations
  Theory::StringAutomaton_ptr tmp_parent_auto = term_value->getStringAutomaton();
  Theory::StringAutomaton_ptr child_result_auto = nullptr;
  if (left_of_child != nullptr) {
    child_result_auto = tmp_parent_auto->PreConcatRight(left_of_child);
    tmp_parent_auto = child_result_auto;
  }
  if (right_of_child != nullptr) {
    if (left_of_child != nullptr) { // that means our variable is in between some other variables, make the preconcat precise (this can be avoided if preconcat works perfect)
      Theory::StringAutomaton_ptr tmp_2 = child_post_value->getStringAutomaton()->Concat(right_of_child);
      Theory::StringAutomaton_ptr tmp_3 = tmp_parent_auto;
      tmp_parent_auto = tmp_3->Intersect(tmp_2);
      child_result_auto = tmp_parent_auto;
      delete tmp_2; tmp_2 = nullptr;
      delete tmp_3; tmp_3 = nullptr;
    }
    Theory::StringAutomaton_ptr  tmp = child_result_auto;
    child_result_auto = tmp_parent_auto->PreConcatLeft(right_of_child);
    delete tmp; tmp = nullptr;
  }
  delete left_of_child; left_of_child = nullptr;
  delete right_of_child; right_of_child = nullptr;

  child_value = new Value(child_post_value->getStringAutomaton()->Intersect(child_result_auto));
  delete child_result_auto; child_result_auto = nullptr;
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitIn(In_ptr in_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *in_term;
  popTerm(in_term);
  Term_ptr child_term = current_path->back();

  if (child_term == in_term->right_term) {
    return; // in operation does not have any restriction on right hand side
  }

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(in_term);

  child_value = term_value->clone();
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitNotIn(NotIn_ptr not_in_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *not_in_term;
  popTerm(not_in_term);
  Term_ptr child_term = current_path->back();

  if (child_term == not_in_term->right_term) {
    return; // notIn operation does not have any restriction on right hand side
  }

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(not_in_term);
  child_value = term_value->clone();
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitLen(Len_ptr len_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *len_term;
  popTerm(len_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }
  Value_ptr term_value = getTermPreImage(len_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  if (Value::Type::INT_CONSTANT == term_value->getType()) {
    child_value = new Value(child_post_value->getStringAutomaton()->RestrictLengthTo(term_value->getIntConstant()));
  } else {
    child_value = new Value(child_post_value->getStringAutomaton()->RestrictLengthTo(term_value->getIntAutomaton()));
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitContains(Contains_ptr contains_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *contains_term;
  popTerm(contains_term);
  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(contains_term);

  if (child_term == contains_term->subject_term) {
    child_value = term_value->clone();
  } else {
    Value_ptr child_post_value = getTermPostImage(child_term);
    Theory::StringAutomaton_ptr sub_strings_auto = term_value->getStringAutomaton()->SubStrings();
    child_value = new Value(child_post_value->getStringAutomaton()->Intersect(sub_strings_auto));
    delete sub_strings_auto; sub_strings_auto = nullptr;
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitNotContains(NotContains_ptr not_contains_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *not_contains_term;
  popTerm(not_contains_term);
  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(not_contains_term);

  if (child_term == not_contains_term->subject_term) {
    child_value = term_value->clone();
  } else {
    Value_ptr child_post_value = getTermPostImage(child_term);
    if (term_value->isSingleValue()) {
      Theory::StringAutomaton_ptr sub_strings_auto = term_value->getStringAutomaton()->SubStrings();
      child_value = new Value(child_post_value->getStringAutomaton()->Difference(sub_strings_auto));
      delete sub_strings_auto; sub_strings_auto = nullptr;

    } else {
      child_value = child_post_value->clone();
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitBegins(Begins_ptr begins_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *begins_term;
  popTerm(begins_term);
  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(begins_term);

  if (child_term == begins_term->subject_term) {
    child_value = term_value->clone();
  } else {
    Value_ptr child_post_value = getTermPostImage(child_term);
    Theory::StringAutomaton_ptr prefixes_auto = term_value->getStringAutomaton()->Prefixes();
    child_value = new Value(child_post_value->getStringAutomaton()->Intersect(prefixes_auto));
    delete prefixes_auto; prefixes_auto = nullptr;
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitNotBegins(NotBegins_ptr not_begins_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *not_begins_term;
  popTerm(not_begins_term);
  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(not_begins_term);

  if (child_term == not_begins_term->subject_term) {
    child_value = term_value->clone();
  } else {
    Value_ptr child_post_value = getTermPostImage(child_term);
    if (term_value->isSingleValue()) {
      Theory::StringAutomaton_ptr prefixes_auto = term_value->getStringAutomaton()->Prefixes();
      child_value = new Value(child_post_value->getStringAutomaton()->Difference(prefixes_auto));
      delete prefixes_auto; prefixes_auto = nullptr;
    } else {
      child_value = child_post_value->clone();
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitEnds(Ends_ptr ends_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *ends_term;
  popTerm(ends_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }
  Value_ptr term_value = getTermPreImage(ends_term);
  if (child_term == ends_term->subject_term) {
    child_value = term_value->clone();
  } else {
    Value_ptr child_post_value = getTermPostImage(child_term);
    Theory::StringAutomaton_ptr suffixes_auto = term_value->getStringAutomaton()->Suffixes();
    child_value = new Value(child_post_value->getStringAutomaton()->Intersect(suffixes_auto));
    delete suffixes_auto; suffixes_auto = nullptr;
  }
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitNotEnds(NotEnds_ptr not_ends_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *not_ends_term;
  popTerm(not_ends_term);
  Term_ptr child_term = current_path->back();

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(not_ends_term);

  if (child_term == not_ends_term->subject_term) {
    child_value = term_value->clone();
  } else {
    Value_ptr child_post_value = getTermPostImage(child_term);
    if (term_value->isSingleValue()) {
      Theory::StringAutomaton_ptr suffixes_auto = term_value->getStringAutomaton()->Suffixes();
      child_value = new Value(child_post_value->getStringAutomaton()->Difference(suffixes_auto));
      delete suffixes_auto; suffixes_auto = nullptr;
    } else {
      child_value = child_post_value->clone();
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitIndexOf(IndexOf_ptr index_of_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *index_of_term;
  popTerm(index_of_term);
  Term_ptr child_term = current_path->back();

  if (child_term == index_of_term->search_term or child_term == index_of_term->from_index) {
    // indexOf operation does not have any restriction on right hand side
    // technically, from_index should be restricted as well if the result of indexOf is -1
    // but for now we overapproximate
    return;
  }

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(index_of_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Value_ptr param_search = getTermPostImage(index_of_term->search_term);
  Value_ptr from_index = nullptr;
  if(index_of_term->from_index != nullptr) {
    from_index = getTermPostImage(index_of_term->from_index);
  }

  if (Value::Type::INT_CONSTANT == term_value->getType()) {

    if(from_index != nullptr and Value::Type::INT_CONSTANT == from_index->getType()) {
      child_value = new Value(child_post_value->getStringAutomaton()
                                ->RestrictIndexOfTo(term_value->getIntConstant(), from_index->getIntConstant(), param_search->getStringAutomaton()));
    } else if(from_index != nullptr and Value::Type::INT_AUTOMATON == from_index->getType()) {
      child_value = new Value(child_post_value->getStringAutomaton()
                                ->RestrictIndexOfTo(term_value->getIntConstant(), from_index->getIntAutomaton(), param_search->getStringAutomaton()));
    } else {
      child_value = new Value(child_post_value->getStringAutomaton()
                                ->RestrictIndexOfTo(term_value->getIntConstant(), param_search->getStringAutomaton()));
    }
  } else {
    if(from_index != nullptr and Value::Type::INT_CONSTANT == from_index->getType()) {
      child_value = new Value(child_post_value->getStringAutomaton()
                                ->RestrictIndexOfTo(term_value->getIntAutomaton(), from_index->getIntConstant(), param_search->getStringAutomaton()));
    } else if(from_index != nullptr and Value::Type::INT_AUTOMATON == from_index->getType()) {
      child_value = new Value(child_post_value->getStringAutomaton()
                                ->RestrictIndexOfTo(term_value->getIntAutomaton(), from_index->getIntAutomaton(), param_search->getStringAutomaton()));
    } else {
      child_value = new Value(child_post_value->getStringAutomaton()
                                ->RestrictIndexOfTo(term_value->getIntAutomaton(), param_search->getStringAutomaton()));
    }
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *last_index_of_term;
  popTerm(last_index_of_term);
  Term_ptr child_term = current_path->back();

  if (child_term == last_index_of_term->search_term) {
    return; // lastIndexOf operation does not have any restriction on right hand side
  }

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(last_index_of_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Value_ptr param_search = getTermPostImage(last_index_of_term->search_term);

  if (Value::Type::INT_CONSTANT == term_value->getType()) {
    child_value = new Value(child_post_value->getStringAutomaton()
            ->RestrictLastIndexOfTo(term_value->getIntConstant(), param_search->getStringAutomaton()));
  } else {
    child_value = new Value(child_post_value->getStringAutomaton()
                ->RestrictLastIndexOfTo(term_value->getIntAutomaton(), param_search->getStringAutomaton()));
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

/**
 *
 */
void VariableValueComputer::visitCharAt(CharAt_ptr char_at_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *char_at_term;
  popTerm(char_at_term);

  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);

  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }


  Value_ptr term_value = getTermPreImage(char_at_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  if (child_term == char_at_term->subject_term)
  {
    Value_ptr index_value = getTermPostImage(char_at_term->index_term);
    if (Value::Type::INT_CONSTANT == index_value->getType()) {
      child_value = new Value(child_post_value->getStringAutomaton()
              ->RestrictAtIndexTo(index_value->getIntConstant(), term_value->getStringAutomaton()));
    } else {
      child_value = new Value(child_post_value->getStringAutomaton()
              ->RestrictAtIndexTo(index_value->getIntAutomaton(), term_value->getStringAutomaton()));
    }
  }
  else
  {
    Value_ptr subject_value = getTermPostImage(char_at_term->subject_term);

    Theory::IntAutomaton_ptr indexes_auto = subject_value->getStringAutomaton()->IndexOf(term_value->getStringAutomaton());
    if (Value::Type::INT_CONSTANT == child_post_value->getType())
    {
      child_value = new Value(indexes_auto->Intersect(child_post_value->getIntConstant()));
    }
    else
    {
      child_value = new Value(indexes_auto->Intersect(child_post_value->getIntAutomaton()));

    }
    delete indexes_auto;
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}


/**
 * (str.substr s i n)
 * s: string
 * i: starting index
 * n: length of substring
 */
void VariableValueComputer::visitSubString(SubString_ptr sub_string_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *sub_string_term;
  popTerm(sub_string_term);
  Term_ptr child_term = current_path->back();

  if (child_term == sub_string_term->start_index_term or
          child_term == sub_string_term->end_index_term) {
    // TODO !!! need to implement logic here
    // even if indices are symbolic, do we need to update?
    return; // subString operation does not have any restriction on indexes
  }

  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  // consider multi-track int and string automata

  Theory::StringAutomaton_ptr child_pre_auto = nullptr;
  Value_ptr term_value = getTermPreImage(sub_string_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Value_ptr start_index_value = getTermPostImage(sub_string_term->start_index_term);
  Value_ptr end_index_value = nullptr;//getTermPostImage(sub_string_term->end_index_term);


//  // result of substring
// term_value->getStringAutomaton()->inspectAuto(false, false);
//  // subject auto
// child_post_value->getStringAutomaton()->inspectAuto(false, false);
//  end_index_value->getIntAutomaton()->inspectAuto(false,true);
// std::cin.get();

  if (Value::Type::INT_CONSTANT == start_index_value->getType()) {
    child_value = new Value(child_post_value->getStringAutomaton()
            ->RestrictAtIndexTo(start_index_value->getIntConstant(), term_value->getStringAutomaton()));
  } else {
    child_value = new Value(child_post_value->getStringAutomaton()
            ->RestrictAtIndexTo(start_index_value->getIntAutomaton(), term_value->getStringAutomaton()));
  }

//  child_value->getStringAutomaton()->inspectAuto(false,false);
//  std::cin.get();

  /*
  switch (sub_string_term->getMode()) {
    case SubString::Mode::FROMINDEX: {
      LOG(INFO) << "FROMINDEX";
      if (Value::Type::INT_CONSTANT == start_index_value->getType()) {
        child_value = new Value(child_post_value->getStringAutomaton()
                ->RestrictFromIndexToEndTo(start_index_value->getIntConstant(), term_value->getStringAutomaton()));
      } else {
        child_value = new Value(child_post_value->getStringAutomaton()
                ->RestrictFromIndexToEndTo(start_index_value->getIntAutomaton(), term_value->getStringAutomaton()));
      }
      break;
    }
    case SubString::Mode::FROMFIRSTOF: {
    LOG(INFO) << "FROMFIRSTOF";
      Value_ptr index_value = getTermPostImage(sub_string_term->start_index_term);
      Theory::StringAutomaton_ptr any_string_not_contains_search = index_value->getStringAutomaton()->GetAnyStringNotContainsMe();
      Theory::StringAutomaton_ptr general_pre_substring = any_string_not_contains_search->Concat(term_value->getStringAutomaton());
      delete any_string_not_contains_search; any_string_not_contains_search = nullptr;

      child_value = new Value(child_post_value->getStringAutomaton()
                    ->Intersect(general_pre_substring));
      delete general_pre_substring; general_pre_substring = nullptr;
      break;
    }
    case SubString::Mode::FROMLASTOF: {
    LOG(INFO) << "FROMLASTOF";
      child_value = new Value(child_post_value->getStringAutomaton()
              ->Ends(term_value->getStringAutomaton()));
      break;
    }
    case SubString::Mode::FROMINDEXTOINDEX: {
    LOG(INFO) << "FROMINDEXTOINDEX";
//      end_index_value = getTermPostImage(sub_string_term->end_index_term);
      //term_value already contains end index
      if (Value::Type::INT_CONSTANT == start_index_value->getType()) {
        child_value = new Value(child_post_value->getStringAutomaton()
                ->RestrictAtIndexTo(start_index_value->getIntConstant(), term_value->getStringAutomaton()));
      } else {
        child_value = new Value(child_post_value->getStringAutomaton()
                ->RestrictAtIndexTo(start_index_value->getIntAutomaton(), term_value->getStringAutomaton()));
      }
      break;
    }
    case SubString::Mode::FROMINDEXTOFIRSTOF: {
    LOG(INFO) << "FROMINDEXTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMINDEXTOLASTOF: {
    LOG(INFO) << "FROMINDEXTOLASTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMFIRSTOFTOINDEX: {
    LOG(INFO) << "FROMFIRSTOFTOINDEX";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMFIRSTOFTOFIRSTOF: {
    LOG(INFO) << "FROMFIRSTOFTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMFIRSTOFTOLASTOF: {
    LOG(INFO) << "FROMFIRSTOFTOLASTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMLASTOFTOINDEX: {
    LOG(INFO) << "FROMLASTOFTOINDEX";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMLASTOFTOFIRSTOF: {
    LOG(INFO) << "FROMLASTOFTOFIRSTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    case SubString::Mode::FROMLASTOFTOLASTOF: {
    LOG(INFO) << "FROMLASTOFTOLASTOF";
      LOG(FATAL)<< "implement me";
      break;
    }
    default:
      LOG(FATAL)<< "Undefined subString semantic";
      break;
  }
   */

//  child_value->getStringAutomaton()->inspectAuto(false,false);
//  std::cin.get();

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

/**
 * TODO improve pre image computation
 *
 */
void VariableValueComputer::visitToUpper(ToUpper_ptr to_upper_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *to_upper_term;
  popTerm(to_upper_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(to_upper_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Theory::StringAutomaton_ptr child_pre_auto = term_value->getStringAutomaton()
      ->PreToUpperCase(child_post_value->getStringAutomaton());
  child_value = new Value(child_pre_auto);
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitToLower(ToLower_ptr to_lower_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *to_lower_term;
  popTerm(to_lower_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(to_lower_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Theory::StringAutomaton_ptr child_pre_auto = term_value->getStringAutomaton()
      ->PreToLowerCase(child_post_value->getStringAutomaton());
  child_value = new Value(child_pre_auto);
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitTrim(Trim_ptr trim_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *trim_term;
  popTerm(trim_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(trim_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Theory::StringAutomaton_ptr child_pre_auto = term_value->getStringAutomaton()
      ->PreTrim(child_post_value->getStringAutomaton());
  child_value = new Value(child_pre_auto);
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitToString(ToString_ptr to_string_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *to_string_term;
  popTerm(to_string_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(to_string_term);
  Value_ptr child_post_value = getTermPostImage(child_term);

  Theory::IntAutomaton_ptr int_auto = term_value->getStringAutomaton()
      ->ParseToIntAutomaton();

  if (int_auto->isAcceptingSingleInt()) {
    int value = int_auto->getAnAcceptingInt();
    child_value = new Value(value);
  } else {
    Theory::IntAutomaton_ptr child_pre_auto = nullptr;
    if (Value::Type::INT_CONSTANT == child_post_value->getType()) {
      child_pre_auto = int_auto->Intersect(child_post_value->getIntConstant());
    } else {
      child_pre_auto = int_auto->Intersect(child_post_value->getIntAutomaton());
    }
    child_value = new Value(child_pre_auto);
  }

  delete int_auto;

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitToInt(ToInt_ptr to_int_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *to_int_term;
  popTerm(to_int_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(to_int_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Theory::StringAutomaton_ptr child_pre_auto = nullptr;
  if (Value::Type::INT_CONSTANT == term_value->getType()) {
    std::stringstream ss;
    ss << term_value->getIntConstant();
    // if -1, then we can't refine child term (anything non-numeric maps to -1)
    if(term_value->getIntConstant() == -1) {
      child_pre_auto = Theory::StringAutomaton::MakeAnyString();
    } else {
      // can start any number of leading zeros
      auto regex_auto = Theory::StringAutomaton::MakeRegexAuto("0*");
      auto str_auto = Theory::StringAutomaton::MakeString(ss.str());
      auto concat_auto = regex_auto->Concat(str_auto);
      child_pre_auto = child_post_value->getStringAutomaton()->Intersect(concat_auto);
      delete str_auto;
      delete regex_auto;
      delete concat_auto;
    }
  } else {
    // if -1, then we can't refine child term (anything non-numeric maps to -1)
    if(term_value->getIntAutomaton()->hasNegative1()) {
      child_pre_auto = Theory::StringAutomaton::MakeAnyString();
    } else {
      auto unary_auto = term_value->getIntAutomaton()->toUnaryAutomaton();
//      unary_auto->inspectAuto(false, true);
      auto str_auto = unary_auto->toStringAutomaton();
//      str_auto->inspectAuto(false, true);
      // can start any number of leading zeros
      auto regex_auto = Theory::StringAutomaton::MakeRegexAuto("0*");
      auto concat_auto = regex_auto->Concat(str_auto);
      child_pre_auto = child_post_value->getStringAutomaton()->Intersect(concat_auto);
//      child_pre_auto->inspectAuto(false, true);
      delete unary_auto;
      delete regex_auto;
      delete concat_auto;
      delete str_auto;
    }
  }

  child_value = new Value(child_pre_auto);
  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitReplace(Replace_ptr replace_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *replace_term;
  popTerm(replace_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr term_value = getTermPreImage(replace_term);
  Value_ptr child_post_value = getTermPostImage(child_term);
  Value_ptr search_auto_value = getTermPostImage(replace_term->search_term);
  Value_ptr replace_auto_value = getTermPostImage(replace_term->replace_term);

  if (child_term == replace_term->replace_term) {
    Theory::StringAutomaton_ptr child_pre_auto =
    		term_value->getStringAutomaton()->PreReplace(search_auto_value->getStringAutomaton(),
            																				 replace_auto_value->getStringAutomaton()->GetAnAcceptingString(),
																										 child_post_value->getStringAutomaton());
    child_value = new Value(child_pre_auto);
  } else {
    child_value = child_post_value->clone();
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitCount(Count_ptr count_term) {
  LOG(FATAL) << "implement me";
  visit_children_of(count_term);
}

void VariableValueComputer::visitIte(Ite_ptr ite_term) {
}

void VariableValueComputer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void VariableValueComputer::visitReUnion(ReUnion_ptr re_union_term) {
}

void VariableValueComputer::visitReInter(ReInter_ptr re_inter_term) {
}

void VariableValueComputer::visitReStar(ReStar_ptr re_star_term) {
}

void VariableValueComputer::visitRePlus(RePlus_ptr re_plus_term) {
}

void VariableValueComputer::visitReOpt(ReOpt_ptr re_opt_term) {
}

void VariableValueComputer::visitReLoop(ReLoop_ptr re_loop_term) {
}

void VariableValueComputer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void VariableValueComputer::visitUnknownTerm(Unknown_ptr unknown_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *unknown_term;
  QualIdentifier_ptr qi_term = dynamic_cast<QualIdentifier_ptr>(unknown_term->term);
  LOG(WARNING) << "operation is not known, over-approximate params of operation: '" << qi_term->getVarName() << "'";
  popTerm(unknown_term);
  Term_ptr child_term = current_path->back();
  Value_ptr child_value = getTermPreImage(child_term);
  if (child_value not_eq nullptr) {
    visit(child_term);
    return;
  }

  Value_ptr child_post_value = getTermPostImage(child_term);
  switch (child_post_value->getType()) {
    case Value::Type::STRING_AUTOMATON:
      child_value = new Value(Theory::StringAutomaton::MakeAnyString());
      break;
    case Value::Type::INT_CONSTANT:
    case Value::Type::INT_AUTOMATON:
      child_value = new Value(Theory::IntAutomaton::makeAnyInt());
      break;
    default:
      child_value = child_post_value->clone();
      break;
  }

  setTermPreImage(child_term, child_value);
  visit(child_term);
}

void VariableValueComputer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void VariableValueComputer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "pop: " << *qi_term << " = " << qi_term->getVarName();
  popTerm(qi_term);

  Value_ptr term_pre_value = getTermPreImage(qi_term);


  /**
   * 1) term automaton is single track, set formula for it
   * and let automaton side figure out if it is needed to be extended
   *
   */
  switch (term_pre_value->getType()) {
    case Value::Type::STRING_AUTOMATON:
    {
      auto string_auto = term_pre_value->getStringAutomaton();
      // string_auto->inspectAuto(true,false);
      // std::cin.get();
      auto formula = string_auto->GetFormula();
      if (formula == nullptr || string_auto->GetNumTracks() == 1) {
        formula = new Theory::StringFormula();
        formula->SetType(Theory::StringFormula::Type::VAR);
        formula->AddVariable(qi_term->getVarName(), 1);
        string_auto->SetFormula(formula);
      } else if (Theory::StringFormula::Type::VAR != formula->GetType()) {
      	LOG(FATAL) << "fix me";
      } else {
        LOG(FATAL) << "WAT";
      }
//      string_auto->inspectAuto(false,true);
//      symbol_table->get_value(qi_term->getVarName())->getStringAutomaton()->inspectAuto(false,true);
//      std::cin.get();

      
    }
      break;
    case Value::Type::INT_CONSTANT:
    case Value::Type::INT_AUTOMATON:
    {
      //TODO !!!! improve mixing constraints by design
    	Variable_ptr variable = symbol_table->get_variable(qi_term->getVarName());
    	auto variable_value = symbol_table->get_value(variable);
      if(Value::Type::BINARYINT_AUTOMATON == variable_value->getType()) {
        if(Value::Type::INT_CONSTANT == term_pre_value->getType()) {
          int constant = term_pre_value->getIntConstant();
          delete term_pre_value;
          term_pre_value = new Value(Theory::IntAutomaton::makeInt(constant));
        }
      	auto unary_auto = term_pre_value->getIntAutomaton()->toUnaryAutomaton();
      	auto term_binary_auto = unary_auto->toBinaryIntAutomaton(qi_term->getVarName(),
																																 variable_value->getIntAutomaton()->GetFormula()->clone(),
																																 term_pre_value->getIntAutomaton()->hasNegative1());

				delete unary_auto;
				delete term_pre_value;
				term_pre_value = new Value(term_binary_auto);
				pre_images[qi_term] = term_pre_value;
      }
    }
      break;
    default:
      LOG(INFO) << term_pre_value << " " << *term_pre_value;
      LOG(FATAL) << "handle case";
      break;
  }

  // if(qi_term->getVarName() == "m") {
  //   LOG(INFO) << "HERE 1";
  //   Variable_ptr variable = symbol_table->get_variable(qi_term->getVarName());
  //   Value_ptr variable_value = symbol_table->get_value(variable);

  //   term_pre_value->getStringAutomaton()->inspectAuto(true,false);
  //   variable_value->getStringAutomaton()->GetAutomatonForVariable("m")->inspectAuto(true,true);
  //   // variable_value->getStringAutomaton()->inspectAuto(false,false);
  // }

  is_satisfiable_ = symbol_table->IntersectValue(qi_term->getVarName(), term_pre_value) and is_satisfiable_;

  // if(qi_term->getVarName() == "m") {
  //   LOG(INFO) << "HERE 2";
  //   Variable_ptr variable = symbol_table->get_variable(qi_term->getVarName());
  //   Value_ptr variable_value = symbol_table->get_value(variable);

  //   auto v = variable_value->getStringAutomaton()->GetAutomatonForVariable("m");
  //   v->inspectAuto(true,false);

    

  //   for(auto i = 0; i < v->getDFA()->ns; i++) {
  //     if(v->IsAcceptingState(i)) {
  //       LOG(INFO) << "state " << i << " is accepting";
  //     } else {
  //       LOG(INFO) << "state " << i << " is NOT accepting";
  //     }
  //   }

  //   std::cin.get();
  // }
}

void VariableValueComputer::visitTermConstant(TermConstant_ptr term_constant) {
}

void VariableValueComputer::visitIdentifier(Identifier_ptr identifier) {
}

void VariableValueComputer::visitPrimitive(Primitive_ptr primitive) {
}

void VariableValueComputer::visitTVariable(TVariable_ptr t_variable) {
}

void VariableValueComputer::visitTBool(TBool_ptr t_bool) {
}

void VariableValueComputer::visitTInt(TInt_ptr t_int) {
}

void VariableValueComputer::visitTString(TString_ptr t_string) {
}

void VariableValueComputer::visitVariable(Variable_ptr variable) {
}

void VariableValueComputer::visitSort(Sort_ptr sort) {
}

void VariableValueComputer::visitAttribute(Attribute_ptr attribute) {
}

void VariableValueComputer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void VariableValueComputer::visitVarBinding(VarBinding_ptr var_binding) {
}

bool VariableValueComputer::is_satisfiable() {
  return is_satisfiable_;
}

Value_ptr VariableValueComputer::getTermPostImage(Term_ptr term) {
  auto iter = post_images.find(term);
  if (iter == post_images.end()) {
    LOG(FATAL)<< "post image value is not computed for term: " << *term;
  }
  return iter->second;
}

Value_ptr VariableValueComputer::getTermPreImage(Term_ptr term) {
  auto iter = pre_images.find(term);
  if (iter == pre_images.end()) {
    return nullptr;
  }
  return iter->second;
}

bool VariableValueComputer::setTermPreImage(Term_ptr term, Value_ptr value) {
  auto result = pre_images.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL)<< "value is already computed for term: " << *term;
  }
  return result.second;
}

void VariableValueComputer::popTerm(Term_ptr term) {
  if (current_path->back() == term) {
    current_path->pop_back();
  } else {
    LOG(FATAL) << "expected '" << *term << "', but found '" << *current_path->back() << "'";
  }
}

} /* namespace Solver */
} /* namespace Vlab */
