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

  visit(root);
  end();
}

void PostImageComputer::end() {
}

void PostImageComputer::visitScript(Script_ptr script) {
  symbol_table->push_scope(script);

  for (auto command : *(script->command_list)) {
    visit(command);
    if (not symbol_table->isAssertionsStillValid()) {
      break;
    }
  }

  symbol_table->pop_scope(); // TODO we will need global scope, it is reachable via script pointer all the time
}

void PostImageComputer::visitCommand(Command_ptr command) {
  switch (command->getType()) {
  case Command::Type::ASSERT: {
    visit_children_of(command);

    Assert_ptr current_assert = dynamic_cast<Assert_ptr>(command);
    Value_ptr result = getTermValue(current_assert->term);
    symbol_table->updateAssertionValid(result->isSatisfiable());

    if (symbol_table->isAssertionsStillValid()) {
      update_variables();
    }

    clearTermValues();
    break;
  }
  default:
    LOG(FATAL)<< "'" << *command<< "' is not expected.";
    break;
  }
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

void PostImageComputer::visitAnd(And_ptr and_term) {
  LOG(FATAL)<< "not implemented yet";
}

void PostImageComputer::visitOr(Or_ptr or_term) {
  LOG(FATAL)<< "not implemented yet";
}

void PostImageComputer::visitNot(Not_ptr not_term) {
  __visit_children_of(not_term);

  Value_ptr result = nullptr, param = getTermValue(not_term->term);

  switch (param->getType()) {
  case Value::Type::BOOl_CONSTANT: {
    result = new Value(Value::Type::BOOl_CONSTANT,
        not param->getBoolConstant());
    break;
  }
  case Value::Type::INT_CONSTANT: {
    // return int automaton other than this constant
    LOG(FATAL)<< "implement me";
    break;
  }
  case Value::Type::BOOL_AUTOMATON: {
    // 1- if singleton do not
    // 2- else over-approximate
    LOG(FATAL) << "implement me";
    break;
  }
  case Value::Type::INT_AUTOMATON: {
    // 1- if singleton do not
    // 2- else over-approximate
    LOG(FATAL) << "implement me";
    break;
  }
  case Value::Type::INTBOOL_AUTOMATON: {
    // 1- if singleton do not
    // 2- else over-approximate
    LOG(FATAL) << "implement me";
    break;
  }
  case Value::Type::STRING_AUTOMATON: {
    // 1- if singleton do not
    // 2- else over-approximate
    LOG(FATAL) << "implement me";
    break;
  }
  default:
  LOG(FATAL) << "not term child is not computed properly: " << *(not_term->term);
  break;
}

  setTermValue(not_term, result);
}

void PostImageComputer::visitUMinus(UMinus_ptr u_minus_term) {
  __visit_children_of(u_minus_term);

  Value_ptr result = nullptr, param = getTermValue(u_minus_term->term);

  switch (param->getType()) {
  case Value::Type::INT_CONSTANT: {
    int data = -param->getIntConstant();
    result = new Value(Value::Type::INT_CONSTANT, data);
    break;
  }
  case Value::Type::INT_AUTOMATON: {
    // do minus operation on automaton
    LOG(FATAL)<< "implement me";
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

  Value_ptr result = nullptr, param_left = getTermValue(minus_term->left_term),
      param_right = getTermValue(minus_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()
      and Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(Value::Type::INT_CONSTANT,
        param_left->getIntConstant() - param_right->getIntConstant());
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()
      and Value::Type::INT_AUTOMATON == param_right->getType()) {
    LOG(FATAL)<< "implement me";
  } else {
    LOG(FATAL) << "implement me"; // handle cases in a better way
  }

  setTermValue(minus_term, result);
}

void PostImageComputer::visitPlus(Plus_ptr plus_term) {
  __visit_children_of(plus_term);

  Value_ptr result = nullptr, param_left = getTermValue(plus_term->left_term),
      param_right = getTermValue(plus_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()
      and Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(Value::Type::INT_CONSTANT,
        param_left->getIntConstant() + param_right->getIntConstant());
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()
      and Value::Type::INT_AUTOMATON == param_right->getType()) {
    LOG(FATAL)<< "implement me";
  } else {
    LOG(FATAL) << "implement me"; // handle cases in a better way
  }

  setTermValue(plus_term, result);
}

void PostImageComputer::visitEq(Eq_ptr eq_term) {
  __visit_children_of(eq_term);

  Value_ptr result = nullptr, param_left = nullptr, param_right = nullptr;

  param_left = getTermValue(eq_term->left_term);
  param_right = getTermValue(eq_term->right_term);

  // TODO cases here does not cover all possibilities, improve code later
  switch (param_left->getType()) {
  case Value::Type::BOOl_CONSTANT: {
    result = new Value(Value::Type::BOOl_CONSTANT,
        param_left->getBoolConstant() == param_right->getBoolConstant());
    break;
  }
  case Value::Type::INT_CONSTANT: {
    result = new Value(Value::Type::BOOl_CONSTANT,
        param_left->getIntConstant() == param_right->getIntConstant());
    break;
  }
  case Value::Type::BOOL_AUTOMATON:
  case Value::Type::INT_AUTOMATON:
  case Value::Type::STRING_AUTOMATON: {
    result = param_left->intersect(param_right);
    break;
  }
  default:
    LOG(FATAL)<< "eq term child is not computed properly";
    break;
  }

  setTermValue(eq_term, result);
}

void PostImageComputer::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitConcat(Concat_ptr concat_term) {
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
  visit_children_of(in_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitSubString(SMT::SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitTrim(SMT::Trim_ptr trim_term) {
  visit_children_of(trim_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
  LOG(FATAL)<< "implement me";
}

void PostImageComputer::visitIte(Ite_ptr ite_term) {
}

void PostImageComputer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void PostImageComputer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void PostImageComputer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void PostImageComputer::visitAsQualIdentifier(
    AsQualIdentifier_ptr as_qid_term) {
}

void PostImageComputer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  Value_ptr result = nullptr, variable_value = symbol_table->getValue(variable);

  result = variable_value->clone();

  setTermValue(qi_term, result);
  setVariablePath(qi_term);
}

void PostImageComputer::visitTermConstant(TermConstant_ptr term_constant) {
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
