/*
 * Counter.cpp
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#include "Counter.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int Counter::VLOG_LEVEL = 17;

Counter::Counter(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table) {
}

Counter::~Counter() {
}

void Counter::start() {
  symbol_table->reset_count();
  visit(root);
  end();
}

void Counter::end() {
  if (VLOG_IS_ON(VLOG_LEVEL)) {
    for (auto& pair : symbol_table->getVariables()) {
      DVLOG(VLOG_LEVEL) << pair.first << " : " << symbol_table->get_total_count(pair.second);
    }
  }
}

void Counter::visitScript(Script_ptr script) {
  symbol_table->push_scope(script);
  visit_children_of(script);
  symbol_table->pop_scope();
}

void Counter::visitCommand(Command_ptr command) {

  switch (command->getType()) {
  case Command::Type::ASSERT: {
    visit_children_of(command);
    break;
  }
  default:
    LOG(FATAL)<< "'" << *command<< "' is not expected.";
    break;
  }
}

void Counter::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void Counter::visitTerm(Term_ptr term) {
  LOG(FATAL)<< "Unexpected term: " << *term;}

void Counter::visitExclamation(Exclamation_ptr exclamation_term) {
  LOG(FATAL)<< "Unhandled term: " << *exclamation_term << ", contact 'vlab@cs.ucsb.edu'";}

void Counter::visitExists(Exists_ptr exists_term) {
  LOG(FATAL)<< "Unhandled term: " << *exists_term << ", contact 'vlab@cs.ucsb.edu'";}

void Counter::visitForAll(ForAll_ptr for_all_term) {
  LOG(FATAL)<< "Unhandled term: " << *for_all_term << ", contact 'vlab@cs.ucsb.edu'";}

void Counter::visitLet(Let_ptr let_term) {
  LOG(FATAL)<< "Unhandled term: " << *let_term << ", contact 'vlab@cs.ucsb.edu'";}

void Counter::visitAnd(And_ptr and_term) {
  visit_children_of(and_term);
}

void Counter::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void Counter::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
}

void Counter::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
}

void Counter::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
}

void Counter::visitPlus(Plus_ptr plus_term) {
  visit_children_of(plus_term);
}

void Counter::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
}

void Counter::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
}

void Counter::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
}

void Counter::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
}

void Counter::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
}

void Counter::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
}

void Counter::visitConcat(Concat_ptr concat_term) {
  visit_children_of(concat_term);
}

void Counter::visitIn(In_ptr in_term) {
  visit_children_of(in_term);
}

void Counter::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
}

void Counter::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
}

void Counter::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
}

void Counter::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
}

void Counter::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
}

void Counter::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
}

void Counter::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
}

void Counter::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
}

void Counter::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);
}

void Counter::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
}

void Counter::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
}

void Counter::visitSubString(SMT::SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
}

void Counter::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
}

void Counter::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
}

void Counter::visitTrim(SMT::Trim_ptr trim_term) {
  visit_children_of(trim_term);
}

void Counter::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);
}

void Counter::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
}

void Counter::visitIte(Ite_ptr ite_term) {
  LOG(FATAL)<< "Unexpected 'ite', syntactic optimization phase should convert them into 'or'";}

void Counter::visitReConcat(ReConcat_ptr re_concat_term) {
  LOG(FATAL)<< "Unexpected 're.++', syntactic optimization phase should convert them into 'concat'";}

void Counter::visitToRegex(ToRegex_ptr to_regex_term) {
  LOG(FATAL)<< "Unexpected 'str.to.re', please check syntactic optimization phase";}

void Counter::visitUnknownTerm(Unknown_ptr unknown_term) {
  LOG(FATAL)<< "Unexptected term: " << *unknown_term;}

void Counter::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
  LOG(FATAL)<< "Unexpected term: " << *as_qid_term;}

void Counter::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  symbol_table->increment_count(symbol_table->getVariable(qi_term->getVarName()));
}

void Counter::visitTermConstant(TermConstant_ptr term_constant) {
}

void Counter::visitIdentifier(Identifier_ptr identifier) {
}

void Counter::visitPrimitive(Primitive_ptr primitive) {
}

void Counter::visitTVariable(TVariable_ptr t_variable) {
}

void Counter::visitTBool(TBool_ptr t_bool) {
}

void Counter::visitTInt(TInt_ptr t_int) {
}

void Counter::visitTString(TString_ptr t_string) {
}

void Counter::visitVariable(Variable_ptr variable) {
}

void Counter::visitSort(Sort_ptr sort) {
}

void Counter::visitAttribute(Attribute_ptr attribute) {
}

void Counter::visitSortedVar(SortedVar_ptr sorted_var) {
}

void Counter::visitVarBinding(VarBinding_ptr var_binding) {
}

} /* namespace Solver */
} /* namespace Vlab */

