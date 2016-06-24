/*
 * CharAtOptimization.cpp
 *
 *  Created on: Mar 11, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "CharAtOptimization.h"

namespace Vlab {
namespace Solver {
namespace Optimization {

using namespace SMT;

const int CharAtOptimization::VLOG_LEVEL = 18;

CharAtOptimization::CharAtOptimization(unsigned index) : _is_optimized {false}, _is_index_updated {false}, _index {index} {
  DVLOG(VLOG_LEVEL) << "'CharAtOptimization' initizalized...";
}

CharAtOptimization::~CharAtOptimization() {
}

void CharAtOptimization::start() {
}

void CharAtOptimization::end() {
}

void CharAtOptimization::visitScript(Script_ptr script) {
}

void CharAtOptimization::visitCommand(Command_ptr command) {
}

void CharAtOptimization::visitAssert(Assert_ptr assert_command) {
}

void CharAtOptimization::visitTerm(Term_ptr term) {
}

void CharAtOptimization::visitExclamation(Exclamation_ptr exclamation_term) {
}

void CharAtOptimization::visitExists(Exists_ptr exists_term) {
}

void CharAtOptimization::visitForAll(ForAll_ptr for_all_term) {
}

void CharAtOptimization::visitLet(Let_ptr let_term) {
}

void CharAtOptimization::visitAnd(And_ptr and_term) {
}

void CharAtOptimization::visitOr(Or_ptr or_term) {
}

void CharAtOptimization::visitNot(Not_ptr not_term) {
}

void CharAtOptimization::visitUMinus(UMinus_ptr u_minus_term) {
}

void CharAtOptimization::visitMinus(Minus_ptr minus_term) {
}

void CharAtOptimization::visitPlus(Plus_ptr plus_term) {
}

void CharAtOptimization::visitTimes(Times_ptr times_term) {
}

void CharAtOptimization::visitEq(Eq_ptr eq_term) {
}

void CharAtOptimization::visitNotEq(NotEq_ptr not_eq_term) {
}

void CharAtOptimization::visitGt(Gt_ptr gt_term) {
}

void CharAtOptimization::visitGe(Ge_ptr ge_term) {
}

void CharAtOptimization::visitLt(Lt_ptr lt_term) {
}

void CharAtOptimization::visitLe(Le_ptr le_term) {
}

void CharAtOptimization::visitConcat(Concat_ptr concat_term) {
  // we only need to check first term of concat,
  // concat operation is optimized before we check charAt, all constant prefixes combined in first param if there is
  for (auto term :*concat_term->term_list) {
    visit(term);
    break;
  }

  if (_is_index_updated) { // modify concat list
    TermList_ptr updated_list = new TermList(concat_term->term_list->begin() + 1, concat_term->term_list->end());
    delete concat_term->term_list;
    concat_term->term_list = updated_list;
  }
}

void CharAtOptimization::visitIn(In_ptr in_term) {
}

void CharAtOptimization::visitNotIn(NotIn_ptr not_in_term) {
}

void CharAtOptimization::visitLen(Len_ptr len_term) {
}

void CharAtOptimization::visitContains(Contains_ptr contains_term) {
}

void CharAtOptimization::visitNotContains(NotContains_ptr not_contains_term) {
}

void CharAtOptimization::visitBegins(Begins_ptr begins_term) {
}

void CharAtOptimization::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void CharAtOptimization::visitEnds(Ends_ptr ends_term) {
}

void CharAtOptimization::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void CharAtOptimization::visitIndexOf(IndexOf_ptr index_of_term) {
}

void CharAtOptimization::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

void CharAtOptimization::visitCharAt(CharAt_ptr char_at_term) {
}

void CharAtOptimization::visitSubString(SubString_ptr sub_string_term) {
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(sub_string_term->start_index_term)) {
    if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
      unsigned sub_str_index = std::stoul(term_constant->getValue());
      _index = _index + sub_str_index;
      visit(sub_string_term->subject_term);
    }
  }

}

void CharAtOptimization::visitToUpper(ToUpper_ptr to_upper_term) {
  visit(to_upper_term->subject_term);
}

void CharAtOptimization::visitToLower(ToLower_ptr to_lower_term) {
  visit(to_lower_term->subject_term);
}

void CharAtOptimization::visitTrim(Trim_ptr trim_term) {
}

void CharAtOptimization::visitToString(ToString_ptr to_string_term) {
}

void CharAtOptimization::visitToInt(ToInt_ptr to_int_term) {
}

void CharAtOptimization::visitReplace(Replace_ptr replace_term) {
}

void CharAtOptimization::visitCount(Count_ptr count_term) {
}

void CharAtOptimization::visitIte(Ite_ptr ite_term) {
}

void CharAtOptimization::visitReConcat(ReConcat_ptr re_concat_term) {
}

void CharAtOptimization::visitReUnion(ReUnion_ptr re_union_term) {
}

void CharAtOptimization::visitReInter(ReInter_ptr re_inter_term) {
}

void CharAtOptimization::visitReStar(ReStar_ptr re_star_term) {
}

void CharAtOptimization::visitRePlus(RePlus_ptr re_plus_term) {
}

void CharAtOptimization::visitReOpt(ReOpt_ptr re_opt_term) {
}

void CharAtOptimization::visitToRegex(ToRegex_ptr to_regex_term) {
}

void CharAtOptimization::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void CharAtOptimization::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void CharAtOptimization::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void CharAtOptimization::visitTermConstant(TermConstant_ptr term_constant) {

  if (Primitive::Type::STRING == term_constant->getValueType()) {
    std::string str_value = term_constant->getValue();
    if (str_value.length() > _index) {
      _value = str_value[_index];
      _is_optimized = true;
    } else {
      // when term constant appears as first parameter in concat
      // if charAt index is larger than concat's first param, we can get rid of first param of concat
      _index -= str_value.length();
      _is_index_updated = true;
    }
  }
}

void CharAtOptimization::visitIdentifier(Identifier_ptr identifier) {
}

void CharAtOptimization::visitPrimitive(Primitive_ptr primitive) {
}

void CharAtOptimization::visitTVariable(TVariable_ptr t_variable) {
}

void CharAtOptimization::visitTBool(TBool_ptr t_bool) {
}

void CharAtOptimization::visitTInt(TInt_ptr t_int) {
}

void CharAtOptimization::visitTString(TString_ptr t_string) {
}

void CharAtOptimization::visitVariable(Variable_ptr variable) {
}

void CharAtOptimization::visitSort(Sort_ptr sort) {
}

void CharAtOptimization::visitAttribute(Attribute_ptr attribute) {
}

void CharAtOptimization::visitSortedVar(SortedVar_ptr sorted_var) {
}

void CharAtOptimization::visitVarBinding(VarBinding_ptr var_binding) {
}

bool CharAtOptimization::is_optimizable() {
  return _is_optimized;
}

bool CharAtOptimization::is_index_updated() {
  return _is_index_updated;
}

std::string CharAtOptimization::get_char_at_result() {
  return _value;
}

unsigned CharAtOptimization::get_index() {
  return _index;
}

} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */
