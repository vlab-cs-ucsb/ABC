/*
 * ConstantTermOptimization.cpp
 *
 *  Created on: Jun 25, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "ConstantTermOptimization.h"

namespace Vlab {
namespace Solver {
namespace Optimization {

using namespace SMT;

const int ConstantTermOptimization::VLOG_LEVEL = 18;

ConstantTermOptimization::ConstantTermOptimization()
  : mode_ (ConstantTermOptimization::Mode::PREFIX) {
  DVLOG(VLOG_LEVEL) << "'ConstantTermOptimization' initizalized...";
}

ConstantTermOptimization::~ConstantTermOptimization() {
}

void ConstantTermOptimization::start(Term_ptr term, int length, ConstantTermOptimization::Mode mode) {
  mode_ = mode;
  length_ = length;
  visit(term);
}

void ConstantTermOptimization::start(TermConstant_ptr term_constant, int length, ConstantTermOptimization::Mode mode) {
  mode_ = mode;
  length_ = length;
  visitTermConstant(term_constant);
}

void ConstantTermOptimization::start() {
}

void ConstantTermOptimization::end() {

}

void ConstantTermOptimization::visitScript(Script_ptr script) {
}

void ConstantTermOptimization::visitCommand(Command_ptr command) {
}

void ConstantTermOptimization::visitAssert(Assert_ptr assert_command) {
}

void ConstantTermOptimization::visitTerm(Term_ptr term) {
}

void ConstantTermOptimization::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ConstantTermOptimization::visitExists(Exists_ptr exists_term) {
}

void ConstantTermOptimization::visitForAll(ForAll_ptr for_all_term) {
}

void ConstantTermOptimization::visitLet(Let_ptr let_term) {
}

void ConstantTermOptimization::visitAnd(And_ptr and_term) {
}

void ConstantTermOptimization::visitOr(Or_ptr or_term) {
}

void ConstantTermOptimization::visitNot(Not_ptr not_term) {
}

void ConstantTermOptimization::visitUMinus(UMinus_ptr u_minus_term) {
}

void ConstantTermOptimization::visitMinus(Minus_ptr minus_term) {
}

void ConstantTermOptimization::visitPlus(Plus_ptr plus_term) {
}

void ConstantTermOptimization::visitTimes(Times_ptr times_term) {
}

void ConstantTermOptimization::visitEq(Eq_ptr eq_term) {
}

void ConstantTermOptimization::visitNotEq(NotEq_ptr not_eq_term) {
}

void ConstantTermOptimization::visitGt(Gt_ptr gt_term) {
}

void ConstantTermOptimization::visitGe(Ge_ptr ge_term) {
}

void ConstantTermOptimization::visitLt(Lt_ptr lt_term) {
}

void ConstantTermOptimization::visitLe(Le_ptr le_term) {
}

/**
 * Make use of the fact that concats are already processed
 */
void ConstantTermOptimization::visitConcat(Concat_ptr concat_term) {
  if (Mode::PREFIX == mode_) {
    visit(concat_term->term_list->front());
  } else {
    visit(concat_term->term_list->back());
  }
}

void ConstantTermOptimization::visitIn(In_ptr in_term) {
}

void ConstantTermOptimization::visitNotIn(NotIn_ptr not_in_term) {
}

void ConstantTermOptimization::visitLen(Len_ptr len_term) {
}

void ConstantTermOptimization::visitContains(Contains_ptr contains_term) {
}

void ConstantTermOptimization::visitNotContains(NotContains_ptr not_contains_term) {
}

void ConstantTermOptimization::visitBegins(Begins_ptr begins_term) {
}

void ConstantTermOptimization::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void ConstantTermOptimization::visitEnds(Ends_ptr ends_term) {
}

void ConstantTermOptimization::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void ConstantTermOptimization::visitIndexOf(IndexOf_ptr index_of_term) {
}

void ConstantTermOptimization::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

/**
 * Char at must be optimized, we can't do more
 */
void ConstantTermOptimization::visitCharAt(CharAt_ptr char_at_term) {
}

/**
 * Sub string must be optimized, we can't do more
 */
void ConstantTermOptimization::visitSubString(SubString_ptr sub_string_term) {

}

/**
 * Transform to upper data
 */
void ConstantTermOptimization::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);


/**
 * Transform to lower data
 */
void ConstantTermOptimization::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
}

/**
 * trim must be optimized, we can't do more
 */
void ConstantTermOptimization::visitTrim(Trim_ptr trim_term) {

}

void ConstantTermOptimization::visitToString(ToString_ptr to_string_term) {
}

void ConstantTermOptimization::visitToInt(ToInt_ptr to_int_term) {
}

void ConstantTermOptimization::visitReplace(Replace_ptr replace_term) {
}

void ConstantTermOptimization::visitCount(Count_ptr count_term) {
}

void ConstantTermOptimization::visitIte(Ite_ptr ite_term) {
}

void ConstantTermOptimization::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstantTermOptimization::visitReUnion(ReUnion_ptr re_union_term) {
}

void ConstantTermOptimization::visitReInter(ReInter_ptr re_inter_term) {
}

void ConstantTermOptimization::visitReStar(ReStar_ptr re_star_term) {
}

void ConstantTermOptimization::visitRePlus(RePlus_ptr re_plus_term) {
}

void ConstantTermOptimization::visitReOpt(ReOpt_ptr re_opt_term) {
}

void ConstantTermOptimization::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstantTermOptimization::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void ConstantTermOptimization::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ConstantTermOptimization::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

/**
 * Checks for a constant string, removes the prefix or suffix of the desired length appropriately
 */
void ConstantTermOptimization::visitTermConstant(TermConstant_ptr term_constant) {
  if (Primitive::Type::STRING == term_constant->getValueType()) {
    std::string new_string = term_constant->getValue();
    if (Mode::PREFIX == mode_) {
      new_string.erase(0, length_);
      term_constant->primitive->setData(new_string);
    }
  }
}

void ConstantTermOptimization::visitIdentifier(Identifier_ptr identifier) {
}

void ConstantTermOptimization::visitPrimitive(Primitive_ptr primitive) {
}

void ConstantTermOptimization::visitTVariable(TVariable_ptr t_variable) {
}

void ConstantTermOptimization::visitTBool(TBool_ptr t_bool) {
}

void ConstantTermOptimization::visitTInt(TInt_ptr t_int) {
}

void ConstantTermOptimization::visitTString(TString_ptr t_string) {
}

void ConstantTermOptimization::visitVariable(Variable_ptr variable) {
}

void ConstantTermOptimization::visitSort(Sort_ptr sort) {
}

void ConstantTermOptimization::visitAttribute(Attribute_ptr attribute) {
}

void ConstantTermOptimization::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ConstantTermOptimization::visitVarBinding(VarBinding_ptr var_binding) {
}


} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */


