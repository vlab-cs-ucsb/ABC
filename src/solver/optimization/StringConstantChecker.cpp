/*
 * StringConstantChecker.cpp
 *
 *  Created on: Jun 25, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "StringConstantChecker.h"

namespace Vlab {
namespace Solver {
namespace Optimization {

using namespace SMT;

const int StringConstantChecker::VLOG_LEVEL = 18;

StringConstantChecker::StringConstantChecker()
        : mode_ (StringConstantChecker::Mode::FULL), term_constant_ { nullptr } {
  DVLOG(VLOG_LEVEL) << "'StringConstantChecker' initizalized...";
}

StringConstantChecker::~StringConstantChecker() {
}

void StringConstantChecker::start(Term_ptr term, StringConstantChecker::Mode mode) {
  mode_ = mode;
  term_constant_ = nullptr;
  value_ = "";
  visit(term);
}

void StringConstantChecker::start(TermConstant_ptr term_constant, StringConstantChecker::Mode mode) {
  mode_ = mode;
  term_constant_ = nullptr;
  value_ = "";
  visitTermConstant(term_constant);
}

void StringConstantChecker::start() {
}

void StringConstantChecker::end() {
  mode_ = StringConstantChecker::Mode::FULL;
  term_constant_ = nullptr;
  value_ = "";
}

void StringConstantChecker::visitScript(Script_ptr script) {
}

void StringConstantChecker::visitCommand(Command_ptr command) {
}

void StringConstantChecker::visitAssert(Assert_ptr assert_command) {
}

void StringConstantChecker::visitTerm(Term_ptr term) {
}

void StringConstantChecker::visitExclamation(Exclamation_ptr exclamation_term) {
}

void StringConstantChecker::visitExists(Exists_ptr exists_term) {
}

void StringConstantChecker::visitForAll(ForAll_ptr for_all_term) {
}

void StringConstantChecker::visitLet(Let_ptr let_term) {
}

void StringConstantChecker::visitAnd(And_ptr and_term) {
}

void StringConstantChecker::visitOr(Or_ptr or_term) {
}

void StringConstantChecker::visitNot(Not_ptr not_term) {
}

void StringConstantChecker::visitUMinus(UMinus_ptr u_minus_term) {
}

void StringConstantChecker::visitMinus(Minus_ptr minus_term) {
}

void StringConstantChecker::visitPlus(Plus_ptr plus_term) {
}

void StringConstantChecker::visitTimes(Times_ptr times_term) {
}

void StringConstantChecker::visitEq(Eq_ptr eq_term) {
}

void StringConstantChecker::visitNotEq(NotEq_ptr not_eq_term) {
}

void StringConstantChecker::visitGt(Gt_ptr gt_term) {
}

void StringConstantChecker::visitGe(Ge_ptr ge_term) {
}

void StringConstantChecker::visitLt(Lt_ptr lt_term) {
}

void StringConstantChecker::visitLe(Le_ptr le_term) {
}

/**
 * Make use of the fact that concats are already processed
 */
void StringConstantChecker::visitConcat(Concat_ptr concat_term) {
  if (Mode::PREFIX == mode_) {
    visit(concat_term->term_list->front());
  } else if (Mode::SUFFIX == mode_) {
    visit(concat_term->term_list->back());
  } else {
    term_constant_ = nullptr;
  }
}

void StringConstantChecker::visitIn(In_ptr in_term) {
}

void StringConstantChecker::visitNotIn(NotIn_ptr not_in_term) {
}

void StringConstantChecker::visitLen(Len_ptr len_term) {
}

void StringConstantChecker::visitContains(Contains_ptr contains_term) {
}

void StringConstantChecker::visitNotContains(NotContains_ptr not_contains_term) {
}

void StringConstantChecker::visitBegins(Begins_ptr begins_term) {
}

void StringConstantChecker::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void StringConstantChecker::visitEnds(Ends_ptr ends_term) {
}

void StringConstantChecker::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void StringConstantChecker::visitIndexOf(IndexOf_ptr index_of_term) {
}

void StringConstantChecker::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

/**
 * Char at must be optimized, we can't do more
 */
void StringConstantChecker::visitCharAt(CharAt_ptr char_at_term) {
}

/**
 * Sub string must be optimized, we can't do more
 */
void StringConstantChecker::visitSubString(SubString_ptr sub_string_term) {

}

/**
 * Transform to upper data
 */
void StringConstantChecker::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::toupper);
}

/**
 * Transform to lower data
 */
void StringConstantChecker::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::tolower);
}

/**
 * trim must be optimized, we can't do more
 */
void StringConstantChecker::visitTrim(Trim_ptr trim_term) {

}

void StringConstantChecker::visitToString(ToString_ptr to_string_term) {
}

void StringConstantChecker::visitToInt(ToInt_ptr to_int_term) {
}

void StringConstantChecker::visitReplace(Replace_ptr replace_term) {
}

void StringConstantChecker::visitCount(Count_ptr count_term) {
}

void StringConstantChecker::visitIte(Ite_ptr ite_term) {
}

void StringConstantChecker::visitReConcat(ReConcat_ptr re_concat_term) {
}

void StringConstantChecker::visitReUnion(ReUnion_ptr re_union_term) {
}

void StringConstantChecker::visitReInter(ReInter_ptr re_inter_term) {
}

void StringConstantChecker::visitReStar(ReStar_ptr re_star_term) {
}

void StringConstantChecker::visitRePlus(RePlus_ptr re_plus_term) {
}

void StringConstantChecker::visitReOpt(ReOpt_ptr re_opt_term) {
}

void StringConstantChecker::visitToRegex(ToRegex_ptr to_regex_term) {
}

void StringConstantChecker::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void StringConstantChecker::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void StringConstantChecker::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

/**
 * Checks for a constant string, transform if regex represents a constant string
 */
void StringConstantChecker::visitTermConstant(TermConstant_ptr term_constant) {
  if (Primitive::Type::STRING == term_constant->getValueType()) {
    term_constant_ = term_constant;
    value_ = term_constant->getValue();
  } else if (Primitive::Type::REGEX == term_constant->getValueType()) {
    std::string data = term_constant->getValue();
    Util::RegularExpression regular_expression (data);
    if (regular_expression.is_constant_string()) {
      term_constant->primitive->setType(Primitive::Type::STRING);
      term_constant->primitive->setData(regular_expression.get_constant_string());
      term_constant_ = term_constant;
      value_ = term_constant->getValue();
      DVLOG(VLOG_LEVEL) << "Constant string regex transformed";
    }
  }
}

void StringConstantChecker::visitIdentifier(Identifier_ptr identifier) {
}

void StringConstantChecker::visitPrimitive(Primitive_ptr primitive) {
}

void StringConstantChecker::visitTVariable(TVariable_ptr t_variable) {
}

void StringConstantChecker::visitTBool(TBool_ptr t_bool) {
}

void StringConstantChecker::visitTInt(TInt_ptr t_int) {
}

void StringConstantChecker::visitTString(TString_ptr t_string) {
}

void StringConstantChecker::visitVariable(Variable_ptr variable) {
}

void StringConstantChecker::visitSort(Sort_ptr sort) {
}

void StringConstantChecker::visitAttribute(Attribute_ptr attribute) {
}

void StringConstantChecker::visitSortedVar(SortedVar_ptr sorted_var) {
}

void StringConstantChecker::visitVarBinding(VarBinding_ptr var_binding) {
}

bool StringConstantChecker::is_constant_string() {
  return (term_constant_ != nullptr);
}

std::string StringConstantChecker::get_constant_string() {
  if (term_constant_) {
    return term_constant_->getValue();
  }
  LOG(FATAL) << "constant string is not found";
  return "";
}

} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */
