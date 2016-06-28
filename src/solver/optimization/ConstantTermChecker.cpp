/*
 * StringConstantChecker.cpp
 *
 *  Created on: Jun 25, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "ConstantTermChecker.h"

namespace Vlab {
namespace Solver {
namespace Optimization {

using namespace SMT;

const int ConstantTermChecker::VLOG_LEVEL = 18;

ConstantTermChecker::ConstantTermChecker()
        : mode_ (ConstantTermChecker::Mode::FULL), term_constant_ { nullptr } {
  DVLOG(VLOG_LEVEL) << "'ConstantTermChecker' initizalized...";
}

ConstantTermChecker::~ConstantTermChecker() {
}

void ConstantTermChecker::start(Term_ptr term, ConstantTermChecker::Mode mode) {
  mode_ = mode;
  term_constant_ = nullptr;
  string_value_ = "";
  visit(term);
}

void ConstantTermChecker::start(TermConstant_ptr term_constant, ConstantTermChecker::Mode mode) {
  mode_ = mode;
  term_constant_ = nullptr;
  string_value_ = "";
  visitTermConstant(term_constant);
}

void ConstantTermChecker::start() {
}

void ConstantTermChecker::end() {
  mode_ = ConstantTermChecker::Mode::FULL;
  term_constant_ = nullptr;
  string_value_ = "";
}

void ConstantTermChecker::visitScript(Script_ptr script) {
}

void ConstantTermChecker::visitCommand(Command_ptr command) {
}

void ConstantTermChecker::visitAssert(Assert_ptr assert_command) {
}

void ConstantTermChecker::visitTerm(Term_ptr term) {
}

void ConstantTermChecker::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ConstantTermChecker::visitExists(Exists_ptr exists_term) {
}

void ConstantTermChecker::visitForAll(ForAll_ptr for_all_term) {
}

void ConstantTermChecker::visitLet(Let_ptr let_term) {
}

void ConstantTermChecker::visitAnd(And_ptr and_term) {
}

void ConstantTermChecker::visitOr(Or_ptr or_term) {
}

void ConstantTermChecker::visitNot(Not_ptr not_term) {
}

void ConstantTermChecker::visitUMinus(UMinus_ptr u_minus_term) {
}

void ConstantTermChecker::visitMinus(Minus_ptr minus_term) {
}

void ConstantTermChecker::visitPlus(Plus_ptr plus_term) {
}

void ConstantTermChecker::visitTimes(Times_ptr times_term) {
}

void ConstantTermChecker::visitEq(Eq_ptr eq_term) {
}

void ConstantTermChecker::visitNotEq(NotEq_ptr not_eq_term) {
}

void ConstantTermChecker::visitGt(Gt_ptr gt_term) {
}

void ConstantTermChecker::visitGe(Ge_ptr ge_term) {
}

void ConstantTermChecker::visitLt(Lt_ptr lt_term) {
}

void ConstantTermChecker::visitLe(Le_ptr le_term) {
}

/**
 * Make use of the fact that concats are already processed
 */
void ConstantTermChecker::visitConcat(Concat_ptr concat_term) {
  if (Mode::PREFIX == mode_) {
    visit(concat_term->term_list->front());
  } else if (Mode::SUFFIX == mode_) {
    visit(concat_term->term_list->back());
  } else {
    term_constant_ = nullptr;
  }
}

void ConstantTermChecker::visitIn(In_ptr in_term) {
}

void ConstantTermChecker::visitNotIn(NotIn_ptr not_in_term) {
}

void ConstantTermChecker::visitLen(Len_ptr len_term) {
}

void ConstantTermChecker::visitContains(Contains_ptr contains_term) {
}

void ConstantTermChecker::visitNotContains(NotContains_ptr not_contains_term) {
}

void ConstantTermChecker::visitBegins(Begins_ptr begins_term) {
}

void ConstantTermChecker::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void ConstantTermChecker::visitEnds(Ends_ptr ends_term) {
}

void ConstantTermChecker::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void ConstantTermChecker::visitIndexOf(IndexOf_ptr index_of_term) {
}

void ConstantTermChecker::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

/**
 * Char at must be optimized, we can't do more
 */
void ConstantTermChecker::visitCharAt(CharAt_ptr char_at_term) {
}

/**
 * Sub string must be optimized, we can't do more
 */
void ConstantTermChecker::visitSubString(SubString_ptr sub_string_term) {

}

/**
 * Transform to upper data
 */
void ConstantTermChecker::visitToUpper(ToUpper_ptr to_upper_term) {
  if (Mode::ONLY_TERM_CONSTANT == mode_) {
    return;
  }
  visit_children_of(to_upper_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(string_value_.begin(), string_value_.end(), string_value_.begin(), ::toupper);
}

/**
 * Transform to lower data
 */
void ConstantTermChecker::visitToLower(ToLower_ptr to_lower_term) {
  if (Mode::ONLY_TERM_CONSTANT == mode_) {
    return;
  }
  visit_children_of(to_lower_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(string_value_.begin(), string_value_.end(), string_value_.begin(), ::tolower);
}

/**
 * trim must be optimized, we can't do more
 */
void ConstantTermChecker::visitTrim(Trim_ptr trim_term) {

}

void ConstantTermChecker::visitToString(ToString_ptr to_string_term) {
}

void ConstantTermChecker::visitToInt(ToInt_ptr to_int_term) {
}

void ConstantTermChecker::visitReplace(Replace_ptr replace_term) {
}

void ConstantTermChecker::visitCount(Count_ptr count_term) {
}

void ConstantTermChecker::visitIte(Ite_ptr ite_term) {
}

void ConstantTermChecker::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstantTermChecker::visitReUnion(ReUnion_ptr re_union_term) {
}

void ConstantTermChecker::visitReInter(ReInter_ptr re_inter_term) {
}

void ConstantTermChecker::visitReStar(ReStar_ptr re_star_term) {
}

void ConstantTermChecker::visitRePlus(RePlus_ptr re_plus_term) {
}

void ConstantTermChecker::visitReOpt(ReOpt_ptr re_opt_term) {
}

void ConstantTermChecker::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstantTermChecker::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void ConstantTermChecker::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ConstantTermChecker::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

/**
 * Checks for a constant string, transform if regex represents a constant string
 */
void ConstantTermChecker::visitTermConstant(TermConstant_ptr term_constant) {
  if (Primitive::Type::STRING == term_constant->getValueType()) {
    term_constant_ = term_constant;
    string_value_ = term_constant->getValue();
  } else if (Primitive::Type::REGEX == term_constant->getValueType()) {
    std::string data = term_constant->getValue();
    Util::RegularExpression regular_expression (data);
    if (regular_expression.is_constant_string()) {
      term_constant->primitive->setType(Primitive::Type::STRING);
      term_constant->primitive->setData(regular_expression.get_constant_string());
      term_constant_ = term_constant;
      string_value_ = term_constant->getValue();
      DVLOG(VLOG_LEVEL) << "Constant string regex transformed";
    }
  } else if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
    term_constant_ = term_constant;
    string_value_ = term_constant->getValue();
  } else if (Primitive::Type::BOOL == term_constant->getValueType()) {
    term_constant_ = term_constant;
    string_value_ = term_constant->getValue();
  }
}

void ConstantTermChecker::visitIdentifier(Identifier_ptr identifier) {
}

void ConstantTermChecker::visitPrimitive(Primitive_ptr primitive) {
}

void ConstantTermChecker::visitTVariable(TVariable_ptr t_variable) {
}

void ConstantTermChecker::visitTBool(TBool_ptr t_bool) {
}

void ConstantTermChecker::visitTInt(TInt_ptr t_int) {
}

void ConstantTermChecker::visitTString(TString_ptr t_string) {
}

void ConstantTermChecker::visitVariable(Variable_ptr variable) {
}

void ConstantTermChecker::visitSort(Sort_ptr sort) {
}

void ConstantTermChecker::visitAttribute(Attribute_ptr attribute) {
}

void ConstantTermChecker::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ConstantTermChecker::visitVarBinding(VarBinding_ptr var_binding) {
}

bool ConstantTermChecker::is_constant() {
  return term_constant_ != nullptr;
}

bool ConstantTermChecker::is_constant_bool() {
  return (is_constant()  and Primitive::Type::BOOL == term_constant_->getValueType());
}

bool ConstantTermChecker::is_constant_int() {
  return (is_constant() and Primitive::Type::NUMERAL == term_constant_->getValueType());
}


bool ConstantTermChecker::is_constant_string() {
  return (is_constant() and Primitive::Type::BOOL == term_constant_->getValueType());
}

bool ConstantTermChecker::get_constant_bool() {
  if (is_constant()) {
    std::stringstream ss(term_constant_->getValue());
    bool b;
    ss >> std::boolalpha >> b;
    return b;
  }

  LOG(FATAL) << "constant bool is not found";
  return false;
}

int ConstantTermChecker::get_constant_int() {
  if (is_constant()) {
    return std::stoi(term_constant_->getValue());
  }
  LOG(FATAL) << "constant int is not found";
  return 0;
}

TermConstant_ptr ConstantTermChecker::get_term_constant() {
  if (is_constant()) {
    if (Mode::ONLY_TERM_CONSTANT == mode_) {
      return term_constant_;
    }
    LOG(FATAL) << "constant term mode is not supported to return term constant";
  }
  LOG(FATAL) << "constant term is not found";
  return nullptr;
}

std::string ConstantTermChecker::get_constant_string() {
  if (is_constant()) {
    return string_value_;
  }
  LOG(FATAL) << "constant string is not found";
  return "";
}

std::string ConstantTermChecker::get_constant_as_string() {
  return get_constant_string();
}


} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */


