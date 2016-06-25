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

StringConstantChecker::StringConstantChecker() : index_{0}, end_index_{-1} {
  DVLOG(VLOG_LEVEL) << "'StringConstantChecker' initizalized...";
}

StringConstantChecker::~StringConstantChecker() {
}

void StringConstantChecker::start(Term_ptr term, StringConstantChecker::Mode mode) {
  mode_ = mode;
  index_ = 0;
  end_index_ = -1;
  visit(term);
}

void StringConstantChecker::start() {
}

void StringConstantChecker::end() {
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

void StringConstantChecker::visitConcat(Concat_ptr concat_term) {
  if (Mode::PREFIX == mode_) {
    visit(concat_term->term_list->front());
  } else if (Mode::SUFFIX == mode_) {
    visit(concat_term->term_list->back());
  }

  if (is_index_updated_) { // modify concat list
    TermList_ptr updated_list = new TermList(concat_term->term_list->begin() + 1, concat_term->term_list->end());
    delete concat_term->term_list;
    concat_term->term_list = updated_list;
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

void StringConstantChecker::visitCharAt(CharAt_ptr char_at_term) {
}

void StringConstantChecker::visitSubString(SubString_ptr sub_string_term) {
  if (sub_string_term->end_index_term == nullptr) {
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(sub_string_term->start_index_term)) {
      if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
        unsigned sub_str_index = std::stoul(term_constant->getValue());
        index_ = index_ + sub_str_index;
        DVLOG(VLOG_LEVEL) << "sub string start index update: " << sub_str_index;
        visit(sub_string_term->subject_term);
      }
    }
  } else {
    if (TermConstant_ptr end_constant = dynamic_cast<TermConstant_ptr>(sub_string_term->end_index_term)) {
      if (TermConstant_ptr begin_constant = dynamic_cast<TermConstant_ptr>(sub_string_term->start_index_term)) {
        if (Primitive::Type::NUMERAL == end_constant->getValueType() and Primitive::Type::NUMERAL == begin_constant->getValueType()) {
          unsigned begin_index = std::stoul(begin_constant->getValue());
          int end_index = std::stoi(end_constant->getValue());
          index_ = index_ + begin_index;
          if (end_index_ == -1) {
            end_index_ = end_index;
          } else {
            end_index_ = end_index_ - end_index + 1;
          }
          DVLOG(VLOG_LEVEL) << "sub string start index and end index update: " << begin_index << "," << end_index;
          visit(sub_string_term->subject_term);
        }
      }
    }
  }
}

void StringConstantChecker::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::toupper);
}

void StringConstantChecker::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::tolower);
}

void StringConstantChecker::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
  // TODO find a better way to do trim
  std::stringstream ss (value_);
  value_ = "";
  ss >> value_;
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

void StringConstantChecker::visitTermConstant(TermConstant_ptr term_constant) {

  if (Primitive::Type::STRING == term_constant->getValueType()) {
    value_ = term_constant->getValue();
    is_constant_ = true;
  } else if (Primitive::Type::REGEX == term_constant->getValueType()) {
    LOG(FATAL) << "implement me";
    is_constant_ = true;
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

bool StringConstantChecker::is_optimizable() {
  return is_constant_;
}

bool StringConstantChecker::is_index_updated() {
  return is_index_updated_;
}

std::string StringConstantChecker::get_char_at_result() {
  return value_;
}

unsigned StringConstantChecker::get_index() {
  return index_;
}


} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */
