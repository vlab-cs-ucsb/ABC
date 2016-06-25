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

CharAtOptimization::CharAtOptimization(unsigned index) : is_optimized_ {false}, is_index_updated_ {false}, index_ {index}, end_index_{-1} {
  DVLOG(VLOG_LEVEL) << "'CharAtOptimization' initizalized...";
}

CharAtOptimization::~CharAtOptimization() {
}

void CharAtOptimization::start(SMT::Term_ptr term) {
  visit(term);
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

  if (is_index_updated_) { // modify concat list
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

void CharAtOptimization::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::toupper);
}

void CharAtOptimization::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::tolower);
}

void CharAtOptimization::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
  // TODO find a better way to do trim
  std::stringstream ss (value_);
  value_ = "";
  ss >> value_;
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
    if (str_value.length() > index_) {
      value_ = str_value[index_];
      is_optimized_ = true;
    } else {
      // when term constant appears as first parameter in concat
      // if charAt index is larger than concat's first param, we can get rid of first param of concat
      index_ -= str_value.length();
      is_index_updated_ = true;
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
  return is_optimized_;
}

bool CharAtOptimization::is_index_updated() {
  return is_index_updated_;
}

std::string CharAtOptimization::get_char_at_result() {
  return value_;
}

unsigned CharAtOptimization::get_index() {
  return index_;
}

} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */
