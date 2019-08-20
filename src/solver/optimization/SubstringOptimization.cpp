/*
 * SubstringOptimization.cpp
 *
 *  Created on: Jun 25, 2016
 *      Author: baki
 */

#include "SubstringOptimization.h"

namespace Vlab {
namespace Solver {
namespace Optimization {


using namespace SMT;

const int SubstringOptimization::VLOG_LEVEL = 18;

SubstringOptimization::SubstringOptimization(SubString_ptr substring_term) : is_optimized_ {false}, is_index_updated_ {false}, concat_seen_ {false}, can_remove_constant_term_{false} {
  has_end_index_ = false;
  has_constant_end_index_ = false;
  subject_term_ = nullptr;
  start_index_term_constant_ = nullptr;
  end_index_term_constant_ = nullptr;
  start_index_ = 0;
  end_index_ = 0;

  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(substring_term->start_index_term)) {
    if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
      std::stringstream ss (term_constant->getValue());
      ss >> start_index_;
      subject_term_ = substring_term->subject_term;
      start_index_term_constant_ = term_constant;
    }
  }

  if (substring_term->end_index_term) {
    has_end_index_ = true;
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(substring_term->end_index_term)) {
      if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
        std::stringstream ss (term_constant->getValue());
        ss >> end_index_;
        has_constant_end_index_ = true;
        end_index_term_constant_ = term_constant;
      }
    }
  }

}

SubstringOptimization::~SubstringOptimization() {
}

void SubstringOptimization::start() {
  visit(subject_term_);

  if (is_index_updated_) {
    start_index_term_constant_->primitive->setData(std::to_string(start_index_));
    if (has_constant_end_index_) {
      end_index_term_constant_->primitive->setData(std::to_string(end_index_));
    }
  }
}

void SubstringOptimization::end() {
}

void SubstringOptimization::visitScript(Script_ptr script) {
}

void SubstringOptimization::visitCommand(Command_ptr command) {
}

void SubstringOptimization::visitAssert(Assert_ptr assert_command) {
}

void SubstringOptimization::visitTerm(Term_ptr term) {
}

void SubstringOptimization::visitExclamation(Exclamation_ptr exclamation_term) {
}

void SubstringOptimization::visitExists(Exists_ptr exists_term) {
}

void SubstringOptimization::visitForAll(ForAll_ptr for_all_term) {
}

void SubstringOptimization::visitLet(Let_ptr let_term) {
}

void SubstringOptimization::visitAnd(And_ptr and_term) {
}

void SubstringOptimization::visitOr(Or_ptr or_term) {
}

void SubstringOptimization::visitNot(Not_ptr not_term) {
}

void SubstringOptimization::visitUMinus(UMinus_ptr u_minus_term) {
}

void SubstringOptimization::visitMinus(Minus_ptr minus_term) {
}

void SubstringOptimization::visitPlus(Plus_ptr plus_term) {
}

void SubstringOptimization::visitTimes(Times_ptr times_term) {
}

void SubstringOptimization::visitDiv(Div_ptr div_term) {
}

void SubstringOptimization::visitEq(Eq_ptr eq_term) {
}

void SubstringOptimization::visitNotEq(NotEq_ptr not_eq_term) {
}

void SubstringOptimization::visitGt(Gt_ptr gt_term) {
}

void SubstringOptimization::visitGe(Ge_ptr ge_term) {
}

void SubstringOptimization::visitLt(Lt_ptr lt_term) {
}

void SubstringOptimization::visitLe(Le_ptr le_term) {
}

void SubstringOptimization::visitConcat(Concat_ptr concat_term) {
  concat_seen_ = true;
  // we only need to check first term of concat,
  // concat operation is optimized before we check substring, all constant prefixes combined in first param if there is
  visit(concat_term->term_list->front());

  if (can_remove_constant_term_) { // modify concat list
    TermList_ptr updated_list = new TermList(concat_term->term_list->begin() + 1, concat_term->term_list->end());
    delete concat_term->term_list;
    concat_term->term_list = updated_list;
  }
}

void SubstringOptimization::visitIn(In_ptr in_term) {
}

void SubstringOptimization::visitNotIn(NotIn_ptr not_in_term) {
}

void SubstringOptimization::visitLen(Len_ptr len_term) {
}

void SubstringOptimization::visitContains(Contains_ptr contains_term) {
}

void SubstringOptimization::visitNotContains(NotContains_ptr not_contains_term) {
}

void SubstringOptimization::visitBegins(Begins_ptr begins_term) {
}

void SubstringOptimization::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void SubstringOptimization::visitEnds(Ends_ptr ends_term) {
}

void SubstringOptimization::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void SubstringOptimization::visitIndexOf(IndexOf_ptr index_of_term) {
}

void SubstringOptimization::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

/**
 * char at must be optimized, we can't do more
 */
void SubstringOptimization::visitCharAt(CharAt_ptr char_at_term) {
}

/**
 * Sub string must be optimized, we can't do more
 */
void SubstringOptimization::visitSubString(SubString_ptr sub_string_term) {

}

void SubstringOptimization::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::toupper);
}

void SubstringOptimization::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  // TODO works for ascii, need to consider other character encodings
  std::transform(value_.begin(), value_.end(), value_.begin(), ::tolower);
}

void SubstringOptimization::visitTrim(Trim_ptr trim_term) {

}

void SubstringOptimization::visitToString(ToString_ptr to_string_term) {
}

void SubstringOptimization::visitToInt(ToInt_ptr to_int_term) {
}

void SubstringOptimization::visitReplace(Replace_ptr replace_term) {
}

void SubstringOptimization::visitCount(Count_ptr count_term) {
}

void SubstringOptimization::visitIte(Ite_ptr ite_term) {
}

void SubstringOptimization::visitReConcat(ReConcat_ptr re_concat_term) {
}

void SubstringOptimization::visitReUnion(ReUnion_ptr re_union_term) {
}

void SubstringOptimization::visitReInter(ReInter_ptr re_inter_term) {
}

void SubstringOptimization::visitReStar(ReStar_ptr re_star_term) {
}

void SubstringOptimization::visitRePlus(RePlus_ptr re_plus_term) {
}

void SubstringOptimization::visitReOpt(ReOpt_ptr re_opt_term) {
}

void SubstringOptimization::visitToRegex(ToRegex_ptr to_regex_term) {
}

void SubstringOptimization::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void SubstringOptimization::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void SubstringOptimization::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void SubstringOptimization::visitTermConstant(TermConstant_ptr term_constant) {
  ConstantTermChecker string_constant_checker;
  string_constant_checker.start(term_constant);
  if (string_constant_checker.is_constant_string()) {
    std::string str_value = string_constant_checker.get_constant_string();
    if (has_end_index_) {
      if (has_constant_end_index_ and str_value.length() >= start_index_) { // can do substring
          value_ = str_value.substr(start_index_, end_index_);
        is_optimized_ = true;
      } else if (has_constant_end_index_ and str_value.length() < start_index_) { // can get rid of that string
        term_constant->primitive->setData("");
        start_index_ -= str_value.length();
        end_index_ -= str_value.length();
        is_index_updated_ = true;
        can_remove_constant_term_ = true;
      } else if (has_constant_end_index_) {
        term_constant->primitive->setData(str_value.substr(0, start_index_));
        start_index_ = 0;
        end_index_ -= start_index_;
        is_index_updated_ = true;
        can_remove_constant_term_ = false;
      }
    } else { // does not have an end index
      if (str_value.length() < start_index_) {
        term_constant->primitive->setData("");
        start_index_ -= str_value.length();
        is_index_updated_ = true;
        can_remove_constant_term_ = true;
      } else if (not concat_seen_) {
        value_ = str_value.substr(start_index_);
        is_optimized_ = true;
      } else {
        term_constant->primitive->setData(str_value.substr(0, start_index_));
        start_index_ = 0;
        is_index_updated_ = true;
        can_remove_constant_term_ = false;
      }
    }
  }
}

void SubstringOptimization::visitIdentifier(Identifier_ptr identifier) {
}

void SubstringOptimization::visitPrimitive(Primitive_ptr primitive) {
}

void SubstringOptimization::visitTVariable(TVariable_ptr t_variable) {
}

void SubstringOptimization::visitTBool(TBool_ptr t_bool) {
}

void SubstringOptimization::visitTInt(TInt_ptr t_int) {
}

void SubstringOptimization::visitTString(TString_ptr t_string) {
}

void SubstringOptimization::visitVariable(Variable_ptr variable) {
}

void SubstringOptimization::visitSort(Sort_ptr sort) {
}

void SubstringOptimization::visitAttribute(Attribute_ptr attribute) {
}

void SubstringOptimization::visitSortedVar(SortedVar_ptr sorted_var) {
}

void SubstringOptimization::visitVarBinding(VarBinding_ptr var_binding) {
}

bool SubstringOptimization::is_optimizable() {
  return is_optimized_;
}

std::string SubstringOptimization::get_substring_result() {
  return value_;
}

bool SubstringOptimization::is_index_updated() {
  return is_index_updated_;
}

bool SubstringOptimization::has_end_index() {
  return has_end_index_;
}

bool SubstringOptimization::has_constant_end_index() {
  return has_constant_end_index_;
}

bool SubstringOptimization::can_remove_constant() {
  return can_remove_constant_term_;
}

size_t SubstringOptimization::get_start_index() {
  return start_index_;
}


} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */
