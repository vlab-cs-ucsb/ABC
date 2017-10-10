/*
 * ConstraintQuerier.cpp
 *
 *  Created on: Jan 21, 2017
 *      Author: baki
 */

#include "ConstraintQuerier.h"

namespace Vlab {
namespace Solver {
namespace Optimization {

using namespace SMT;

ConstraintQuerier::ConstraintQuerier() : mode_{ConstraintQuerier::Mode::QUERY},query_result_{false}, param_index_{0}, search_term_{nullptr} {


}

ConstraintQuerier::~ConstraintQuerier() {

}

bool ConstraintQuerier::is_param_equal_to(SMT::Term_ptr term_search, SMT::Term_ptr term_subject, int index) {
  mode_ = Mode::QUERY;
  query_result_ = false;
  param_index_ = index;
  search_term_ = term_search;
  visit(term_subject);
  return query_result_;
}

Term_ptr ConstraintQuerier::get_parameter(Term_ptr term_subject, int index) {
  mode_ = Mode::GET;
  param_index_ = index;
  search_term_ = nullptr;
  visit(term_subject);

  return search_term_;
}

void ConstraintQuerier::start() {
}

void ConstraintQuerier::end() {

}

void ConstraintQuerier::visitScript(Script_ptr script) {
}

void ConstraintQuerier::visitCommand(Command_ptr command) {
}

void ConstraintQuerier::visitAssert(Assert_ptr assert_command) {
}

void ConstraintQuerier::visitTerm(Term_ptr term) {
}

void ConstraintQuerier::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ConstraintQuerier::visitExists(Exists_ptr exists_term) {
}

void ConstraintQuerier::visitForAll(ForAll_ptr for_all_term) {
}

void ConstraintQuerier::visitLet(Let_ptr let_term) {
}

void ConstraintQuerier::visitAnd(And_ptr and_term) {
}

void ConstraintQuerier::visitOr(Or_ptr or_term) {
}

void ConstraintQuerier::visitNot(Not_ptr not_term) {
}

void ConstraintQuerier::visitUMinus(UMinus_ptr u_minus_term) {
}

void ConstraintQuerier::visitMinus(Minus_ptr minus_term) {
}

void ConstraintQuerier::visitPlus(Plus_ptr plus_term) {
}

void ConstraintQuerier::visitTimes(Times_ptr times_term) {
}

void ConstraintQuerier::visitDiv(Div_ptr div_term) {
}

void ConstraintQuerier::visitEq(Eq_ptr eq_term) {
}

void ConstraintQuerier::visitNotEq(NotEq_ptr not_eq_term) {
}

void ConstraintQuerier::visitGt(Gt_ptr gt_term) {
}

void ConstraintQuerier::visitGe(Ge_ptr ge_term) {
}

void ConstraintQuerier::visitLt(Lt_ptr lt_term) {
}

void ConstraintQuerier::visitLe(Le_ptr le_term) {
}

void ConstraintQuerier::visitConcat(Concat_ptr concat_term) {

}

void ConstraintQuerier::visitIn(In_ptr in_term) {

}

void ConstraintQuerier::visitNotIn(NotIn_ptr not_in_term) {

}

void ConstraintQuerier::visitLen(Len_ptr len_term) {

}

void ConstraintQuerier::visitContains(Contains_ptr contains_term) {

}

void ConstraintQuerier::visitNotContains(NotContains_ptr not_contains_term) {
}

void ConstraintQuerier::visitBegins(Begins_ptr begins_term) {
}

void ConstraintQuerier::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void ConstraintQuerier::visitEnds(Ends_ptr ends_term) {
}

void ConstraintQuerier::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void ConstraintQuerier::visitIndexOf(IndexOf_ptr index_of_term) {

  switch (mode_) {
    case Mode::QUERY: {
      if (param_index_ == 1) { // check again param 1
        query_result_ = Ast2Dot::isEquivalent(search_term_, index_of_term->subject_term);
      }
    }
      break;
    case Mode::GET: {
      if (param_index_ == 1) {
        search_term_ = index_of_term->subject_term;
      } else if (param_index_ == 2) {
        search_term_ = index_of_term->search_term;
      } else if (param_index_ == 3) {
        search_term_ = index_of_term->from_index;
      }
    }
      break;
    default:
      break;
  }

}

void ConstraintQuerier::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

void ConstraintQuerier::visitCharAt(CharAt_ptr char_at_term) {
}

void ConstraintQuerier::visitSubString(SubString_ptr sub_string_term) {

}

void ConstraintQuerier::visitToUpper(ToUpper_ptr to_upper_term) {
}

void ConstraintQuerier::visitToLower(ToLower_ptr to_lower_term) {
}

void ConstraintQuerier::visitTrim(Trim_ptr trim_term) {

}

void ConstraintQuerier::visitToString(ToString_ptr to_string_term) {
}

void ConstraintQuerier::visitToInt(ToInt_ptr to_int_term) {
}

void ConstraintQuerier::visitReplace(Replace_ptr replace_term) {
}

void ConstraintQuerier::visitCount(Count_ptr count_term) {
}

void ConstraintQuerier::visitIte(Ite_ptr ite_term) {
}

void ConstraintQuerier::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstraintQuerier::visitReUnion(ReUnion_ptr re_union_term) {
}

void ConstraintQuerier::visitReInter(ReInter_ptr re_inter_term) {
}

void ConstraintQuerier::visitReStar(ReStar_ptr re_star_term) {
}

void ConstraintQuerier::visitRePlus(RePlus_ptr re_plus_term) {
}

void ConstraintQuerier::visitReOpt(ReOpt_ptr re_opt_term) {
}

void ConstraintQuerier::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstraintQuerier::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void ConstraintQuerier::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ConstraintQuerier::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void ConstraintQuerier::visitTermConstant(TermConstant_ptr term_constant) {
//  if (Primitive::Type::STRING == term_constant->getValueType()) {
//    term_constant_ = term_constant;
//    string_value_ = term_constant->getValue();
//  } else if (Primitive::Type::REGEX == term_constant->getValueType()) {
//    std::string data = term_constant->getValue();
//    Util::RegularExpression regular_expression (data);
//    if (regular_expression.is_constant_string()) {
//      term_constant->primitive->setType(Primitive::Type::STRING);
//      term_constant->primitive->setData(regular_expression.constant_str());
//      term_constant_ = term_constant;
//      string_value_ = term_constant->getValue();
//      DVLOG(VLOG_LEVEL) << "Constant string regex transformed";
//    }
//  } else if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
//    term_constant_ = term_constant;
//    string_value_ = term_constant->getValue();
//  } else if (Primitive::Type::BOOL == term_constant->getValueType()) {
//    term_constant_ = term_constant;
//    string_value_ = term_constant->getValue();
//  }
}

void ConstraintQuerier::visitIdentifier(Identifier_ptr identifier) {
}

void ConstraintQuerier::visitPrimitive(Primitive_ptr primitive) {
}

void ConstraintQuerier::visitTVariable(TVariable_ptr t_variable) {
}

void ConstraintQuerier::visitTBool(TBool_ptr t_bool) {
}

void ConstraintQuerier::visitTInt(TInt_ptr t_int) {
}

void ConstraintQuerier::visitTString(TString_ptr t_string) {
}

void ConstraintQuerier::visitVariable(Variable_ptr variable) {
}

void ConstraintQuerier::visitSort(Sort_ptr sort) {
}

void ConstraintQuerier::visitAttribute(Attribute_ptr attribute) {
}

void ConstraintQuerier::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ConstraintQuerier::visitVarBinding(VarBinding_ptr var_binding) {
}

} /* namespace Optimization */
} /* namespace Solver */
} /* namespace Vlab */
