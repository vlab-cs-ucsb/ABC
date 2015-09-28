/*
 * PostOrderTraversal.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#include "PostOrderTraversal.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

PostOrderTraversal::PostOrderTraversal(Script_ptr script) :
    root (script), parent_term (nullptr) {

}

PostOrderTraversal::~PostOrderTraversal() {
}

void PostOrderTraversal::setCommandCallback(
    std::function<bool(SMT::Command_ptr)> command_callback) {
  this->command_callback = command_callback;
}

void PostOrderTraversal::setTermCallback(
    std::function<bool(SMT::Term_ptr)> term_callback) {
  this->term_callback = term_callback;
}

void PostOrderTraversal::start() {
}

void PostOrderTraversal::end() {
}

void PostOrderTraversal::visitScript(SMT::Script_ptr script) {
  visit_children_of(script);
}

void PostOrderTraversal::visitCommand(SMT::Command_ptr command) {
  visit_children_of(command);
}

void PostOrderTraversal::visitTerm(SMT::Term_ptr term) {
  visit_children_of(term);
}

void PostOrderTraversal::visitExclamation(SMT::Exclamation_ptr exclamation_term) {
  visit_children_of(exclamation_term);
}

void PostOrderTraversal::visitExists(SMT::Exists_ptr exists_term) {
  visit_children_of(exists_term);
}

void PostOrderTraversal::visitForAll(SMT::ForAll_ptr for_all_term) {
  visit_children_of(for_all_term);
}

void PostOrderTraversal::visitLet(SMT::Let_ptr let_term) {
  visit_children_of(let_term);
}

void PostOrderTraversal::visitAnd(SMT::And_ptr and_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitOr(SMT::Or_ptr or_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitNot(SMT::Not_ptr not_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitUMinus(SMT::UMinus_ptr u_minus_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitMinus(SMT::Minus_ptr minus_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitPlus(SMT::Plus_ptr plus_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitEq(SMT::Eq_ptr eq_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitNotEq(SMT::NotEq_ptr not_eq_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitGt(SMT::Gt_ptr gt_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitGe(SMT::Ge_ptr ge_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitLt(SMT::Lt_ptr lt_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitLe(SMT::Le_ptr le_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitConcat(SMT::Concat_ptr concat_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitIn(SMT::In_ptr in_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitNotIn(SMT::NotIn_ptr not_in_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitLen(SMT::Len_ptr len_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitContains(SMT::Contains_ptr contains_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitNotContains(SMT::NotContains_ptr not_contains_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitBegins(SMT::Begins_ptr begins_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitNotBegins(SMT::NotBegins_ptr not_begins_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitEnds(SMT::Ends_ptr ends_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitNotEnds(SMT::NotEnds_ptr not_ends_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitIndexOf(SMT::IndexOf_ptr index_of_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitSubString(SMT::SubString_ptr sub_string_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitTrim(SMT::Trim_ptr trim_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitReplace(SMT::Replace_ptr replace_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitCount(SMT::Count_ptr count_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitIte(SMT::Ite_ptr ite_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitReConcat(SMT::ReConcat_ptr re_concat_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitToRegex(SMT::ToRegex_ptr to_regex_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitUnknownTerm(SMT::Unknown_ptr unknown_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitAsQualIdentifier(SMT::AsQualIdentifier_ptr as_qi_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitQualIdentifier(SMT::QualIdentifier_ptr qi_term) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitTermConstant(SMT::TermConstant_ptr term_constant) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitSort(SMT::Sort_ptr sort) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitTVariable(SMT::TVariable_ptr t_variable) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitTBool(SMT::TBool_ptr t_bool) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitTInt(SMT::TInt_ptr t_int) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitTString(SMT::TString_ptr t_string) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitAttribute(SMT::Attribute_ptr attribute) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitSortedVar(SMT::SortedVar_ptr sorted_var) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitVarBinding(SMT::VarBinding_ptr var_binding) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitIdentifier(SMT::Identifier_ptr identifier) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitPrimitive(SMT::Primitive_ptr primitive) {
  visit_children_of(and_term);
}

void PostOrderTraversal::visitVariable(SMT::Variable_ptr variable) {
  visit_children_of(and_term);
}

} /* namespace Solver */
} /* namespace Vlab */
