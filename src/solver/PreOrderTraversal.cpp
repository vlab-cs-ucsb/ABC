/*
 * PreOrderTraversal.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#include "PreOrderTraversal.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

PreOrderTraversal::PreOrderTraversal(Script_ptr script) :
    root (script) {

}

PreOrderTraversal::~PreOrderTraversal() {

}

void PreOrderTraversal::setCommandCallback(std::function<bool(SMT::Command_ptr)> command_callback) {
}

void PreOrderTraversal::setTermCallback(std::function<bool(SMT::Term_ptr)> term_callback) {
}

void PreOrderTraversal::start() {
  visit(root);
}

void PreOrderTraversal::end() {
}

void PreOrderTraversal::visitScript(SMT::Script_ptr script) {
  visit_children_of(script);
}

void PreOrderTraversal::visitCommand(SMT::Command_ptr command) {
  if (command_callback and command_callback(command)) {
    visit_children_of(command);
  }
}

void PreOrderTraversal::visitAssert(Assert_ptr assert_command) {
  if (command_callback and command_callback(assert_command)) {
    parent_term_stack.push(&assert_command->term);
    visit(assert_command->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitTerm(SMT::Term_ptr term) {

}

void PreOrderTraversal::visitExclamation(SMT::Exclamation_ptr exclamation_term) {
  if (term_callback and term_callback(exclamation_term)) {
    parent_term_stack.push(&exclamation_term->term);
    visit(exclamation_term->term);
    parent_term_stack.pop();
    visit_list(exclamation_term->attribute_list);
  }
}

void PreOrderTraversal::visitExists(SMT::Exists_ptr exists_term) {
  if (term_callback and term_callback(exists_term)) {
    visit_list(exists_term->sorted_var_list);
    parent_term_stack.push(&exists_term->term);
    visit(exists_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitForAll(SMT::ForAll_ptr for_all_term) {
  if (term_callback and term_callback(for_all_term)) {
    visit_list(for_all_term->sorted_var_list);
    parent_term_stack.push(&for_all_term->term);
    visit(for_all_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitLet(SMT::Let_ptr let_term) {
  if (term_callback and term_callback(let_term)) {
    visit_list(let_term->var_binding_list);
    parent_term_stack.push(&let_term->term);
    visit(let_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitAnd(SMT::And_ptr and_term) {
  if (term_callback and term_callback(and_term)) {
    for (auto& term : *and_term->term_list) {
      parent_term_stack.push(&term);
      visit(term);
      parent_term_stack.pop();
    }
  }
}

void PreOrderTraversal::visitOr(SMT::Or_ptr or_term) {
  if (term_callback and term_callback(or_term)) {
    for (auto& term : *or_term->term_list) {
      parent_term_stack.push(&term);
      visit(term);
      parent_term_stack.pop();
    }
  }
}

void PreOrderTraversal::visitNot(SMT::Not_ptr not_term) {
  if (term_callback and term_callback(not_term)) {
    parent_term_stack.push(&not_term->term);
    visit(not_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitUMinus(SMT::UMinus_ptr u_minus_term) {
  if (term_callback and term_callback(u_minus_term)) {
    parent_term_stack.push(&u_minus_term->term);
    visit(u_minus_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitMinus(SMT::Minus_ptr minus_term) {
  if (term_callback and term_callback(minus_term)) {
    parent_term_stack.push(&minus_term->left_term);
    visit(minus_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&minus_term->right_term);
    visit(minus_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitPlus(SMT::Plus_ptr plus_term) {
  if (term_callback and term_callback(plus_term)) {
    parent_term_stack.push(&plus_term->left_term);
    visit(plus_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&plus_term->right_term);
    visit(plus_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitEq(SMT::Eq_ptr eq_term) {
  if (term_callback and term_callback(eq_term)) {
    parent_term_stack.push(&eq_term->left_term);
    visit(eq_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&eq_term->right_term);
    visit(eq_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitNotEq(SMT::NotEq_ptr not_eq_term) {
  if (term_callback and term_callback(not_eq_term)) {
    parent_term_stack.push(&not_eq_term->left_term);
    visit(not_eq_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&not_eq_term->right_term);
    visit(not_eq_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitGt(SMT::Gt_ptr gt_term) {
  if (term_callback and term_callback(gt_term)) {
    parent_term_stack.push(&gt_term->left_term);
    visit(gt_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&gt_term->right_term);
    visit(gt_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitGe(SMT::Ge_ptr ge_term) {
  if (term_callback and term_callback(ge_term)) {
    parent_term_stack.push(&ge_term->left_term);
    visit(ge_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&ge_term->right_term);
    visit(ge_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitLt(SMT::Lt_ptr lt_term) {
  if (term_callback and term_callback(lt_term)) {
    parent_term_stack.push(&lt_term->left_term);
    visit(lt_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&lt_term->right_term);
    visit(lt_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitLe(SMT::Le_ptr le_term) {
  if (term_callback and term_callback(le_term)) {
    parent_term_stack.push(&le_term->left_term);
    visit(le_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&le_term->right_term);
    visit(le_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitConcat(SMT::Concat_ptr concat_term) {
  if (term_callback and term_callback(concat_term)) {
    for (auto& term : *concat_term->term_list) {
      parent_term_stack.push(&term);
      visit(term);
      parent_term_stack.pop();
    }
  }
}

void PreOrderTraversal::visitIn(SMT::In_ptr in_term) {
  if (term_callback and term_callback(in_term)) {
    parent_term_stack.push(&in_term->left_term);
    visit(in_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&in_term->right_term);
    visit(in_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitNotIn(SMT::NotIn_ptr not_in_term) {
  if (term_callback and term_callback(not_in_term)) {
    parent_term_stack.push(&not_in_term->left_term);
    visit(not_in_term->left_term);
    parent_term_stack.pop();
    parent_term_stack.push(&not_in_term->right_term);
    visit(not_in_term->right_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitLen(SMT::Len_ptr len_term) {
  if (term_callback and term_callback(len_term)) {
    parent_term_stack.push(&len_term->term);
    visit(len_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitContains(SMT::Contains_ptr contains_term) {
  if (term_callback and term_callback(contains_term)) {
    parent_term_stack.push(&contains_term->subject_term);
    visit(contains_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&contains_term->search_term);
    visit(contains_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitNotContains(SMT::NotContains_ptr not_contains_term) {
  if (term_callback and term_callback(not_contains_term)) {
    parent_term_stack.push(&not_contains_term->subject_term);
    visit(not_contains_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&not_contains_term->search_term);
    visit(not_contains_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitBegins(SMT::Begins_ptr begins_term) {
  if (term_callback and term_callback(begins_term)) {
    parent_term_stack.push(&begins_term->subject_term);
    visit(begins_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&begins_term->search_term);
    visit(begins_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitNotBegins(SMT::NotBegins_ptr not_begins_term) {
  if (term_callback and term_callback(not_begins_term)) {
    parent_term_stack.push(&not_begins_term->subject_term);
    visit(not_begins_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&not_begins_term->search_term);
    visit(not_begins_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitEnds(SMT::Ends_ptr ends_term) {
  if (term_callback and term_callback(ends_term)) {
    parent_term_stack.push(&ends_term->subject_term);
    visit(ends_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&ends_term->search_term);
    visit(ends_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitNotEnds(SMT::NotEnds_ptr not_ends_term) {
  if (term_callback and term_callback(not_ends_term)) {
    parent_term_stack.push(&not_ends_term->subject_term);
    visit(not_ends_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&not_ends_term->search_term);
    visit(not_ends_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitIndexOf(SMT::IndexOf_ptr index_of_term) {
  if (term_callback and term_callback(index_of_term)) {
    parent_term_stack.push(&index_of_term->subject_term);
    visit(index_of_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&index_of_term->search_term);
    visit(index_of_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  if (term_callback and term_callback(last_index_of_term)) {
    parent_term_stack.push(&last_index_of_term->subject_term);
    visit(last_index_of_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&last_index_of_term->search_term);
    visit(last_index_of_term->search_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitCharAt(SMT::CharAt_ptr char_at_term) {
  if (term_callback and term_callback(char_at_term)) {
    parent_term_stack.push(&char_at_term->subject_term);
    visit(char_at_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&char_at_term->index_term);
    visit(char_at_term->index_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitSubString(SMT::SubString_ptr sub_string_term) {
  if (term_callback and term_callback(sub_string_term)) {
    parent_term_stack.push(&sub_string_term->subject_term);
    visit(sub_string_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&sub_string_term->start_index_term);
    visit(sub_string_term->start_index_term);
    parent_term_stack.pop();
    if (sub_string_term->end_index_term) {
      parent_term_stack.push(&sub_string_term->end_index_term);
      visit(sub_string_term->end_index_term);
      parent_term_stack.pop();
    }
  }
}

void PreOrderTraversal::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  if (term_callback and term_callback(to_upper_term)) {
    parent_term_stack.push(&to_upper_term->subject_term);
    visit(to_upper_term->subject_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitToLower(SMT::ToLower_ptr to_lower_term) {
  if (term_callback and term_callback(to_lower_term)) {
    parent_term_stack.push(&to_lower_term->subject_term);
    visit(to_lower_term->subject_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitTrim(SMT::Trim_ptr trim_term) {
  if (term_callback and term_callback(trim_term)) {
    parent_term_stack.push(&trim_term->subject_term);
    visit(trim_term->subject_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitReplace(SMT::Replace_ptr replace_term) {
  if (term_callback and term_callback(replace_term)) {
    parent_term_stack.push(&replace_term->subject_term);
    visit(replace_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&replace_term->search_term);
    visit(replace_term->search_term);
    parent_term_stack.pop();
    parent_term_stack.push(&replace_term->replace_term);
    visit(replace_term->replace_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitCount(SMT::Count_ptr count_term) {
  if (term_callback and term_callback(count_term)) {
    parent_term_stack.push(&count_term->subject_term);
    visit(count_term->subject_term);
    parent_term_stack.pop();
    parent_term_stack.push(&count_term->bound_term);
    visit(count_term->bound_term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitIte(SMT::Ite_ptr ite_term) {
  if (term_callback and term_callback(ite_term)) {
    parent_term_stack.push(&ite_term->cond);
    visit(ite_term->cond);
    parent_term_stack.pop();
    parent_term_stack.push(&ite_term->then_branch);
    visit(ite_term->then_branch);
    parent_term_stack.pop();
    parent_term_stack.push(&ite_term->else_branch);
    visit(ite_term->else_branch);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitReConcat(SMT::ReConcat_ptr re_concat_term) {
  if (term_callback and term_callback(re_concat_term)) {
    for (auto& term : *re_concat_term->term_list) {
      parent_term_stack.push(&term);
      visit(term);
      parent_term_stack.pop();
    }
  }
}

void PreOrderTraversal::visitToRegex(SMT::ToRegex_ptr to_regex_term) {
  if (term_callback and term_callback(to_regex_term)) {
    parent_term_stack.push(&to_regex_term->term);
    visit(to_regex_term->term);
    parent_term_stack.pop();
  }
}

void PreOrderTraversal::visitUnknownTerm(SMT::Unknown_ptr unknown_term) {
  if (term_callback and term_callback(unknown_term)) {
    parent_term_stack.push(&unknown_term->term);
    visit(unknown_term->term);
    parent_term_stack.pop();
    for (auto& term : *unknown_term->term_list) {
      parent_term_stack.push(&term);
      visit(term);
      parent_term_stack.pop();
    }
  }
}

void PreOrderTraversal::visitAsQualIdentifier(SMT::AsQualIdentifier_ptr as_qi_term) {
  if (term_callback and term_callback(as_qi_term)) {
    visit_children_of(as_qi_term);
  }
}

void PreOrderTraversal::visitQualIdentifier(SMT::QualIdentifier_ptr qi_term) {
  if (term_callback and term_callback(qi_term)) {
    visit_children_of(qi_term);
  }
}

void PreOrderTraversal::visitTermConstant(SMT::TermConstant_ptr term_constant) {
  if (term_callback and term_callback(term_constant)) {
    visit_children_of(term_constant);
  }
}

void PreOrderTraversal::visitSort(SMT::Sort_ptr sort) {
   visit_children_of(sort);
}

void PreOrderTraversal::visitTVariable(SMT::TVariable_ptr t_variable) {
  visit_children_of(t_variable);
}

void PreOrderTraversal::visitTBool(SMT::TBool_ptr t_bool) {
  visit_children_of(t_bool);
}

void PreOrderTraversal::visitTInt(SMT::TInt_ptr t_int) {
  visit_children_of(t_int);
}

void PreOrderTraversal::visitTString(SMT::TString_ptr t_string) {
  visit_children_of(t_string);
}

void PreOrderTraversal::visitAttribute(SMT::Attribute_ptr attribute) {
  visit_children_of(attribute);
}

void PreOrderTraversal::visitSortedVar(SMT::SortedVar_ptr sorted_var) {
  visit_children_of(sorted_var);
}

void PreOrderTraversal::visitVarBinding(SMT::VarBinding_ptr var_binding) {
  visit_children_of(var_binding);
}

void PreOrderTraversal::visitIdentifier(SMT::Identifier_ptr identifier) {
  visit_children_of(identifier);
}

void PreOrderTraversal::visitPrimitive(SMT::Primitive_ptr primitive) {
  visit_children_of(primitive);
}

void PreOrderTraversal::visitVariable(SMT::Variable_ptr variable) {
  visit_children_of(variable);
}

void PreOrderTraversal::push(SMT::Term_ptr* parent_term_ptr) {
  parent_term_stack.push(parent_term_ptr);
}

void PreOrderTraversal::pop() {
  parent_term_stack.pop();
}

SMT::Term_ptr* PreOrderTraversal::top() {
  return parent_term_stack.top();
}

} /* namespace Solver */
} /* namespace Vlab */

