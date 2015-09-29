/*
 * AstTraverser.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#include "AstTraverser.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

AstTraverser::AstTraverser(Script_ptr script) :
    root (script) {

}

AstTraverser::~AstTraverser() {

}

void AstTraverser::setCommandPreCallback(std::function<bool(SMT::Command_ptr)> command_callback) {
  this->command_pre_callback = command_callback;
}

void AstTraverser::setTermPreCallback(std::function<bool(SMT::Term_ptr)> term_callback) {
  this->term_pre_callback = term_callback;
}

void AstTraverser::setCommandPostCallback(std::function<bool(SMT::Command_ptr)> command_callback) {
  this->command_post_callback = command_callback;

  if (not command_pre_callback) {
    command_pre_callback = [] (Command_ptr command) -> bool {
      return true;
    };
  }
}

void AstTraverser::setTermPostCallback(std::function<bool(SMT::Term_ptr)> term_callback) {
  this->term_post_callback = term_callback;

  if (not command_pre_callback) {
    command_pre_callback = [] (Command_ptr command) -> bool {
      return true;
    };
  }

  if (not term_pre_callback) {
    term_pre_callback = [] (Term_ptr term) -> bool {
      return true;
    };
  }
}

void AstTraverser::start() {
  Visitor::visit(root);
}

void AstTraverser::end() {
}

void AstTraverser::visitScript(SMT::Script_ptr script) {
  visit_children_of(script);
}

void AstTraverser::visitCommand(SMT::Command_ptr command) {
  if (command_pre_callback and command_pre_callback(command)) {
    visit_children_of(command);
  }

  if (command_post_callback) {
    command_post_callback(command);
  }
}

void AstTraverser::visitAssert(Assert_ptr assert_command) {
  if (command_pre_callback and command_pre_callback(assert_command)) {
    visit(assert_command->term);
  }

  if (command_post_callback) {
    command_post_callback(assert_command);
  }
}

void AstTraverser::visitTerm(SMT::Term_ptr term) {

}

void AstTraverser::visitExclamation(SMT::Exclamation_ptr exclamation_term) {
  if (term_pre_callback and term_pre_callback(exclamation_term)) {
    visit(exclamation_term->term);
    visit_list(exclamation_term->attribute_list);
  }

  if (term_post_callback) {
    term_post_callback(exclamation_term);
  }
}

void AstTraverser::visitExists(SMT::Exists_ptr exists_term) {
  if (term_pre_callback and term_pre_callback(exists_term)) {
    visit_list(exists_term->sorted_var_list);
    visit(exists_term->term);
  }

  if (term_post_callback) {
    term_post_callback(exists_term);
  }
}

void AstTraverser::visitForAll(SMT::ForAll_ptr for_all_term) {
  if (term_pre_callback and term_pre_callback(for_all_term)) {
    visit_list(for_all_term->sorted_var_list);
    visit(for_all_term->term);
  }

  if (term_post_callback) {
    term_post_callback(for_all_term);
  }
}

void AstTraverser::visitLet(SMT::Let_ptr let_term) {
  if (term_pre_callback and term_pre_callback(let_term)) {
    visit_list(let_term->var_binding_list);
    visit(let_term->term);
  }

  if (term_post_callback) {
    term_post_callback(let_term);
  }
}

void AstTraverser::visitAnd(SMT::And_ptr and_term) {
  if (term_pre_callback and term_pre_callback(and_term)) {
    for (auto& term : *and_term->term_list) {
      visit(term);
    }
  }

  if (term_post_callback) {
    term_post_callback(and_term);
  }
}

void AstTraverser::visitOr(SMT::Or_ptr or_term) {
  if (term_pre_callback and term_pre_callback(or_term)) {
    for (auto& term : *or_term->term_list) {
      visit(term);
    }
  }

  if (term_post_callback) {
    term_post_callback(or_term);
  }
}

void AstTraverser::visitNot(SMT::Not_ptr not_term) {
  if (term_pre_callback and term_pre_callback(not_term)) {
    visit(not_term->term);
  }

  if (term_post_callback) {
    term_post_callback(not_term);
  }
}

void AstTraverser::visitUMinus(SMT::UMinus_ptr u_minus_term) {
  if (term_pre_callback and term_pre_callback(u_minus_term)) {
    visit(u_minus_term->term);
  }

  if (term_post_callback) {
    term_post_callback(u_minus_term);
  }
}

void AstTraverser::visitMinus(SMT::Minus_ptr minus_term) {
  if (term_pre_callback and term_pre_callback(minus_term)) {
    visit(minus_term->left_term);
    visit(minus_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(minus_term);
  }
}

void AstTraverser::visitPlus(SMT::Plus_ptr plus_term) {
  if (term_pre_callback and term_pre_callback(plus_term)) {
    visit(plus_term->left_term);
    visit(plus_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(plus_term);
  }
}

void AstTraverser::visitEq(SMT::Eq_ptr eq_term) {
  if (term_pre_callback and term_pre_callback(eq_term)) {
    visit(eq_term->left_term);
    visit(eq_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(eq_term);
  }
}

void AstTraverser::visitNotEq(SMT::NotEq_ptr not_eq_term) {
  if (term_pre_callback and term_pre_callback(not_eq_term)) {
    visit(not_eq_term->left_term);
    visit(not_eq_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(not_eq_term);
  }
}

void AstTraverser::visitGt(SMT::Gt_ptr gt_term) {
  if (term_pre_callback and term_pre_callback(gt_term)) {
    visit(gt_term->left_term);
    visit(gt_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(gt_term);
  }
}

void AstTraverser::visitGe(SMT::Ge_ptr ge_term) {
  if (term_pre_callback and term_pre_callback(ge_term)) {
    visit(ge_term->left_term);
    visit(ge_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(ge_term);
  }
}

void AstTraverser::visitLt(SMT::Lt_ptr lt_term) {
  if (term_pre_callback and term_pre_callback(lt_term)) {
    visit(lt_term->left_term);
    visit(lt_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(lt_term);
  }
}

void AstTraverser::visitLe(SMT::Le_ptr le_term) {
  if (term_pre_callback and term_pre_callback(le_term)) {
    visit(le_term->left_term);
    visit(le_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(le_term);
  }
}

void AstTraverser::visitConcat(SMT::Concat_ptr concat_term) {
  if (term_pre_callback and term_pre_callback(concat_term)) {
    for (auto& term : *concat_term->term_list) {
      visit(term);
    }
  }

  if (term_post_callback) {
    term_post_callback(concat_term);
  }
}

void AstTraverser::visitIn(SMT::In_ptr in_term) {
  if (term_pre_callback and term_pre_callback(in_term)) {
    visit(in_term->left_term);
    visit(in_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(in_term);
  }
}

void AstTraverser::visitNotIn(SMT::NotIn_ptr not_in_term) {
  if (term_pre_callback and term_pre_callback(not_in_term)) {
    visit(not_in_term->left_term);
    visit(not_in_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(not_in_term);
  }
}

void AstTraverser::visitLen(SMT::Len_ptr len_term) {
  if (term_pre_callback and term_pre_callback(len_term)) {
    visit(len_term->term);
  }

  if (term_post_callback) {
    term_post_callback(len_term);
  }
}

void AstTraverser::visitContains(SMT::Contains_ptr contains_term) {
  if (term_pre_callback and term_pre_callback(contains_term)) {
    visit(contains_term->subject_term);
    visit(contains_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(contains_term);
  }
}

void AstTraverser::visitNotContains(SMT::NotContains_ptr not_contains_term) {
  if (term_pre_callback and term_pre_callback(not_contains_term)) {
    visit(not_contains_term->subject_term);
    visit(not_contains_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(not_contains_term);
  }
}

void AstTraverser::visitBegins(SMT::Begins_ptr begins_term) {
  if (term_pre_callback and term_pre_callback(begins_term)) {
    visit(begins_term->subject_term);
    visit(begins_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(begins_term);
  }
}

void AstTraverser::visitNotBegins(SMT::NotBegins_ptr not_begins_term) {
  if (term_pre_callback and term_pre_callback(not_begins_term)) {
    visit(not_begins_term->subject_term);
    visit(not_begins_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(not_begins_term);
  }
}

void AstTraverser::visitEnds(SMT::Ends_ptr ends_term) {
  if (term_pre_callback and term_pre_callback(ends_term)) {
    visit(ends_term->subject_term);
    visit(ends_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(ends_term);
  }
}

void AstTraverser::visitNotEnds(SMT::NotEnds_ptr not_ends_term) {
  if (term_pre_callback and term_pre_callback(not_ends_term)) {
    visit(not_ends_term->subject_term);
    visit(not_ends_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(not_ends_term);
  }
}

void AstTraverser::visitIndexOf(SMT::IndexOf_ptr index_of_term) {
  if (term_pre_callback and term_pre_callback(index_of_term)) {
    visit(index_of_term->subject_term);
    visit(index_of_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(index_of_term);
  }
}

void AstTraverser::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  if (term_pre_callback and term_pre_callback(last_index_of_term)) {
    visit(last_index_of_term->subject_term);
    visit(last_index_of_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(last_index_of_term);
  }
}

void AstTraverser::visitCharAt(SMT::CharAt_ptr char_at_term) {
  if (term_pre_callback and term_pre_callback(char_at_term)) {
    visit(char_at_term->subject_term);
    visit(char_at_term->index_term);
  }

  if (term_post_callback) {
    term_post_callback(char_at_term);
  }
}

void AstTraverser::visitSubString(SMT::SubString_ptr sub_string_term) {
  if (term_pre_callback and term_pre_callback(sub_string_term)) {
    visit(sub_string_term->subject_term);
    visit(sub_string_term->start_index_term);
    if (sub_string_term->end_index_term) {
      visit(sub_string_term->end_index_term);
    }
  }

  if (term_post_callback) {
    term_post_callback(sub_string_term);
  }
}

void AstTraverser::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  if (term_pre_callback and term_pre_callback(to_upper_term)) {
    visit(to_upper_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(to_upper_term);
  }
}

void AstTraverser::visitToLower(SMT::ToLower_ptr to_lower_term) {
  if (term_pre_callback and term_pre_callback(to_lower_term)) {
    visit(to_lower_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(to_lower_term);
  }
}

void AstTraverser::visitTrim(SMT::Trim_ptr trim_term) {
  if (term_pre_callback and term_pre_callback(trim_term)) {
    visit(trim_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(trim_term);
  }
}

void AstTraverser::visitReplace(SMT::Replace_ptr replace_term) {
  if (term_pre_callback and term_pre_callback(replace_term)) {
    visit(replace_term->subject_term);
    visit(replace_term->search_term);
    visit(replace_term->replace_term);
  }

  if (term_post_callback) {
    term_post_callback(replace_term);
  }
}

void AstTraverser::visitCount(SMT::Count_ptr count_term) {
  if (term_pre_callback and term_pre_callback(count_term)) {
    visit(count_term->subject_term);
    visit(count_term->bound_term);
  }

  if (term_post_callback) {
    term_post_callback(count_term);
  }
}

void AstTraverser::visitIte(SMT::Ite_ptr ite_term) {
  if (term_pre_callback and term_pre_callback(ite_term)) {
    visit(ite_term->cond);
    visit(ite_term->then_branch);
    visit(ite_term->else_branch);
  }

  if (term_post_callback) {
    term_post_callback(ite_term);
  }
}

void AstTraverser::visitReConcat(SMT::ReConcat_ptr re_concat_term) {
  if (term_pre_callback and term_pre_callback(re_concat_term)) {
    for (auto& term : *re_concat_term->term_list) {
      visit(term);
    }
  }

  if (term_post_callback) {
    term_post_callback(re_concat_term);
  }
}

void AstTraverser::visitToRegex(SMT::ToRegex_ptr to_regex_term) {
  if (term_pre_callback and term_pre_callback(to_regex_term)) {
    visit(to_regex_term->term);
  }

  if (term_post_callback) {
    term_post_callback(to_regex_term);
  }
}

void AstTraverser::visitUnknownTerm(SMT::Unknown_ptr unknown_term) {
  if (term_pre_callback and term_pre_callback(unknown_term)) {
    visit(unknown_term->term);
    for (auto& term : *unknown_term->term_list) {
      visit(term);
    }
  }

  if (term_post_callback) {
    term_post_callback(unknown_term);
  }
}

void AstTraverser::visitAsQualIdentifier(SMT::AsQualIdentifier_ptr as_qi_term) {
  if (term_pre_callback and term_pre_callback(as_qi_term)) {
    visit_children_of(as_qi_term);
  }

  if (term_post_callback) {
    term_post_callback(as_qi_term);
  }
}

void AstTraverser::visitQualIdentifier(SMT::QualIdentifier_ptr qi_term) {
  if (term_pre_callback and term_pre_callback(qi_term)) {
    visit_children_of(qi_term);
  }

  if (term_post_callback) {
    term_post_callback(qi_term);
  }
}

void AstTraverser::visitTermConstant(SMT::TermConstant_ptr term_constant) {
  if (term_pre_callback and term_pre_callback(term_constant)) {
    visit_children_of(term_constant);
  }

  if (term_post_callback) {
    term_post_callback(term_constant);
  }
}

void AstTraverser::visitSort(SMT::Sort_ptr sort) {
   visit_children_of(sort);
}

void AstTraverser::visitTVariable(SMT::TVariable_ptr t_variable) {
  visit_children_of(t_variable);
}

void AstTraverser::visitTBool(SMT::TBool_ptr t_bool) {
  visit_children_of(t_bool);
}

void AstTraverser::visitTInt(SMT::TInt_ptr t_int) {
  visit_children_of(t_int);
}

void AstTraverser::visitTString(SMT::TString_ptr t_string) {
  visit_children_of(t_string);
}

void AstTraverser::visitAttribute(SMT::Attribute_ptr attribute) {
  visit_children_of(attribute);
}

void AstTraverser::visitSortedVar(SMT::SortedVar_ptr sorted_var) {
  visit_children_of(sorted_var);
}

void AstTraverser::visitVarBinding(SMT::VarBinding_ptr var_binding) {
  visit_children_of(var_binding);
}

void AstTraverser::visitIdentifier(SMT::Identifier_ptr identifier) {
  visit_children_of(identifier);
}

void AstTraverser::visitPrimitive(SMT::Primitive_ptr primitive) {
  visit_children_of(primitive);
}

void AstTraverser::visitVariable(SMT::Variable_ptr variable) {
  visit_children_of(variable);
}

void AstTraverser::push(SMT::Term_ptr* parent_term_ptr) {
  term_stack.push(parent_term_ptr);
}

void AstTraverser::pop() {
  term_stack.pop();
}

SMT::Term_ptr* AstTraverser::top() {
  return term_stack.top();
}

void AstTraverser::visit(SMT::Term_ptr& term) {
  term_stack.push(&term);
  Visitor::visit(term);
  term_stack.pop();
}

} /* namespace Solver */
} /* namespace Vlab */

