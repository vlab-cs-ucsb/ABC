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

void AstTraverser::setCommandPreCallback(std::function<bool(Command_ptr)> command_callback) {
  this->command_pre_callback = command_callback;
}

void AstTraverser::setTermPreCallback(std::function<bool(Term_ptr)> term_callback) {
  this->term_pre_callback = term_callback;
}

void AstTraverser::setCommandPostCallback(std::function<bool(Command_ptr)> command_callback) {
  this->command_post_callback = command_callback;

  if (not command_pre_callback) {
    command_pre_callback = [] (Command_ptr command) -> bool {
      return true;
    };
  }
}

void AstTraverser::setTermPostCallback(std::function<bool(Term_ptr)> term_callback) {
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

void AstTraverser::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void AstTraverser::visitCommand(Command_ptr command) {
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

void AstTraverser::visitTerm(Term_ptr term) {

}

void AstTraverser::visitExclamation(Exclamation_ptr exclamation_term) {
  if (term_pre_callback and term_pre_callback(exclamation_term)) {
    visit(exclamation_term->term);
    visit_list(exclamation_term->attribute_list);
  }

  if (term_post_callback) {
    term_post_callback(exclamation_term);
  }
}

void AstTraverser::visitExists(Exists_ptr exists_term) {
  if (term_pre_callback and term_pre_callback(exists_term)) {
    visit_list(exists_term->sorted_var_list);
    visit(exists_term->term);
  }

  if (term_post_callback) {
    term_post_callback(exists_term);
  }
}

void AstTraverser::visitForAll(ForAll_ptr for_all_term) {
  if (term_pre_callback and term_pre_callback(for_all_term)) {
    visit_list(for_all_term->sorted_var_list);
    visit(for_all_term->term);
  }

  if (term_post_callback) {
    term_post_callback(for_all_term);
  }
}

void AstTraverser::visitLet(Let_ptr let_term) {
  if (term_pre_callback and term_pre_callback(let_term)) {
    visit_list(let_term->var_binding_list);
    visit(let_term->term);
  }

  if (term_post_callback) {
    term_post_callback(let_term);
  }
}

void AstTraverser::visitAnd(And_ptr and_term) {
  if (term_pre_callback and term_pre_callback(and_term)) {
    visit_term_list(and_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(and_term);
  }
}

void AstTraverser::visitOr(Or_ptr or_term) {
  if (term_pre_callback and term_pre_callback(or_term)) {
    visit_term_list(or_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(or_term);
  }
}

void AstTraverser::visitNot(Not_ptr not_term) {
  if (term_pre_callback and term_pre_callback(not_term)) {
    visit(not_term->term);
  }

  if (term_post_callback) {
    term_post_callback(not_term);
  }
}

void AstTraverser::visitUMinus(UMinus_ptr u_minus_term) {
  if (term_pre_callback and term_pre_callback(u_minus_term)) {
    visit(u_minus_term->term);
  }

  if (term_post_callback) {
    term_post_callback(u_minus_term);
  }
}

void AstTraverser::visitMinus(Minus_ptr minus_term) {
  if (term_pre_callback and term_pre_callback(minus_term)) {
    visit(minus_term->left_term);
    visit(minus_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(minus_term);
  }
}

void AstTraverser::visitPlus(Plus_ptr plus_term) {
  if (term_pre_callback and term_pre_callback(plus_term)) {
    visit_term_list(plus_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(plus_term);
  }
}

void AstTraverser::visitTimes(Times_ptr times_term) {
  if (term_pre_callback and term_pre_callback(times_term)) {
    visit_term_list(times_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(times_term);
  }
}

void AstTraverser::visitEq(Eq_ptr eq_term) {
  if (term_pre_callback and term_pre_callback(eq_term)) {
    visit(eq_term->left_term);
    visit(eq_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(eq_term);
  }
}

void AstTraverser::visitNotEq(NotEq_ptr not_eq_term) {
  if (term_pre_callback and term_pre_callback(not_eq_term)) {
    visit(not_eq_term->left_term);
    visit(not_eq_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(not_eq_term);
  }
}

void AstTraverser::visitGt(Gt_ptr gt_term) {
  if (term_pre_callback and term_pre_callback(gt_term)) {
    visit(gt_term->left_term);
    visit(gt_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(gt_term);
  }
}

void AstTraverser::visitGe(Ge_ptr ge_term) {
  if (term_pre_callback and term_pre_callback(ge_term)) {
    visit(ge_term->left_term);
    visit(ge_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(ge_term);
  }
}

void AstTraverser::visitLt(Lt_ptr lt_term) {
  if (term_pre_callback and term_pre_callback(lt_term)) {
    visit(lt_term->left_term);
    visit(lt_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(lt_term);
  }
}

void AstTraverser::visitLe(Le_ptr le_term) {
  if (term_pre_callback and term_pre_callback(le_term)) {
    visit(le_term->left_term);
    visit(le_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(le_term);
  }
}

void AstTraverser::visitConcat(Concat_ptr concat_term) {
  if (term_pre_callback and term_pre_callback(concat_term)) {
    visit_term_list(concat_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(concat_term);
  }
}

void AstTraverser::visitIn(In_ptr in_term) {
  if (term_pre_callback and term_pre_callback(in_term)) {
    visit(in_term->left_term);
    visit(in_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(in_term);
  }
}

void AstTraverser::visitNotIn(NotIn_ptr not_in_term) {
  if (term_pre_callback and term_pre_callback(not_in_term)) {
    visit(not_in_term->left_term);
    visit(not_in_term->right_term);
  }

  if (term_post_callback) {
    term_post_callback(not_in_term);
  }
}

void AstTraverser::visitLen(Len_ptr len_term) {
  if (term_pre_callback and term_pre_callback(len_term)) {
    visit(len_term->term);
  }

  if (term_post_callback) {
    term_post_callback(len_term);
  }
}

void AstTraverser::visitContains(Contains_ptr contains_term) {
  if (term_pre_callback and term_pre_callback(contains_term)) {
    visit(contains_term->subject_term);
    visit(contains_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(contains_term);
  }
}

void AstTraverser::visitNotContains(NotContains_ptr not_contains_term) {
  if (term_pre_callback and term_pre_callback(not_contains_term)) {
    visit(not_contains_term->subject_term);
    visit(not_contains_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(not_contains_term);
  }
}

void AstTraverser::visitBegins(Begins_ptr begins_term) {
  if (term_pre_callback and term_pre_callback(begins_term)) {
    visit(begins_term->subject_term);
    visit(begins_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(begins_term);
  }
}

void AstTraverser::visitNotBegins(NotBegins_ptr not_begins_term) {
  if (term_pre_callback and term_pre_callback(not_begins_term)) {
    visit(not_begins_term->subject_term);
    visit(not_begins_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(not_begins_term);
  }
}

void AstTraverser::visitEnds(Ends_ptr ends_term) {
  if (term_pre_callback and term_pre_callback(ends_term)) {
    visit(ends_term->subject_term);
    visit(ends_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(ends_term);
  }
}

void AstTraverser::visitNotEnds(NotEnds_ptr not_ends_term) {
  if (term_pre_callback and term_pre_callback(not_ends_term)) {
    visit(not_ends_term->subject_term);
    visit(not_ends_term->search_term);
  }

  if (term_post_callback) {
    term_post_callback(not_ends_term);
  }
}

void AstTraverser::visitIndexOf(IndexOf_ptr index_of_term) {
  if (term_pre_callback and term_pre_callback(index_of_term)) {
    visit(index_of_term->subject_term);
    visit(index_of_term->search_term);
    if (index_of_term->from_index) {
      visit(index_of_term->from_index);
    }
  }

  if (term_post_callback) {
    term_post_callback(index_of_term);
  }
}

void AstTraverser::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  if (term_pre_callback and term_pre_callback(last_index_of_term)) {
    visit(last_index_of_term->subject_term);
    visit(last_index_of_term->search_term);
    if (last_index_of_term->from_index) {
      visit(last_index_of_term->from_index);
    }
  }

  if (term_post_callback) {
    term_post_callback(last_index_of_term);
  }
}

void AstTraverser::visitCharAt(CharAt_ptr char_at_term) {
  if (term_pre_callback and term_pre_callback(char_at_term)) {
    visit(char_at_term->subject_term);
    visit(char_at_term->index_term);
  }

  if (term_post_callback) {
    term_post_callback(char_at_term);
  }
}

void AstTraverser::visitSubString(SubString_ptr sub_string_term) {
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

void AstTraverser::visitToUpper(ToUpper_ptr to_upper_term) {
  if (term_pre_callback and term_pre_callback(to_upper_term)) {
    visit(to_upper_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(to_upper_term);
  }
}

void AstTraverser::visitToLower(ToLower_ptr to_lower_term) {
  if (term_pre_callback and term_pre_callback(to_lower_term)) {
    visit(to_lower_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(to_lower_term);
  }
}

void AstTraverser::visitTrim(Trim_ptr trim_term) {
  if (term_pre_callback and term_pre_callback(trim_term)) {
    visit(trim_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(trim_term);
  }
}

void AstTraverser::visitToString(ToString_ptr to_string_term) {
  if (term_pre_callback and term_pre_callback(to_string_term)) {
    visit(to_string_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(to_string_term);
  }
}

void AstTraverser::visitToInt(ToInt_ptr to_int_term) {
  if (term_pre_callback and term_pre_callback(to_int_term)) {
    visit(to_int_term->subject_term);
  }

  if (term_post_callback) {
    term_post_callback(to_int_term);
  }
}

void AstTraverser::visitReplace(Replace_ptr replace_term) {
  if (term_pre_callback and term_pre_callback(replace_term)) {
    visit(replace_term->subject_term);
    visit(replace_term->search_term);
    visit(replace_term->replace_term);
  }

  if (term_post_callback) {
    term_post_callback(replace_term);
  }
}

void AstTraverser::visitCount(Count_ptr count_term) {
  if (term_pre_callback and term_pre_callback(count_term)) {
    visit(count_term->subject_term);
    visit(count_term->bound_term);
  }

  if (term_post_callback) {
    term_post_callback(count_term);
  }
}

void AstTraverser::visitIte(Ite_ptr ite_term) {
  if (term_pre_callback and term_pre_callback(ite_term)) {
    visit(ite_term->cond);
    visit(ite_term->then_branch);
    visit(ite_term->else_branch);
  }

  if (term_post_callback) {
    term_post_callback(ite_term);
  }
}

void AstTraverser::visitReConcat(ReConcat_ptr re_concat_term) {
  if (term_pre_callback and term_pre_callback(re_concat_term)) {
    visit_term_list(re_concat_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(re_concat_term);
  }
}

void AstTraverser::visitToRegex(ToRegex_ptr to_regex_term) {
  if (term_pre_callback and term_pre_callback(to_regex_term)) {
    visit(to_regex_term->term);
  }

  if (term_post_callback) {
    term_post_callback(to_regex_term);
  }
}

void AstTraverser::visitUnknownTerm(Unknown_ptr unknown_term) {
  if (term_pre_callback and term_pre_callback(unknown_term)) {
    visit(unknown_term->term);
    visit_term_list(unknown_term->term_list);
  }

  if (term_post_callback) {
    term_post_callback(unknown_term);
  }
}

void AstTraverser::visitAsQualIdentifier(AsQualIdentifier_ptr as_qi_term) {
  if (term_pre_callback and term_pre_callback(as_qi_term)) {
    visit_children_of(as_qi_term);
  }

  if (term_post_callback) {
    term_post_callback(as_qi_term);
  }
}

void AstTraverser::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  if (term_pre_callback and term_pre_callback(qi_term)) {
    visit_children_of(qi_term);
  }

  if (term_post_callback) {
    term_post_callback(qi_term);
  }
}

void AstTraverser::visitTermConstant(TermConstant_ptr term_constant) {
  if (term_pre_callback and term_pre_callback(term_constant)) {
    visit_children_of(term_constant);
  }

  if (term_post_callback) {
    term_post_callback(term_constant);
  }
}

void AstTraverser::visitSort(Sort_ptr sort) {
   visit_children_of(sort);
}

void AstTraverser::visitTVariable(TVariable_ptr t_variable) {
  visit_children_of(t_variable);
}

void AstTraverser::visitTBool(TBool_ptr t_bool) {
  visit_children_of(t_bool);
}

void AstTraverser::visitTInt(TInt_ptr t_int) {
  visit_children_of(t_int);
}

void AstTraverser::visitTString(TString_ptr t_string) {
  visit_children_of(t_string);
}

void AstTraverser::visitAttribute(Attribute_ptr attribute) {
  visit_children_of(attribute);
}

void AstTraverser::visitSortedVar(SortedVar_ptr sorted_var) {
  visit_children_of(sorted_var);
}

void AstTraverser::visitVarBinding(VarBinding_ptr var_binding) {
  visit_children_of(var_binding);
}

void AstTraverser::visitIdentifier(Identifier_ptr identifier) {
  visit_children_of(identifier);
}

void AstTraverser::visitPrimitive(Primitive_ptr primitive) {
  visit_children_of(primitive);
}

void AstTraverser::visitVariable(Variable_ptr variable) {
  visit_children_of(variable);
}

void AstTraverser::push(Term_ptr* parent_pointer_to_term) {
  term_ptr_ref_stack_.push(parent_pointer_to_term);
}

void AstTraverser::pop() {
  term_ptr_ref_stack_.pop();
}

Term_ptr* AstTraverser::top() {
  if (term_ptr_ref_stack_.empty()) {
    return nullptr;
  }
  return term_ptr_ref_stack_.top();
}

void AstTraverser::visit(Term_ptr& term) {
  term_ptr_ref_stack_.push(&term);
  this->Visitor::visit(term);
  term_ptr_ref_stack_.pop();
}

void AstTraverser::visit_term_list(SMT::TermList_ptr term_list) {
  if (term_list == nullptr)
    return;
  for (auto& el : *term_list) {
    visit(el);
  }
}

} /* namespace Solver */
} /* namespace Vlab */

