/*
 * FormulaOptimizer.cpp
 *
 *  Created on: May 12, 2015
 *      Author: baki
 */

#include "FormulaOptimizer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int FormulaOptimizer::VLOG_LEVEL = 14;

FormulaOptimizer::FormulaOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table) {
}

FormulaOptimizer::~FormulaOptimizer() {
}

void FormulaOptimizer::start() {

  push_scope(root);
  visit(root);
  pop_scope();

  end();
}

void FormulaOptimizer::end() {
  SyntacticOptimizer syntactic_optimizer(root, symbol_table);
  syntactic_optimizer.start();
}

void FormulaOptimizer::visitScript(Script_ptr script) {
  for (auto& command : *(script->command_list)) {
    if (Command::Type::ASSERT == command->getType()) {
      Assert_ptr assert_command = dynamic_cast<Assert_ptr>(command);
      add_term_to_check_list(assert_command->term);
    }
  }
  visit_children_of(script);
}

void FormulaOptimizer::visitCommand(Command_ptr command) {

  switch (command->getType()) {
  case Command::Type::ASSERT: {
    Assert_ptr assert_command = dynamic_cast<Assert_ptr>(command);
    visit_and_callback(assert_command->term);
    break;
  }
  default:
    LOG(FATAL)<< "'" << *command<< "' is not expected.";
    break;
  }
}

void FormulaOptimizer::visitTerm(Term_ptr term) {
}

void FormulaOptimizer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void FormulaOptimizer::visitExists(Exists_ptr exists_term) {
}

void FormulaOptimizer::visitForAll(ForAll_ptr for_all_term) {
}

void FormulaOptimizer::visitLet(Let_ptr let_term) {
}

void FormulaOptimizer::visitAnd(And_ptr and_term) {
  bool remove_and_term = false;
  for (auto& term : *(and_term->term_list)) {
    if (check_term(term)) {
      remove_and_term = true;
      break;
    }
  }

  if (remove_and_term) {
    DVLOG(VLOG_LEVEL) << "replace: 'and' with constant 'false'";
    auto callback = [and_term](Term_ptr& term) mutable {
      term = new TermConstant(new Primitive("false", Primitive::Type::BOOL));
      delete and_term;
    };
    callbacks.push(callback);
  } else {
    add_terms_to_check_list(and_term->term_list);
    for (auto& term : *(and_term->term_list)) {
      visit_and_callback(term);
    }
  }
}

void FormulaOptimizer::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    push_scope(term);
    visit_and_callback(term);
    pop_scope();
  }
}

void FormulaOptimizer::visitNot(Not_ptr not_term) {
  visit_and_callback(not_term->term);
}

void FormulaOptimizer::visitUMinus(UMinus_ptr u_minus_term) {
  visit_and_callback(u_minus_term->term);
}

void FormulaOptimizer::visitMinus(Minus_ptr minus_term) {
  visit_and_callback(minus_term->left_term);
  visit_and_callback(minus_term->right_term);
}

void FormulaOptimizer::visitPlus(Plus_ptr plus_term) {
  visit_and_callback(plus_term->left_term);
  visit_and_callback(plus_term->right_term);
}

void FormulaOptimizer::visitEq(Eq_ptr eq_term) {
  visit_and_callback(eq_term->left_term);
  visit_and_callback(eq_term->right_term);
}

void FormulaOptimizer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_and_callback(not_eq_term->left_term);
  visit_and_callback(not_eq_term->right_term);
}

void FormulaOptimizer::visitGt(Gt_ptr gt_term) {
  visit_and_callback(gt_term->left_term);
  visit_and_callback(gt_term->right_term);
}

void FormulaOptimizer::visitGe(Ge_ptr ge_term) {
  visit_and_callback(ge_term->left_term);
  visit_and_callback(ge_term->right_term);
}

void FormulaOptimizer::visitLt(Lt_ptr lt_term) {
  visit_and_callback(lt_term->left_term);
  visit_and_callback(lt_term->right_term);
}

void FormulaOptimizer::visitLe(Le_ptr le_term) {
  visit_and_callback(le_term->left_term);
  visit_and_callback(le_term->right_term);
}

void FormulaOptimizer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : *(concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }
}

void FormulaOptimizer::visitIn(In_ptr in_term) {
  visit_and_callback(in_term->left_term);
  visit_and_callback(in_term->right_term);
}

void FormulaOptimizer::visitNotIn(NotIn_ptr not_in_term) {
  visit_and_callback(not_in_term->left_term);
  visit_and_callback(not_in_term->right_term);
}

void FormulaOptimizer::visitLen(Len_ptr len_term) {
  visit_and_callback(len_term->term);
}

void FormulaOptimizer::visitContains(Contains_ptr contains_term) {
  visit_and_callback(contains_term->subject_term);
  visit_and_callback(contains_term->search_term);
}

void FormulaOptimizer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_and_callback(not_contains_term->subject_term);
  visit_and_callback(not_contains_term->search_term);
}

void FormulaOptimizer::visitBegins(Begins_ptr begins_term) {
  visit_and_callback(begins_term->subject_term);
  visit_and_callback(begins_term->search_term);
}

void FormulaOptimizer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_and_callback(not_begins_term->subject_term);
  visit_and_callback(not_begins_term->search_term);
}

void FormulaOptimizer::visitEnds(Ends_ptr ends_term) {
  visit_and_callback(ends_term->subject_term);
  visit_and_callback(ends_term->search_term);
}

void FormulaOptimizer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_and_callback(not_ends_term->subject_term);
  visit_and_callback(not_ends_term->search_term);
}

void FormulaOptimizer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_and_callback(index_of_term->subject_term);
  visit_and_callback(index_of_term->search_term);
}

void FormulaOptimizer::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visit_and_callback(last_index_of_term->subject_term);
  visit_and_callback(last_index_of_term->search_term);
}

void FormulaOptimizer::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visit_and_callback(char_at_term->subject_term);
  visit_and_callback(char_at_term->index_term);
}

void FormulaOptimizer::visitSubString(SMT::SubString_ptr sub_string_term) {
  visit_and_callback(sub_string_term->subject_term);
  visit_and_callback(sub_string_term->start_index_term);
}

void FormulaOptimizer::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visit_and_callback(to_upper_term->subject_term);
}

void FormulaOptimizer::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visit_and_callback(to_lower_term->subject_term);
}

void FormulaOptimizer::visitTrim(SMT::Trim_ptr trim_term) {
  visit_and_callback(trim_term->subject_term);
}

void FormulaOptimizer::visitReplace(Replace_ptr replace_term) {
  visit_and_callback(replace_term->subject_term);
  visit_and_callback(replace_term->search_term);
  visit_and_callback(replace_term->replace_term);
}

void FormulaOptimizer::visitCount(Count_ptr count_term) {
  visit_and_callback(count_term->subject_term);
  visit_and_callback(count_term->bound_term);
}

void FormulaOptimizer::visitIte(Ite_ptr ite_term) {
}

void FormulaOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void FormulaOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void FormulaOptimizer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void FormulaOptimizer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void FormulaOptimizer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void FormulaOptimizer::visitTermConstant(TermConstant_ptr term_constant) {
}

void FormulaOptimizer::visitIdentifier(Identifier_ptr identifier) {
}

void FormulaOptimizer::visitPrimitive(Primitive_ptr primitive) {
}

void FormulaOptimizer::visitTVariable(TVariable_ptr t_variable) {
}

void FormulaOptimizer::visitTBool(TBool_ptr t_bool) {
}

void FormulaOptimizer::visitTInt(TInt_ptr t_int) {
}

void FormulaOptimizer::visitTString(TString_ptr t_string) {
}

void FormulaOptimizer::visitVariable(Variable_ptr variable) {
}

void FormulaOptimizer::visitSort(Sort_ptr sort) {
}

void FormulaOptimizer::visitAttribute(Attribute_ptr attribute) {
}

void FormulaOptimizer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void FormulaOptimizer::visitVarBinding(VarBinding_ptr var_binding) {
}

void FormulaOptimizer::push_scope(Visitable_ptr key) {
  scope_stack.push_back(key);
}

Visitable_ptr FormulaOptimizer::pop_scope() {
  Visitable_ptr scope = scope_stack.back();
  auto it = check_table.find(scope);
  check_table.erase(it);
  scope_stack.pop_back();
  return scope;
}

void FormulaOptimizer::add_term_to_check_list(Term_ptr term) {
  check_table[scope_stack.back()].push_back(term);
}
void FormulaOptimizer::add_terms_to_check_list(TermList_ptr term_list) {
  check_table[scope_stack.back()].insert(check_table[scope_stack.back()].end(), term_list->begin(), term_list->end());
}

bool FormulaOptimizer::check_term(Term_ptr term) {
  for (auto& scope : scope_stack) {
    for (auto& other_term : check_table[scope]) {
      if (term->getType() == Term::Type::NOT and other_term->getType() != Term::Type::NOT) {
        Not_ptr not_term = dynamic_cast<Not_ptr>(term);
        if (is_equivalent(not_term->term, other_term)) {
          return true;
        }
      } else if (term->getType() != Term::Type::NOT and other_term->getType() == Term::Type::NOT) {
        Not_ptr not_term = dynamic_cast<Not_ptr>(other_term);
        if (is_equivalent(not_term->term, term)) {
          return true;
        }
      }
    }
  }
  return false;
}

void FormulaOptimizer::visit_and_callback(Term_ptr& term) {
  visit(term);
  while (not callbacks.empty()) {
    callbacks.front()(term);
    callbacks.pop();

  }
}

bool FormulaOptimizer::is_equivalent(Term_ptr x, Term_ptr y) {
  if (x == y) {
    return true;
  }
  return (to_string(x) == to_string(y));
}

std::string FormulaOptimizer::to_string(Visitable_ptr visitable) {
  std::stringstream ss;
  Ast2Dot ast2dot(&ss);
  ast2dot.start(visitable);
  return ss.str();
}

} /* namespace Solver */
} /* namespace Vlab */
