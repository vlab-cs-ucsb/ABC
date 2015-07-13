/*
 * OptimizationRuleRunner.cpp
 *
 *  Created on: May 6, 2015
 *      Author: baki
 */

#include "OptimizationRuleRunner.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int OptimizationRuleRunner::VLOG_LEVEL = 16;

OptimizationRuleRunner::OptimizationRuleRunner(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table) {
}

OptimizationRuleRunner::~OptimizationRuleRunner() {
}

void OptimizationRuleRunner::start() {

  if (not has_optimization_rules()) {
    return;
  }

  symbol_table->push_scope(root);
  visit(root);
  symbol_table->pop_scope();

  end();

}

void OptimizationRuleRunner::end() {
  SyntacticOptimizer syntactic_optimizer(root, symbol_table);
  syntactic_optimizer.start();
}

void OptimizationRuleRunner::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void OptimizationRuleRunner::visitCommand(Command_ptr command) {

  switch (command->getType()) {
  case Command::Type::ASSERT: {
    Assert_ptr assert_command = dynamic_cast<Assert_ptr>(command);
    check_and_substitute_var(assert_command->term);
    visit_children_of(assert_command);
    break;
  }
  default:
    LOG(FATAL)<< "'" << *command<< "' is not expected.";
    break;
  }
}

void OptimizationRuleRunner::visitTerm(Term_ptr term) {
}

void OptimizationRuleRunner::visitExclamation(Exclamation_ptr exclamation_term) {
}

void OptimizationRuleRunner::visitExists(Exists_ptr exists_term) {
}

void OptimizationRuleRunner::visitForAll(ForAll_ptr for_all_term) {
}

void OptimizationRuleRunner::visitLet(Let_ptr let_term) {
}

void OptimizationRuleRunner::visitAnd(And_ptr and_term) {
  for (auto& term : *(and_term->term_list)) {
    check_and_substitute_var(term);
    visit(term);
  }
}

void OptimizationRuleRunner::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    check_and_substitute_var(term);
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void OptimizationRuleRunner::visitNot(Not_ptr not_term) {
  check_and_substitute_var(not_term->term);
  visit_children_of(not_term);
}

void OptimizationRuleRunner::visitUMinus(UMinus_ptr u_minus_term) {
  check_and_substitute_var(u_minus_term->term);
  visit_children_of(u_minus_term);
}

void OptimizationRuleRunner::visitMinus(Minus_ptr minus_term) {
  check_and_substitute_var(minus_term->left_term);
  check_and_substitute_var(minus_term->right_term);
  visit_children_of(minus_term);
}

void OptimizationRuleRunner::visitPlus(Plus_ptr plus_term) {
  check_and_substitute_var(plus_term->left_term);
  check_and_substitute_var(plus_term->right_term);
  visit_children_of(plus_term);
}

void OptimizationRuleRunner::visitEq(Eq_ptr eq_term) {
  check_and_substitute_var(eq_term->left_term);
  check_and_substitute_var(eq_term->right_term);
  visit_children_of(eq_term);
}

void OptimizationRuleRunner::visitGt(Gt_ptr gt_term) {
  check_and_substitute_var(gt_term->left_term);
  check_and_substitute_var(gt_term->right_term);
  visit_children_of(gt_term);
}

void OptimizationRuleRunner::visitGe(Ge_ptr ge_term) {
  check_and_substitute_var(ge_term->left_term);
  check_and_substitute_var(ge_term->right_term);
  visit_children_of(ge_term);
}

void OptimizationRuleRunner::visitLt(Lt_ptr lt_term) {
  check_and_substitute_var(lt_term->left_term);
  check_and_substitute_var(lt_term->right_term);
  visit_children_of(lt_term);
}

void OptimizationRuleRunner::visitLe(Le_ptr le_term) {
  check_and_substitute_var(le_term->left_term);
  check_and_substitute_var(le_term->right_term);
  visit_children_of(le_term);
}

void OptimizationRuleRunner::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : *(concat_term->term_list)) {
    check_and_substitute_var(term_ptr);
    visit(term_ptr);
  }
}

void OptimizationRuleRunner::visitIn(In_ptr in_term) {
  check_and_substitute_var(in_term->left_term);
  check_and_substitute_var(in_term->right_term);
  visit_children_of(in_term);
}

void OptimizationRuleRunner::visitLen(Len_ptr len_term) {
  check_and_substitute_var(len_term->term);
  visit_children_of(len_term);
}

void OptimizationRuleRunner::visitContains(Contains_ptr contains_term) {
  check_and_substitute_var(contains_term->subject_term);
  check_and_substitute_var(contains_term->search_term);
  visit_children_of(contains_term);
}

void OptimizationRuleRunner::visitBegins(Begins_ptr begins_term) {
  check_and_substitute_var(begins_term->subject_term);
  check_and_substitute_var(begins_term->search_term);
  visit_children_of(begins_term);
}

void OptimizationRuleRunner::visitEnds(Ends_ptr ends_term) {
  check_and_substitute_var(ends_term->subject_term);
  check_and_substitute_var(ends_term->search_term);
  visit_children_of(ends_term);
}

void OptimizationRuleRunner::visitIndexOf(IndexOf_ptr index_of_term) {
  check_and_substitute_var(index_of_term->subject_term);
  check_and_substitute_var(index_of_term->search_term);
  visit_children_of(index_of_term);
}

void OptimizationRuleRunner::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  check_and_substitute_var(last_index_of_term->subject_term);
  check_and_substitute_var(last_index_of_term->search_term);
  visit_children_of(last_index_of_term);
}

void OptimizationRuleRunner::visitCharAt(SMT::CharAt_ptr char_at_term) {
  check_and_substitute_var(char_at_term->subject_term);
  check_and_substitute_var(char_at_term->index_term);
  visit_children_of(char_at_term);
}

void OptimizationRuleRunner::visitSubString(SMT::SubString_ptr sub_string_term) {
  check_and_substitute_var(sub_string_term->subject_term);
  check_and_substitute_var(sub_string_term->start_index_term);
  visit_children_of(sub_string_term);
}

void OptimizationRuleRunner::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  check_and_substitute_var(to_upper_term->subject_term);
  visit_children_of(to_upper_term);
}

void OptimizationRuleRunner::visitToLower(SMT::ToLower_ptr to_lower_term) {
  check_and_substitute_var(to_lower_term->subject_term);
  visit_children_of(to_lower_term);
}

void OptimizationRuleRunner::visitTrim(SMT::Trim_ptr trim_term) {
  check_and_substitute_var(trim_term->subject_term);
  visit_children_of(trim_term);
}

void OptimizationRuleRunner::visitReplace(Replace_ptr replace_term) {
  check_and_substitute_var(replace_term->subject_term);
  check_and_substitute_var(replace_term->search_term);
  check_and_substitute_var(replace_term->replace_term);
  visit_children_of(replace_term);

}

void OptimizationRuleRunner::visitCount(Count_ptr count_term) {
  check_and_substitute_var(count_term->subject_term);
  check_and_substitute_var(count_term->bound_term);
  visit_children_of(count_term);
}

void OptimizationRuleRunner::visitIte(Ite_ptr ite_term) {
}

void OptimizationRuleRunner::visitReConcat(ReConcat_ptr re_concat_term) {
}

void OptimizationRuleRunner::visitToRegex(ToRegex_ptr to_regex_term) {
}

void OptimizationRuleRunner::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void OptimizationRuleRunner::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void OptimizationRuleRunner::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void OptimizationRuleRunner::visitTermConstant(TermConstant_ptr term_constant) {
}

void OptimizationRuleRunner::visitIdentifier(Identifier_ptr identifier) {
}

void OptimizationRuleRunner::visitPrimitive(Primitive_ptr primitive) {
}

void OptimizationRuleRunner::visitTVariable(TVariable_ptr t_variable) {
}

void OptimizationRuleRunner::visitTBool(TBool_ptr t_bool) {
}

void OptimizationRuleRunner::visitTInt(TInt_ptr t_int) {
}

void OptimizationRuleRunner::visitTString(TString_ptr t_string) {
}

void OptimizationRuleRunner::visitVariable(Variable_ptr variable) {
}

void OptimizationRuleRunner::visitSort(Sort_ptr sort) {
}

void OptimizationRuleRunner::visitAttribute(Attribute_ptr attribute) {
}

void OptimizationRuleRunner::visitSortedVar(SortedVar_ptr sorted_var) {
}

void OptimizationRuleRunner::visitVarBinding(VarBinding_ptr var_binding) {
}

bool OptimizationRuleRunner::has_optimization_rules() {
  for (auto& pair : symbol_table->get_variable_substitution_table()) {
    if (not pair.second.empty()) {
      return true;
    }
  }
  return false;
}

bool OptimizationRuleRunner::check_and_substitute_var(Term_ptr& term) {
  if (Term::Type::QUALIDENTIFIER == term->getType()) {
    Variable_ptr variable = symbol_table->getVariable(term);
    Term_ptr subs_term = symbol_table->get_variable_substitution_term(variable);
    if (subs_term != nullptr) {
      DVLOG(VLOG_LEVEL) << "apply rule: " << *variable << " (" << variable << ") -> " << *subs_term << " ("
                                 << subs_term << " )";
      Term_ptr tmp_term = term;
      term = subs_term->clone();
      delete tmp_term;
    }
  }
  return false;
}

} /* namespace Solver */
} /* namespace Vlab */
