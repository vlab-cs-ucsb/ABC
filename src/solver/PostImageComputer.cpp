/*
 * PostImageComputer.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "PostImageComputer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int PostImageComputer::VLOG_LEVEL = 11;

PostImageComputer::PostImageComputer(Script_ptr script, SymbolTable_ptr symbol_table)
: root (script), symbol_table (symbol_table) { }

PostImageComputer::~PostImageComputer() { }

void PostImageComputer::start() {

  visit(root);
  end();
}

void PostImageComputer::end() { }

void PostImageComputer::visitScript(Script_ptr script) {
  symbol_table -> push_scope(script);
  visit_children_of(script);
  symbol_table -> pop_scope();
}

void PostImageComputer::visitCommand(Command_ptr command) { }

void PostImageComputer::visitTerm(Term_ptr term) { }

void PostImageComputer::visitExclamation(Exclamation_ptr exclamation_term) { }

void PostImageComputer::visitExists(Exists_ptr exists_term) { }

void PostImageComputer::visitForAll(ForAll_ptr for_all_term) { }

void PostImageComputer::visitLet(Let_ptr let_term) { }

void PostImageComputer::visitAnd(And_ptr and_term) { }

void PostImageComputer::visitOr(Or_ptr or_term) { }

void PostImageComputer::visitNot(Not_ptr not_term) { visit_children_of(not_term); }

void PostImageComputer::visitUMinus(UMinus_ptr u_minus_term) { visit_children_of(u_minus_term); }

void PostImageComputer::visitMinus(Minus_ptr minus_term) { visit_children_of(minus_term); }

void PostImageComputer::visitPlus(Plus_ptr plus_term) { visit_children_of(plus_term); }

void PostImageComputer::visitEq(Eq_ptr eq_term) { visit_children_of(eq_term); }

void PostImageComputer::visitGt(Gt_ptr gt_term) { visit_children_of(gt_term); }

void PostImageComputer::visitGe(Ge_ptr ge_term) { visit_children_of(ge_term); }

void PostImageComputer::visitLt(Lt_ptr lt_term) {	visit_children_of(lt_term); }

void PostImageComputer::visitLe(Le_ptr le_term) {	visit_children_of(le_term); }

void PostImageComputer::visitConcat(Concat_ptr concat_term) { visit_children_of(concat_term); }

void PostImageComputer::visitIn(In_ptr in_term) {	visit_children_of(in_term); }

void PostImageComputer::visitLen(Len_ptr len_term) { visit_children_of(len_term); }

void PostImageComputer::visitContains(Contains_ptr contains_term) { visit_children_of(contains_term); }

void PostImageComputer::visitBegins(Begins_ptr begins_term) { visit_children_of(begins_term); }

void PostImageComputer::visitEnds(Ends_ptr ends_term) { visit_children_of(ends_term); }

void PostImageComputer::visitIndexOf(IndexOf_ptr index_of_term) {	visit_children_of(index_of_term); }

void PostImageComputer::visitReplace(Replace_ptr replace_term) { visit_children_of(replace_term); }

void PostImageComputer::visitCount(Count_ptr count_term) { visit_children_of(count_term); }

void PostImageComputer::visitIte(Ite_ptr ite_term) { }

void PostImageComputer::visitReConcat(ReConcat_ptr re_concat_term) { }

void PostImageComputer::visitToRegex(ToRegex_ptr to_regex_term) { }

void PostImageComputer::visitUnknownTerm(Unknown_ptr unknown_term) { }

void PostImageComputer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void PostImageComputer::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void PostImageComputer::visitTermConstant(TermConstant_ptr term_constant) { }

void PostImageComputer::visitIdentifier(Identifier_ptr identifier) { }

void PostImageComputer::visitPrimitive(Primitive_ptr primitive) { }

void PostImageComputer::visitTVariable(TVariable_ptr t_variable) { }

void PostImageComputer::visitTBool(TBool_ptr t_bool) { }

void PostImageComputer::visitTInt(TInt_ptr t_int) { }

void PostImageComputer::visitTString(TString_ptr t_string) { }

void PostImageComputer::visitVariable(Variable_ptr variable) { }

void PostImageComputer::visitSort(Sort_ptr sort) { }

void PostImageComputer::visitAttribute(Attribute_ptr attribute) {  }

void PostImageComputer::visitSortedVar(SortedVar_ptr sorted_var) { }

void PostImageComputer::visitVarBinding(VarBinding_ptr var_binding) {  }

} /* namespace Solver */
} /* namespace Vlab */
