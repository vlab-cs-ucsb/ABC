/*
 * PreImageComputer.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "PreImageComputer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int PreImageComputer::VLOG_LEVEL = 12;

PreImageComputer::PreImageComputer(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table) { }

PreImageComputer::~PreImageComputer() { }

void PreImageComputer::start() {

	visit(root);
	end();
}

void PreImageComputer::end() { }

void PreImageComputer::visitScript(Script_ptr script) { }

void PreImageComputer::visitCommand(Command_ptr command) { }

void PreImageComputer::visitTerm(Term_ptr term) { }

void PreImageComputer::visitExclamation(Exclamation_ptr exclamation_term) { }

void PreImageComputer::visitExists(Exists_ptr exists_term) { }

void PreImageComputer::visitForAll(ForAll_ptr for_all_term) { }

void PreImageComputer::visitLet(Let_ptr let_term) { }

void PreImageComputer::visitAnd(And_ptr and_term) { }

void PreImageComputer::visitOr(Or_ptr or_term) { }

void PreImageComputer::visitNot(Not_ptr not_term) { visit_children_of(not_term); }

void PreImageComputer::visitUMinus(UMinus_ptr u_minus_term) { visit_children_of(u_minus_term); }

void PreImageComputer::visitMinus(Minus_ptr minus_term) { visit_children_of(minus_term); }

void PreImageComputer::visitPlus(Plus_ptr plus_term) { visit_children_of(plus_term); }

void PreImageComputer::visitEq(Eq_ptr eq_term) { visit_children_of(eq_term); }

void PreImageComputer::visitGt(Gt_ptr gt_term) { visit_children_of(gt_term); }

void PreImageComputer::visitGe(Ge_ptr ge_term) { visit_children_of(ge_term); }

void PreImageComputer::visitLt(Lt_ptr lt_term) {	visit_children_of(lt_term); }

void PreImageComputer::visitLe(Le_ptr le_term) {	visit_children_of(le_term); }

void PreImageComputer::visitConcat(Concat_ptr concat_term) { visit_children_of(concat_term); }

void PreImageComputer::visitIn(In_ptr in_term) {	visit_children_of(in_term); }

void PreImageComputer::visitLen(Len_ptr len_term) { visit_children_of(len_term); }

void PreImageComputer::visitContains(Contains_ptr contains_term) { visit_children_of(contains_term); }

void PreImageComputer::visitBegins(Begins_ptr begins_term) { visit_children_of(begins_term); }

void PreImageComputer::visitEnds(Ends_ptr ends_term) { visit_children_of(ends_term); }

void PreImageComputer::visitIndexOf(IndexOf_ptr index_of_term) {	visit_children_of(index_of_term); }

void PreImageComputer::visitReplace(Replace_ptr replace_term) { visit_children_of(replace_term); }

void PreImageComputer::visitCount(Count_ptr count_term) { visit_children_of(count_term); }

void PreImageComputer::visitIte(Ite_ptr ite_term) { }

void PreImageComputer::visitReConcat(ReConcat_ptr re_concat_term) { }

void PreImageComputer::visitToRegex(ToRegex_ptr to_regex_term) { }

void PreImageComputer::visitUnknownTerm(Unknown_ptr unknown_term) { }

void PreImageComputer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void PreImageComputer::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void PreImageComputer::visitTermConstant(TermConstant_ptr term_constant) { }

void PreImageComputer::visitIdentifier(Identifier_ptr identifier) { }

void PreImageComputer::visitPrimitive(Primitive_ptr primitive) { }

void PreImageComputer::visitTVariable(TVariable_ptr t_variable) { }

void PreImageComputer::visitTBool(TBool_ptr t_bool) { }

void PreImageComputer::visitTInt(TInt_ptr t_int) { }

void PreImageComputer::visitTString(TString_ptr t_string) { }

void PreImageComputer::visitVariable(Variable_ptr variable) { }

void PreImageComputer::visitSort(Sort_ptr sort) { }

void PreImageComputer::visitAttribute(Attribute_ptr attribute) {  }

void PreImageComputer::visitSortedVar(SortedVar_ptr sorted_var) { }

void PreImageComputer::visitVarBinding(VarBinding_ptr var_binding) {  }

} /* namespace Solver */
} /* namespace Vlab */
