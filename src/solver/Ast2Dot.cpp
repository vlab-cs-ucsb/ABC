/*
 * Ast2Dot.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: baki
 */

#include "Ast2Dot.h"

namespace Vlab { namespace SMT {

Ast2Dot::Ast2Dot(std::ostream* out) : m_out (out) {
	count = 0;
	*m_out << "digraph G { " << std::endl;
}

Ast2Dot::~Ast2Dot() {}

void Ast2Dot::finish() {
	*m_out << "}" << std::endl;
}

void Ast2Dot::add_edge(u_int64_t p, u_int64_t c) {
	 *m_out << "\"" << p << "\" -> \"" << c << "\";" << std::endl;

}

void Ast2Dot::add_node(u_int64_t c, std::string label) {
	*m_out << "\"" << c << "\" [label=\""<< label << "\"];" << std::endl;
}

void Ast2Dot::draw(std::string label, Visitable_ptr p) {
    count++;
    add_node( count, label );
    add_edge( s.top(), count );
    s.push(count);
    if (p != nullptr) {
    	visit_children_of(p);
    }
    s.pop();

}

void Ast2Dot::draw_terminal(std::string label) {
    count++;
	*m_out << "\""<< count << "\" [label=\"" << label << "\"];" << std::endl;
    add_edge( s.top(), count );
}

/* visit starting any node */
void Ast2Dot::visitPartial(Visitable_ptr v) {
	if (count != 0) {
		count = 0;
		*m_out << "digraph G { " << std::endl;
	}
	add_node( count, "Partial");
	s.push(count);
	visit(v);
	s.pop();
	finish();
}

/* root node */
void Ast2Dot::visitScript(Script_ptr script) {
    add_node( count, "Script" );
	s.push(count);
    if (script != nullptr) {
    	visit_children_of(script);
    }
    s.pop();
}

void Ast2Dot::visitCommand(Command_ptr command) { draw(command->str(), command); }

void Ast2Dot::visitTerm(Term_ptr term) { draw(term->str(), term); }

void Ast2Dot::visitSort(Sort_ptr sort) { draw("Sort", sort); }

void Ast2Dot::visitAttribute(Attribute_ptr attribute) { draw("Attribute", attribute); }

void Ast2Dot::visitSortedVar(SortedVar_ptr sorted_var) { draw("SortedVar", sorted_var); }

void Ast2Dot::visitVarBinding(VarBinding_ptr var_binding) { draw("VarBinding", var_binding); }

void Ast2Dot::visitIdentifier(Identifier_ptr identifier) { draw("Identifier", identifier); }

void Ast2Dot::visitAnd(And_ptr and_term) { visitTerm(and_term); }

void Ast2Dot::visitNot(Not_ptr not_term) { visitTerm(not_term); }

void Ast2Dot::visitUMinus(UMinus_ptr u_minus_term) { visitTerm(u_minus_term); }

void Ast2Dot::visitMinus(Minus_ptr minus_term) { visitTerm(minus_term); }

void Ast2Dot::visitPlus(Plus_ptr plus_term) { visitTerm(plus_term); }

void Ast2Dot::visitEq(Eq_ptr eq_term) { visitTerm(eq_term); }

void Ast2Dot::visitGt(Gt_ptr gt_term) { visitTerm(gt_term); }

void Ast2Dot::visitGe(Ge_ptr ge_term) { visitTerm(ge_term); }

void Ast2Dot::visitLt(Lt_ptr lt_term) { visitTerm(lt_term); }

void Ast2Dot::visitLe(Le_ptr le_term) { visitTerm(le_term); }

void Ast2Dot::visitIte(Ite_ptr ite_term) { visitTerm(ite_term); }

void Ast2Dot::visitReConcat(ReConcat_ptr re_concat_term) { visitTerm(re_concat_term); }

void Ast2Dot::visitReOr(ReOr_ptr re_or_term) { visitTerm(re_or_term); }

void Ast2Dot::visitConcat(Concat_ptr concat_term) { visitTerm(concat_term); }

void Ast2Dot::visitIn(In_ptr in_term) { visitTerm(in_term); }

void Ast2Dot::visitLen(Len_ptr len_term) { visitTerm(len_term); }

void Ast2Dot::visitToRegex(ToRegex_ptr to_regex_term) { visitTerm(to_regex_term); }

void Ast2Dot::visitUnknownTerm(Unknown_ptr unknown_term) { visitTerm(unknown_term); }

void Ast2Dot::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { visitTerm(as_qid_term); }

void Ast2Dot::visitQualIdentifier(QualIdentifier_ptr qi_term) { visitTerm(qi_term); }

void Ast2Dot::visitTermConstant(TermConstant_ptr term_constant) { visitTerm(term_constant); }

void Ast2Dot::visitVarType(VarType_ptr t_var) { draw_terminal(t_var->str()); }

void Ast2Dot::visitTBool(TBool_ptr t_bool) { draw_terminal(t_bool->str()); }

void Ast2Dot::visitTInt(TInt_ptr t_int) { draw_terminal(t_int->str()); }

void Ast2Dot::visitTString(TString_ptr t_string) { draw_terminal(t_string->str()); }

void Ast2Dot::visitPrimitive(Primitive_ptr primitive) {	draw_terminal(primitive->str()); }

void Ast2Dot::visitVariable(Variable_ptr var) { draw("Variable",var); }

void Ast2Dot::exception(std::string what) { }

} /* namespace SMT */
} /* namespace Vlab */


