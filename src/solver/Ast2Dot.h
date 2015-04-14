/*
 * Ast2Dot.h
 *
 *  Created on: Nov 23, 2014
 *      Author: baki
 */

#ifndef PARSER_AST2DOT_H_
#define PARSER_AST2DOT_H_

#include <iostream>
#include <stack>

#include "../smt/ast.h"

namespace Vlab {
namespace SMT {

class Ast2Dot : public Visitor {
public:
	Ast2Dot(std::ostream* out);

	~Ast2Dot();

	void finish();
	void add_edge(u_int64_t p, u_int64_t c);
	void add_node(u_int64_t c, std::string label);
	void draw(std::string label, Visitable_ptr p);
	void draw_terminal(std::string label);
	void visitPartial(Visitable_ptr);

	void visitScript(Script_ptr);
	void visitCommand(Command_ptr);
	void visitTerm(Term_ptr);
	void visitAnd(And_ptr);
	void visitNot(Not_ptr);
	void visitUMinus(UMinus_ptr);
	void visitMinus(Minus_ptr);
	void visitPlus(Plus_ptr);
	void visitEq(Eq_ptr);
	void visitGt(Gt_ptr);
	void visitGe(Ge_ptr);
	void visitLt(Lt_ptr);
	void visitLe(Le_ptr);
	void visitIte(Ite_ptr);
	void visitReConcat(ReConcat_ptr);
	void visitReOr(ReOr_ptr);
	void visitConcat(Concat_ptr);
	void visitIn(In_ptr);
	void visitLen(Len_ptr);
	void visitToRegex(ToRegex_ptr);
	void visitUnknownTerm(Unknown_ptr);
	void visitAsQualIdentifier(AsQualIdentifier_ptr);
	void visitQualIdentifier(QualIdentifier_ptr);
	void visitTermConstant(TermConstant_ptr);
	void visitSort(Sort_ptr);
	void visitVarType(VarType_ptr);
	void visitTBool(TBool_ptr);
	void visitTInt(TInt_ptr);
	void visitTString(TString_ptr);
	void visitAttribute(Attribute_ptr);
	void visitSortedVar(SortedVar_ptr);
	void visitVarBinding(VarBinding_ptr);
	void visitIdentifier(Identifier_ptr);
	void visitPrimitive(Primitive_ptr);
	void visitVariable(Variable_ptr);
	void exception(std::string);

private:
	std::ostream* m_out; //file for writting output
	u_int64_t count; //used to give each node a uniq id
	std::stack<u_int64_t> s; //stack for tracking parent/child pairs

};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* PARSER_AST2DOT_H_ */
