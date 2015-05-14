/*
 * FormulaOptimizer.h
 *
 *  Created on: May 12, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_FORMULAOPTIMIZER_H_
#define SRC_SOLVER_FORMULAOPTIMIZER_H_

#include <sstream>
#include <queue>
#include <vector>
#include <map>
#include <functional>

#include <glog/logging.h>
#include "../smt/ast.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"
#include "SyntacticOptimizer.h"

namespace Vlab {
namespace SMT {

class FormulaOptimizer: public Visitor {
public:
	FormulaOptimizer(Script_ptr, SymbolTable_ptr);
	virtual ~FormulaOptimizer();
	void start();
	void end();

	void visitScript(Script_ptr);
	void visitCommand(Command_ptr);
	void visitTerm(Term_ptr);
	void visitExclamation(Exclamation_ptr);
	void visitExists(Exists_ptr);
	void visitForAll(ForAll_ptr);
	void visitLet(Let_ptr);
	void visitAnd(And_ptr);
	void visitOr(Or_ptr);
	void visitNot(Not_ptr);
	void visitUMinus(UMinus_ptr);
	void visitMinus(Minus_ptr);
	void visitPlus(Plus_ptr);
	void visitEq(Eq_ptr);
	void visitGt(Gt_ptr);
	void visitGe(Ge_ptr);
	void visitLt(Lt_ptr);
	void visitLe(Le_ptr);
	void visitConcat(Concat_ptr);
	void visitIn(In_ptr);
	void visitLen(Len_ptr);
	void visitContains(Contains_ptr);
	void visitBegins(Begins_ptr);
	void visitEnds(Ends_ptr);
	void visitIndexOf(IndexOf_ptr);
	void visitReplace(Replace_ptr);
	void visitCount(Count_ptr);
	void visitIte(Ite_ptr);
	void visitReConcat(ReConcat_ptr);
	void visitToRegex(ToRegex_ptr);
	void visitUnknownTerm(Unknown_ptr);
	void visitAsQualIdentifier(AsQualIdentifier_ptr);
	void visitQualIdentifier(QualIdentifier_ptr);
	void visitTermConstant(TermConstant_ptr);
	void visitSort(Sort_ptr);
	void visitTVariable(TVariable_ptr);
	void visitTBool(TBool_ptr);
	void visitTInt(TInt_ptr);
	void visitTString(TString_ptr);
	void visitAttribute(Attribute_ptr);
	void visitSortedVar(SortedVar_ptr);
	void visitVarBinding(VarBinding_ptr);
	void visitIdentifier(Identifier_ptr);
	void visitPrimitive(Primitive_ptr);
	void visitVariable(Variable_ptr);
protected:
	void push_scope(Visitable_ptr);
	Visitable_ptr pop_scope();
	void add_term_to_check_list(Term_ptr);
	void add_terms_to_check_list(TermList_ptr);
	bool check_term(Term_ptr);
	void visit_and_callback(Term_ptr&);
	bool is_equivalent(Term_ptr, Term_ptr);
	std::string to_string(Visitable_ptr);

	Script_ptr root;
	SymbolTable_ptr symbol_table;

	std::vector<Visitable_ptr> scope_stack;
	std::map<Visitable_ptr, std::vector<Term_ptr>> check_table;
	std::queue<std::function <void (Term_ptr&)>> callbacks;
private:
	static const int VLOG_LEVEL;
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SRC_SOLVER_FORMULAOPTIMIZER_H_ */
