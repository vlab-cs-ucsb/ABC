/*
 * ConstraintSorter.h
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#ifndef SOLVER_CONSTRAINTSORTER_H_
#define SOLVER_CONSTRAINTSORTER_H_

#include <vector>

#include <glog/logging.h>
#include "../smt/ast.h"
#include "SymbolTable.h"

namespace Vlab {
namespace SMT {

class ConstraintSorter: public Visitor {
public:
	ConstraintSorter(Script_ptr, SymbolTable_ptr);
	virtual ~ConstraintSorter();
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

	Script_ptr root;
	SymbolTable_ptr symbol_table;

private:
	static const int VLOG_LEVEL;

	class DependencyNode {
	public:
		DependencyNode(Visitable_ptr node);
		~DependencyNode();

		void add_child_node(Visitable_ptr node, bool left_child);
	protected:
		Visitable_ptr node;
		std::vector<Visitable_ptr> next_node_list;
		std::vector<Visitable_ptr> all_child_node_list;
		std::vector<Visitable_ptr> left_child_node_list;
		std::vector<Visitable_ptr> right_child_node_list;
	};

	std::vector<DependencyNode*> dependency_node_list;
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_CONSTRAINTSORTER_H_ */
