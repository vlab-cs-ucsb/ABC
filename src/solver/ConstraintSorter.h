/*
 * ConstraintSorter.h
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#ifndef SOLVER_CONSTRAINTSORTER_H_
#define SOLVER_CONSTRAINTSORTER_H_

#include <iostream>
#include <sstream>
#include <vector>
#include <map>
#include <algorithm>

#include <glog/logging.h>
#include "../smt/ast.h"
#include "SymbolTable.h"
#include "Counter.h"

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
	class VariableNode;
	class VisitableNode;
	typedef VariableNode* VariableNode_ptr;
	typedef VisitableNode* VisitableNode_ptr;

	VariableNode_ptr get_variable_node(Variable_ptr);
	VisitableNode_ptr process_child_nodes(VisitableNode_ptr, VisitableNode_ptr);
	void sort_visitable_nodes(std::vector<VisitableNode_ptr>& visitable_node_list);

	Script_ptr root;
	SymbolTable_ptr symbol_table;
	VisitableNode_ptr visitable_node;

	std::vector<VisitableNode_ptr> dependency_node_list;
	std::map<Variable_ptr, VariableNode_ptr> variable_nodes;

	class VisitableNode {
	public:
		VisitableNode();
		VisitableNode(Visitable_ptr node);
		~VisitableNode();
		std::string str();

		void set_node(Visitable_ptr node);
		Visitable_ptr get_node();
		void add_node(VariableNode_ptr variable, bool is_left_side);
		void add_nodes(std::vector<VariableNode_ptr>&, bool is_left_side);
		std::vector<VariableNode_ptr>& get_left_nodes();
		std::vector<VariableNode_ptr>& get_right_nodes();
		std::vector<VariableNode_ptr>& get_all_nodes();
		void shift_to_left();
		void shift_to_right();
		void add_me_to_child_variable_nodes();
		int num_of_total_vars();
		int num_of_left_vars();
		int num_of_right_vars();
		void check_for_symbolic_variables();
		bool has_symbolic_var_on_left();
		bool has_symbolic_var_on_right();
		bool has_symbolic_var();
	protected:
		Visitable_ptr _node;
		bool _has_symbolic_var_on_left;
		bool _has_symbolic_var_on_right;
		std::vector<Visitable_ptr> _next_node_list;
		std::vector<VariableNode_ptr> _all_child_node_list;
		std::vector<VariableNode_ptr> _left_child_node_list;
		std::vector<VariableNode_ptr> _right_child_node_list;
	private:
		void merge_vectors(std::vector<VariableNode_ptr>&,std::vector<VariableNode_ptr>&);
	};

	class VariableNode {
	public:
		VariableNode(Variable_ptr variable);
		~VariableNode();
		std::string str();

		Variable_ptr get_variable();
		void add_node(VisitableNode_ptr node, bool is_left_side);
	protected:
		Variable_ptr variable;
		std::vector<VisitableNode_ptr> all_var_appearance_list;
		std::vector<VisitableNode_ptr> left_side_var_appearance_list;
		std::vector<VisitableNode_ptr> right_side_var_appearance_list;
	};

private:
	static const int VLOG_LEVEL;
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_CONSTRAINTSORTER_H_ */
