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
namespace Solver {

class ConstraintSorter: public SMT::Visitor {
public:
	ConstraintSorter(SMT::Script_ptr, SymbolTable_ptr);
	virtual ~ConstraintSorter();
	void start();
	void end();

	void visitScript(SMT::Script_ptr);
	void visitCommand(SMT::Command_ptr);
	void visitTerm(SMT::Term_ptr);
	void visitExclamation(SMT::Exclamation_ptr);
	void visitExists(SMT::Exists_ptr);
	void visitForAll(SMT::ForAll_ptr);
	void visitLet(SMT::Let_ptr);
	void visitAnd(SMT::And_ptr);
	void visitOr(SMT::Or_ptr);
	void visitNot(SMT::Not_ptr);
	void visitUMinus(SMT::UMinus_ptr);
	void visitMinus(SMT::Minus_ptr);
	void visitPlus(SMT::Plus_ptr);
	void visitEq(SMT::Eq_ptr);
	void visitGt(SMT::Gt_ptr);
	void visitGe(SMT::Ge_ptr);
	void visitLt(SMT::Lt_ptr);
	void visitLe(SMT::Le_ptr);
	void visitConcat(SMT::Concat_ptr);
	void visitIn(SMT::In_ptr);
	void visitLen(SMT::Len_ptr);
	void visitContains(SMT::Contains_ptr);
	void visitBegins(SMT::Begins_ptr);
	void visitEnds(SMT::Ends_ptr);
	void visitIndexOf(SMT::IndexOf_ptr);
	void visitReplace(SMT::Replace_ptr);
	void visitCount(SMT::Count_ptr);
	void visitIte(SMT::Ite_ptr);
	void visitReConcat(SMT::ReConcat_ptr);
	void visitToRegex(SMT::ToRegex_ptr);
	void visitUnknownTerm(SMT::Unknown_ptr);
	void visitAsQualIdentifier(SMT::AsQualIdentifier_ptr);
	void visitQualIdentifier(SMT::QualIdentifier_ptr);
	void visitTermConstant(SMT::TermConstant_ptr);
	void visitSort(SMT::Sort_ptr);
	void visitTVariable(SMT::TVariable_ptr);
	void visitTBool(SMT::TBool_ptr);
	void visitTInt(SMT::TInt_ptr);
	void visitTString(SMT::TString_ptr);
	void visitAttribute(SMT::Attribute_ptr);
	void visitSortedVar(SMT::SortedVar_ptr);
	void visitVarBinding(SMT::VarBinding_ptr);
	void visitIdentifier(SMT::Identifier_ptr);
	void visitPrimitive(SMT::Primitive_ptr);
	void visitVariable(SMT::Variable_ptr);
protected:
	class VariableNode;
	class VisitableNode;
	typedef VariableNode* VariableNode_ptr;
	typedef VisitableNode* VisitableNode_ptr;

	VariableNode_ptr get_variable_node(SMT::Variable_ptr);
	VisitableNode_ptr process_child_nodes(VisitableNode_ptr, VisitableNode_ptr);
	void sort_visitable_nodes(std::vector<VisitableNode_ptr>& visitable_node_list);

	SMT::Script_ptr root;
	SymbolTable_ptr symbol_table;
	VisitableNode_ptr visitable_node;

	std::vector<VisitableNode_ptr> dependency_node_list;
	std::map<SMT::Variable_ptr, VariableNode_ptr> variable_nodes;

	class VisitableNode {
	public:
		VisitableNode();
		VisitableNode(SMT::Visitable_ptr node);
		~VisitableNode();
		std::string str();

		void set_node(SMT::Visitable_ptr node);
		SMT::Visitable_ptr get_node();
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
		SMT::Visitable_ptr _node;
		bool _has_symbolic_var_on_left;
		bool _has_symbolic_var_on_right;
		std::vector<SMT::Visitable_ptr> _next_node_list;
		std::vector<VariableNode_ptr> _all_child_node_list;
		std::vector<VariableNode_ptr> _left_child_node_list;
		std::vector<VariableNode_ptr> _right_child_node_list;
	private:
		void merge_vectors(std::vector<VariableNode_ptr>&,std::vector<VariableNode_ptr>&);
	};

	class VariableNode {
	public:
		VariableNode(SMT::Variable_ptr variable);
		~VariableNode();
		std::string str();

		SMT::Variable_ptr get_variable();
		void add_node(VisitableNode_ptr node, bool is_left_side);
	protected:
		SMT::Variable_ptr variable;
		std::vector<VisitableNode_ptr> all_var_appearance_list;
		std::vector<VisitableNode_ptr> left_side_var_appearance_list;
		std::vector<VisitableNode_ptr> right_side_var_appearance_list;
	};

private:
	static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_CONSTRAINTSORTER_H_ */
