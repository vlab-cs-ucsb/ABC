/*
 * ConstraintSorter.cpp
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#include "ConstraintSorter.h"

namespace Vlab {
namespace SMT {

const int ConstraintSorter::VLOG_LEVEL = 13;

ConstraintSorter::ConstraintSorter(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table), visitable_node (nullptr), is_left_side(true) { }

ConstraintSorter::~ConstraintSorter() { }

void ConstraintSorter::start() {
	Counter counter(root, symbol_table);
	counter.start();

	symbol_table->push_scope(root);
	visit(root);
	symbol_table->pop_scope();
	end();
}

void ConstraintSorter::end() { }

void ConstraintSorter::visitScript(Script_ptr script) {
	visit_children_of(script);
}

void ConstraintSorter::visitCommand(Command_ptr command) {

	switch (command->getType()) {
		case Command::Type::ASSERT:
		{
			visitable_node = nullptr;
			visit_children_of(command);

			break;
		}
	default:
		LOG(FATAL) << "'" << *command<< "' is not expected.";
		break;
	}
}

void ConstraintSorter::visitTerm(Term_ptr term) {  }

void ConstraintSorter::visitExclamation(Exclamation_ptr exclamation_term) {  }

void ConstraintSorter::visitExists(Exists_ptr exists_term) { }

void ConstraintSorter::visitForAll(ForAll_ptr for_all_term) {  }

void ConstraintSorter::visitLet(Let_ptr let_term) { }

void ConstraintSorter::visitAnd(And_ptr and_term) {

//	for (auto& term : *(and_term->term_list)) {
//		symbol_table->push_scope(term);
//		push_node(term);
//		visit(term);
//		pop_node();
//		symbol_table->pop_scope();
//	}
}

void ConstraintSorter::visitOr(Or_ptr or_term) {
//	for (auto& term : *(or_term->term_list)) {
//		symbol_table->push_scope(term);
//		visit(term);
//		symbol_table->pop_scope();
//	}
}

void ConstraintSorter::visitNot(Not_ptr not_term) {
	visitable_node = nullptr;
	visit_children_of(not_term);
	if (visitable_node != nullptr) {
		visitable_node->shift_to_right();
	}
}

void ConstraintSorter::visitUMinus(UMinus_ptr u_minus_term) {
	visitable_node = nullptr;
	visit_children_of(u_minus_term);
	if (visitable_node != nullptr) {
		visitable_node->shift_to_right();
	}
}

void ConstraintSorter::visitMinus(Minus_ptr minus_term) {
	visitable_node = nullptr;
	visit(minus_term->left_term);
	VisitableNode_ptr  left_node = visitable_node;
	visitable_node = nullptr;
	visit(minus_term->right_term);
	VisitableNode_ptr right_node = visitable_node;

	if (left_node != nullptr and right_node != nullptr) {
		right_node->shift_to_right();
		right_node->add_nodes(left_node->get_all_nodes(), true);
		delete left_node;
	} else if (left_node != nullptr) {
		left_node->shift_to_left();
		visitable_node = left_node;
	} else if (right_node != nullptr) {
		right_node->shift_to_right();
	}

}

void ConstraintSorter::visitPlus(Plus_ptr plus_term) { visit_children_of(plus_term); }

void ConstraintSorter::visitEq(Eq_ptr eq_term) {

}

void ConstraintSorter::visitGt(Gt_ptr gt_term) {

}

void ConstraintSorter::visitGe(Ge_ptr ge_term) {

}

void ConstraintSorter::visitLt(Lt_ptr lt_term) {

}

void ConstraintSorter::visitLe(Le_ptr le_term) {

}

void ConstraintSorter::visitConcat(Concat_ptr concat_term) {

}

void ConstraintSorter::visitIn(In_ptr in_term) {

}

void ConstraintSorter::visitLen(Len_ptr len_term) {

}

void ConstraintSorter::visitContains(Contains_ptr contains_term) {

}

void ConstraintSorter::visitBegins(Begins_ptr begins_term) {

}

void ConstraintSorter::visitEnds(Ends_ptr ends_term) {

}

void ConstraintSorter::visitIndexOf(IndexOf_ptr index_of_term) {

}

void ConstraintSorter::visitReplace(Replace_ptr replace_term) {

}

void ConstraintSorter::visitCount(Count_ptr count_term) {

}

void ConstraintSorter::visitIte(Ite_ptr ite_term) { }

void ConstraintSorter::visitReConcat(ReConcat_ptr re_concat_term) { }

void ConstraintSorter::visitToRegex(ToRegex_ptr to_regex_term) { }

void ConstraintSorter::visitUnknownTerm(Unknown_ptr unknown_term) {  }

void ConstraintSorter::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void ConstraintSorter::visitQualIdentifier(QualIdentifier_ptr qi_term) {
	Variable_ptr variable = symbol_table -> getVariable(qi_term->getVarName());
	VariableNode_ptr variable_node = get_variable_node(variable);
	variable_node->add_node(dependency_node_list.back(), is_left_side);
	dependency_node_list.back()->add_node(variable_node, is_left_side);
}

void ConstraintSorter::visitTermConstant(TermConstant_ptr term_constant) { }

void ConstraintSorter::visitIdentifier(Identifier_ptr identifier) { }

void ConstraintSorter::visitPrimitive(Primitive_ptr primitive) { }

void ConstraintSorter::visitTVariable(TVariable_ptr t_variable) { }

void ConstraintSorter::visitTBool(TBool_ptr t_bool) { }

void ConstraintSorter::visitTInt(TInt_ptr t_int) { }

void ConstraintSorter::visitTString(TString_ptr t_string) { }

void ConstraintSorter::visitVariable(Variable_ptr variable) { }

void ConstraintSorter::visitSort(Sort_ptr sort) { }

void ConstraintSorter::visitAttribute(Attribute_ptr attribute) {  }

void ConstraintSorter::visitSortedVar(SortedVar_ptr sorted_var) { }

void ConstraintSorter::visitVarBinding(VarBinding_ptr var_binding) {  }

void ConstraintSorter::push_node(Visitable_ptr node) {
	node_stack.push(node);
}

Visitable_ptr ConstraintSorter::pop_node() {
	Visitable_ptr node = node_stack.top();
	node_stack.pop();
	return node;
}

ConstraintSorter::VariableNode_ptr ConstraintSorter::get_variable_node(Variable_ptr variable) {
	auto it = variable_nodes.find(variable);
	if (it != variable_nodes.end()) {
		return it->second;
	}
	VariableNode_ptr variable_node = new VariableNode(variable);
	variable_nodes[variable] = variable_node;
	return variable_node;
}

ConstraintSorter::VisitableNode::VisitableNode(Visitable_ptr node): node (node) { }

ConstraintSorter::VisitableNode::~VisitableNode() { }

void ConstraintSorter::VisitableNode::add_node(ConstraintSorter::VariableNode_ptr variable, bool is_left_side) {
	all_child_node_list.push_back(variable);
	is_left_side ? left_child_node_list.push_back(variable) : right_child_node_list.push_back(variable);
}

void ConstraintSorter::VisitableNode::add_nodes(std::vector<VariableNode_ptr>& var_node_list, bool is_left_side) {
	merge_vectors(all_child_node_list, var_node_list);
	is_left_side ? merge_vectors(left_child_node_list, var_node_list) : merge_vectors(right_child_node_list, var_node_list);
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::VisitableNode::get_all_nodes() {
	return all_child_node_list;
}

void ConstraintSorter::VisitableNode::shift_to_left() {
	merge_vectors(left_child_node_list, right_child_node_list);
	right_child_node_list.clear();
}

void ConstraintSorter::VisitableNode::shift_to_right() {
	merge_vectors(right_child_node_list, left_child_node_list);
	left_child_node_list.clear();
}

void ConstraintSorter::VisitableNode::merge_vectors(std::vector<VariableNode_ptr>& vector_1, std::vector<VariableNode_ptr>& vector_2) {
	vector_1.insert(vector_1.end(), vector_2.begin(), vector_2.end());
}

ConstraintSorter::VariableNode::VariableNode(Variable_ptr variable)
	: variable (variable) { }

ConstraintSorter::VariableNode::~VariableNode() { }

void ConstraintSorter::VariableNode::add_node(ConstraintSorter::VisitableNode_ptr node, bool is_left_side) {
	all_var_appearance_list.push_back(node);
	is_left_side ? left_side_var_appearance_list.push_back(node) : right_side_var_appearance_list.push_back(node);
}

} /* namespace SMT */
} /* namespace Vlab */


