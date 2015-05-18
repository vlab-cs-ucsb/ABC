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
	: root (script), symbol_table (symbol_table) { }

ConstraintSorter::~ConstraintSorter() { }

void ConstraintSorter::start() {
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

			dependency_node_list.push_back(new DependencyNode(command));
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
	std::vector<DependencyNode*> local_dependency_node_list;
	for (auto& term : *(and_term->term_list)) {
		symbol_table->push_scope(term);

		visit(term);
		symbol_table->pop_scope();
	}
}

void ConstraintSorter::visitOr(Or_ptr or_term) {
	for (auto& term : *(or_term->term_list)) {
		symbol_table->push_scope(term);
		visit(term);
		symbol_table->pop_scope();
	}
}

void ConstraintSorter::visitNot(Not_ptr not_term) {

}

void ConstraintSorter::visitUMinus(UMinus_ptr u_minus_term) {

}

void ConstraintSorter::visitMinus(Minus_ptr minus_term) {

}

void ConstraintSorter::visitPlus(Plus_ptr plus_term) {

}

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

void ConstraintSorter::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

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

ConstraintSorter::DependencyNode::DependencyNode(Visitable_ptr node): node (node) { }

ConstraintSorter::DependencyNode::~DependencyNode() { }

void ConstraintSorter::DependencyNode::add_child_node(Visitable_ptr node, bool left_child) {
	all_child_node_list.push_back(node);
	left_child ? left_child_node_list.push_back(node) : right_child_node_list.push_back(node);
}

} /* namespace SMT */
} /* namespace Vlab */
