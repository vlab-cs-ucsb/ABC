/*
 * VariableOptimizer.cpp
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#include "VariableOptimizer.h"

namespace Vlab {
namespace SMT {

VariableOptimizer::VariableOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table) { }

VariableOptimizer::~VariableOptimizer() { }


void VariableOptimizer::start() {
	Counter counter(root, symbol_table);
	counter.start();
//	visit(root);
	end();
}

void VariableOptimizer::end() {
}

void VariableOptimizer::visitScript(Script_ptr script) {
	visit_children_of(script);
}

void VariableOptimizer::visitCommand(Command_ptr command) {

	switch (command->getType()) {
		case Command::Type::ASSERT:
		{
			visit_children_of(command);
			break;
		}
	default:
		LOG(FATAL) << "'" << *command<< "' is not expected.";
		break;
	}
}

void VariableOptimizer::visitTerm(Term_ptr term) {  }

void VariableOptimizer::visitExclamation(Exclamation_ptr exclamation_term) {  }

void VariableOptimizer::visitExists(Exists_ptr exists_term) { }

void VariableOptimizer::visitForAll(ForAll_ptr for_all_term) {  }

void VariableOptimizer::visitLet(Let_ptr let_term) { }

void VariableOptimizer::visitAnd(And_ptr and_term) {
	for (auto& term : *(and_term->term_list)) {
		visit_and_callback(term);
	}
}

void VariableOptimizer::visitOr(Or_ptr or_term) {
	for (auto& term : *(or_term->term_list)) {
		visit_and_callback(term);
	}
}

void VariableOptimizer::visitNot(Not_ptr not_term) {
	visit_and_callback(not_term->term);
}

void VariableOptimizer::visitUMinus(UMinus_ptr u_minus_term) {
	visit_and_callback(u_minus_term->term);
}

void VariableOptimizer::visitMinus(Minus_ptr minus_term) {
	visit_and_callback(minus_term->left_term);
	visit_and_callback(minus_term->right_term);

}

void VariableOptimizer::visitPlus(Plus_ptr plus_term) {
	visit_and_callback(plus_term->left_term);
	visit_and_callback(plus_term->right_term);
}

void VariableOptimizer::visitEq(Eq_ptr eq_term) {
	visit_and_callback(eq_term->left_term);
	visit_and_callback(eq_term->right_term);

}

void VariableOptimizer::visitGt(Gt_ptr gt_term) {
	visit_and_callback(gt_term->left_term);
	visit_and_callback(gt_term->right_term);

}

void VariableOptimizer::visitGe(Ge_ptr ge_term) {
	visit_and_callback(ge_term->left_term);
	visit_and_callback(ge_term->right_term);

}

void VariableOptimizer::visitLt(Lt_ptr lt_term) {
	visit_and_callback(lt_term->left_term);
	visit_and_callback(lt_term->right_term);

}

void VariableOptimizer::visitLe(Le_ptr le_term) {
	visit_and_callback(le_term->left_term);
	visit_and_callback(le_term->right_term);

}

void VariableOptimizer::visitConcat(Concat_ptr concat_term) {
	for (auto& term_ptr : *(concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}
}

void VariableOptimizer::visitIn(In_ptr in_term) {
	visit_and_callback(in_term->left_term);
	visit_and_callback(in_term->right_term);
}

void VariableOptimizer::visitLen(Len_ptr len_term) {
	visit_and_callback(len_term->term);
}

void VariableOptimizer::visitContains(Contains_ptr contains_term) {
	visit_and_callback(contains_term->subject_term);
	visit_and_callback(contains_term->search_term);
}

void VariableOptimizer::visitBegins(Begins_ptr begins_term) {
	visit_and_callback(begins_term->subject_term);
	visit_and_callback(begins_term->search_term);
}

void VariableOptimizer::visitEnds(Ends_ptr ends_term) {
	visit_and_callback(ends_term->subject_term);
	visit_and_callback(ends_term->search_term);
}

void VariableOptimizer::visitIndexOf(IndexOf_ptr index_of_term) {
	visit_and_callback(index_of_term->subject_term);
	visit_and_callback(index_of_term->search_term);
}

void VariableOptimizer::visitReplace(Replace_ptr replace_term) {
	visit_and_callback(replace_term->subject_term);
	visit_and_callback(replace_term->search_term);
	visit_and_callback(replace_term->replace_term);
}

void VariableOptimizer::visitCount(Count_ptr count_term) {
	visit_and_callback(count_term->bound_term);
	visit_and_callback(count_term->subject_term);
}

void VariableOptimizer::visitIte(Ite_ptr ite_term) {
	visit_and_callback(ite_term->cond);
	visit_and_callback(ite_term->then_branch);
	visit_and_callback(ite_term->else_branch);
}

void VariableOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
	for (auto& term_ptr : *(re_concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}

}

void VariableOptimizer::visitToRegex(ToRegex_ptr to_regex_term) { }

void VariableOptimizer::visitUnknownTerm(Unknown_ptr unknown_term) {  }

void VariableOptimizer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void VariableOptimizer::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void VariableOptimizer::visitTermConstant(TermConstant_ptr term_constant) { }

void VariableOptimizer::visitIdentifier(Identifier_ptr identifier) { }

void VariableOptimizer::visitPrimitive(Primitive_ptr primitive) { }

void VariableOptimizer::visitTVariable(TVariable_ptr t_variable) { }

void VariableOptimizer::visitTBool(TBool_ptr t_bool) { }

void VariableOptimizer::visitTInt(TInt_ptr t_int) { }

void VariableOptimizer::visitTString(TString_ptr t_string) { }

void VariableOptimizer::visitVariable(Variable_ptr variable) { }

void VariableOptimizer::visitSort(Sort_ptr sort) { }

void VariableOptimizer::visitAttribute(Attribute_ptr attribute) {  }

void VariableOptimizer::visitSortedVar(SortedVar_ptr sorted_var) { }

void VariableOptimizer::visitVarBinding(VarBinding_ptr var_binding) {  }

void VariableOptimizer::visit_and_callback(Term_ptr& term) {
	visit(term);
	if (not callbacks.empty()) {
		callbacks.top()(term);
		callbacks.pop();
	}
}

} /* namespace SMT */
} /* namespace Vlab */
