/*
 * BooleanVarReductor.cpp
 *
 *  Created on: May 2, 2015
 *      Author: baki
 */

#include "BooleanVarReductor.h"

namespace Vlab {
namespace SMT {

BooleanVarReductor::BooleanVarReductor(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table) { }

BooleanVarReductor::~BooleanVarReductor() { }


void BooleanVarReductor::start() {
	visit(root);
	end();
}

void BooleanVarReductor::end() {
}

void BooleanVarReductor::visitScript(Script_ptr script) {
	visit_children_of(script);
}

void BooleanVarReductor::visitCommand(Command_ptr command) {

	switch (command->getType()) {
		case Command::Type::ASSERT:
		{
			Assert_ptr assert = dynamic_cast<Assert_ptr>(command);
			visit_and_callback(assert->term);
			break;
		}
	default:
		LOG(FATAL) << "'" << *command<< "' is not expected.";
		break;
	}
}

void BooleanVarReductor::visitTerm(Term_ptr term) {  }

void BooleanVarReductor::visitSort(Sort_ptr sort) { }

void BooleanVarReductor::visitAttribute(Attribute_ptr attribute) {  }

void BooleanVarReductor::visitSortedVar(SortedVar_ptr sorted_var) { }

void BooleanVarReductor::visitVarBinding(VarBinding_ptr var_binding) {  }

void BooleanVarReductor::visitIdentifier(Identifier_ptr identifier) { }

void BooleanVarReductor::visitExclamation(Exclamation_ptr exclamation_term) {  }

void BooleanVarReductor::visitExists(Exists_ptr exists_term) { }

void BooleanVarReductor::visitForAll(ForAll_ptr for_all_term) {  }

void BooleanVarReductor::visitLet(Let_ptr let_term) { }

void BooleanVarReductor::visitAnd(And_ptr and_term) {
	for (auto& term : *(and_term->term_list)) {
		visit_and_callback(term);
	}
}

void BooleanVarReductor::visitOr(Or_ptr or_term) {
	for (auto& term : *(or_term->term_list)) {
		visit_and_callback(term);
	}
}

void BooleanVarReductor::visitNot(Not_ptr not_term) {
	visit_and_callback(not_term->term);
}

void BooleanVarReductor::visitUMinus(UMinus_ptr u_minus_term) {
	visit_and_callback(u_minus_term->term);
}

void BooleanVarReductor::visitMinus(Minus_ptr minus_term) {
	visit_and_callback(minus_term->left_term);
	visit_and_callback(minus_term->right_term);

}

void BooleanVarReductor::visitPlus(Plus_ptr plus_term) {
	visit_and_callback(plus_term->left_term);
	visit_and_callback(plus_term->right_term);
}

void BooleanVarReductor::visitEq(Eq_ptr eq_term) {
	visit_and_callback(eq_term->left_term);
	visit_and_callback(eq_term->right_term);

}

void BooleanVarReductor::visitGt(Gt_ptr gt_term) {
	visit_and_callback(gt_term->left_term);
	visit_and_callback(gt_term->right_term);

}

void BooleanVarReductor::visitGe(Ge_ptr ge_term) {
	visit_and_callback(ge_term->left_term);
	visit_and_callback(ge_term->right_term);

}

void BooleanVarReductor::visitLt(Lt_ptr lt_term) {
	visit_and_callback(lt_term->left_term);
	visit_and_callback(lt_term->right_term);

}

void BooleanVarReductor::visitLe(Le_ptr le_term) {
	visit_and_callback(le_term->left_term);
	visit_and_callback(le_term->right_term);

}

void BooleanVarReductor::visitConcat(Concat_ptr concat_term) {
	for (auto& term_ptr : *(concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}
}

void BooleanVarReductor::visitIn(In_ptr in_term) {
	visit_and_callback(in_term->left_term);
	visit_and_callback(in_term->right_term);
}

void BooleanVarReductor::visitLen(Len_ptr len_term) {
	visit_and_callback(len_term->term);
}

void BooleanVarReductor::visitContains(Contains_ptr contains_term) {
	visit_and_callback(contains_term->subject_term);
	visit_and_callback(contains_term->search_term);
}

void BooleanVarReductor::visitBegins(Begins_ptr begins_term) {
	visit_and_callback(begins_term->subject_term);
	visit_and_callback(begins_term->search_term);
}

void BooleanVarReductor::visitEnds(Ends_ptr ends_term) {
	visit_and_callback(ends_term->subject_term);
	visit_and_callback(ends_term->search_term);
}

void BooleanVarReductor::visitIndexOf(IndexOf_ptr index_of_term) {
	visit_and_callback(index_of_term->subject_term);
	visit_and_callback(index_of_term->search_term);
}

void BooleanVarReductor::visitReplace(Replace_ptr replace_term) {
	visit_and_callback(replace_term->subject_term);
	visit_and_callback(replace_term->search_term);
	visit_and_callback(replace_term->replace_term);
}

void BooleanVarReductor::visitCount(Count_ptr count_term) {
	visit_and_callback(count_term->bound_term);
	visit_and_callback(count_term->subject_term);
}

void BooleanVarReductor::visitIte(Ite_ptr ite_term) {
	visit_and_callback(ite_term->cond);
	visit_and_callback(ite_term->then_branch);
	visit_and_callback(ite_term->else_branch);
}

void BooleanVarReductor::visitReConcat(ReConcat_ptr re_concat_term) {
	for (auto& term_ptr : *(re_concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}

}

void BooleanVarReductor::visitToRegex(ToRegex_ptr to_regex_term) { }

void BooleanVarReductor::visitUnknownTerm(Unknown_ptr unknown_term) {  }

void BooleanVarReductor::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void BooleanVarReductor::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void BooleanVarReductor::visitTermConstant(TermConstant_ptr term_constant) { }

void BooleanVarReductor::visitTVariable(TVariable_ptr t_variable) { }

void BooleanVarReductor::visitTBool(TBool_ptr t_bool) { }

void BooleanVarReductor::visitTInt(TInt_ptr t_int) { }

void BooleanVarReductor::visitTString(TString_ptr t_string) { }

void BooleanVarReductor::visitPrimitive(Primitive_ptr primitive) { }

void BooleanVarReductor::visitVariable(Variable_ptr variable) { }

void BooleanVarReductor::visit_and_callback(Term_ptr& term) {
	visit(term);
	if (not callbacks.empty()) {
		callbacks.top()(term);
		callbacks.pop();
	}
}

} /* namespace SMT */
} /* namespace Vlab */
