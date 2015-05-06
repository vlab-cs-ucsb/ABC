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
	: root (script), symbol_table (symbol_table),
	  target_type(Variable::Type::NONE), existential_elimination_phase(true) { }

VariableOptimizer::~VariableOptimizer() { }


/**
 * Apply the following sequentially for Bool, Int, String variables
 * 1 - Collect existential elimination rules and apply them
 * 2 - Collect variable reduction rules and apply them
 */
void VariableOptimizer::start() {
	Counter counter(root, symbol_table);
	counter.start();

	target_type = Variable::Type::BOOL;
	existential_elimination_phase = true;
	symbol_table->push_scope(root);
	visit(root);
	symbol_table->pop_scope();

	// apply substition rule
	// clear any previous rule
	counter.start();

	existential_elimination_phase = false;
	symbol_table->push_scope(root);
	visit(root);
	symbol_table->pop_scope();

	// apply substition rule
	// clear any previous rule
	counter.start();

	end();

	target_type = Variable::Type::INT;
//	...
	end();
}

void VariableOptimizer::end() {
//	call variable substitution
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
		symbol_table -> push_scope(term);
		visit(term);
		symbol_table -> pop_scope();
	}
}

void VariableOptimizer::visitNot(Not_ptr not_term) { }

void VariableOptimizer::visitUMinus(UMinus_ptr u_minus_term) { }

void VariableOptimizer::visitMinus(Minus_ptr minus_term) { }

void VariableOptimizer::visitPlus(Plus_ptr plus_term) { }

void VariableOptimizer::visitEq(Eq_ptr eq_term) {

	if (existential_elimination_phase) {
		if (Term::Type::QUALIDENTIFIER == eq_term->left_term->getType() and
				Term::Type::QUALIDENTIFIER == eq_term->right_term->getType()) {

			Variable_ptr left_var = symbol_table -> getVariable(get_variable_name(eq_term->left_term));
			Variable_ptr right_var = symbol_table -> getVariable(get_variable_name(eq_term->right_term));

			if (left_var->getType() == target_type) {
				if (symbol_table -> get_total_count(left_var->getName()) == symbol_table -> get_local_count(left_var->getName()) and
						symbol_table -> get_total_count(right_var->getName()) == symbol_table -> get_local_count(right_var->getName())) {

					if (symbol_table -> get_total_count(left_var->getName()) <= symbol_table -> get_total_count(right_var->getName())) {
						// replace left with right
					} else {
						// replace right with left
					}
				}
			}
		}
	} else {

	}

}

void VariableOptimizer::visitGt(Gt_ptr gt_term) { }

void VariableOptimizer::visitGe(Ge_ptr ge_term) { }

void VariableOptimizer::visitLt(Lt_ptr lt_term) { }

void VariableOptimizer::visitLe(Le_ptr le_term) { }

void VariableOptimizer::visitConcat(Concat_ptr concat_term) { }

void VariableOptimizer::visitIn(In_ptr in_term) { }

void VariableOptimizer::visitLen(Len_ptr len_term) { }

void VariableOptimizer::visitContains(Contains_ptr contains_term) { }

void VariableOptimizer::visitBegins(Begins_ptr begins_term) { }

void VariableOptimizer::visitEnds(Ends_ptr ends_term) { }

void VariableOptimizer::visitIndexOf(IndexOf_ptr index_of_term) { }

void VariableOptimizer::visitReplace(Replace_ptr replace_term) { }

void VariableOptimizer::visitCount(Count_ptr count_term) { }

void VariableOptimizer::visitIte(Ite_ptr ite_term) { }

void VariableOptimizer::visitReConcat(ReConcat_ptr re_concat_term) { }

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

std::string VariableOptimizer::get_variable_name(Term_ptr term) {
	QualIdentifier_ptr variable_identifier = dynamic_cast<QualIdentifier_ptr>(term);
	return variable_identifier->getVarName();
}

void VariableOptimizer::add_variable_substitution_rule(Variable_ptr subject_var, Variable_ptr target_var, Term_ptr target_term) {
	if (subject_var->isSymbolic()) { return; }

	/* 1 - Update the target if the target variable is already a subject in the substitution map (rule transition) */
	for (auto& substitution_rule : symbol_table -> get_variable_substitution_map()) {
		if (target_var == substitution_rule.first) {
			target_term = substitution_rule.second;
			break;
		}
	}

	/* 2 - Update a rule with the target if the subject variable is already a target */
	for (auto& substitution_rule : symbol_table -> get_variable_substitution_map()) {
		if (Term::Type::QUALIDENTIFIER == substitution_rule.second->getType()) {
			if (subject_var == symbol_table -> getVariable(get_variable_name(substitution_rule.second))) {
				Term_ptr tmp_term = substitution_rule.second;
				substitution_rule.second = target_term->clone();
				delete tmp_term;
			}
		}
	}

	if (not symbol_table -> add_var_substitution_rule(subject_var, target_term->clone())) {
		LOG(FATAL) << "A variable cannot have multiple rules: " << *subject_var;
	}
}

} /* namespace SMT */
} /* namespace Vlab */
