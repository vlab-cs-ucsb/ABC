/*
 * OptimizationRuleRunner.cpp
 *
 *  Created on: May 6, 2015
 *      Author: baki
 */

#include "OptimizationRuleRunner.h"

namespace Vlab {
namespace SMT {

OptimizationRuleRunner::OptimizationRuleRunner(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table), current_assert (nullptr) { }

OptimizationRuleRunner::~OptimizationRuleRunner() { }


void OptimizationRuleRunner::start() {

	if (not has_optimization_rules()) { return; }

	symbol_table->push_scope(root);
	visit(root);
	symbol_table->pop_scope();

	end();

}

void OptimizationRuleRunner::end() { }

void OptimizationRuleRunner::visitScript(Script_ptr script) {
	CommandList_ptr commands = script->command_list;
	for (auto iter = commands->begin(); iter != commands->end(); ) {
		visit(*iter);
		if (current_assert->term == nullptr) {
			delete (*iter);
			iter = commands->erase(iter);
			DVLOG(15) << "remove: assert command";
		} else {
			iter++;
		}
		delete_list.clear();
	}

	if (script->command_list->empty()) {
		script->command_list->push_back(new Assert(generate_dummy_term()));
	}
}

void OptimizationRuleRunner::visitCommand(Command_ptr command) {

	switch (command->getType()) {
		case Command::Type::ASSERT:
		{
			current_assert = dynamic_cast<Assert_ptr>(command);
			check_and_substitute_var(current_assert->term);
			visit_and_callback(current_assert->term);
			if (delete_list.find(current_assert->term) != delete_list.end()) {
				delete_list.erase(current_assert->term);
				delete current_assert->term;
				current_assert->term = nullptr;
			}
			break;
		}
	default:
		LOG(FATAL) << "'" << *command<< "' is not expected.";
		break;
	}
}

void OptimizationRuleRunner::visitTerm(Term_ptr term) {  }

void OptimizationRuleRunner::visitExclamation(Exclamation_ptr exclamation_term) {  }

void OptimizationRuleRunner::visitExists(Exists_ptr exists_term) { }

void OptimizationRuleRunner::visitForAll(ForAll_ptr for_all_term) {  }

void OptimizationRuleRunner::visitLet(Let_ptr let_term) { }

void OptimizationRuleRunner::visitAnd(And_ptr and_term) {
	delete_list.clear();
	for (auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
		visit_and_callback(*iter);
		if (delete_list.find(*iter) != delete_list.end() or (*iter) == nullptr) {
			delete_list.erase(*iter);
			delete (*iter);
			iter = and_term->term_list->erase(iter);
			DVLOG(15) << "remove: term from 'and'";
		} else {
			iter++;
		}
	}
	delete_list.clear();

	if (and_term->term_list->empty()) {
		auto callback = [and_term](Term_ptr& term) mutable {
			delete and_term;
			term = nullptr;
		};
		callbacks.push(callback);
	} else if (and_term->term_list->size() == 1) {
		auto callback = [and_term](Term_ptr& term) mutable {
			Term_ptr child_term = and_term->term_list->front();
			and_term->term_list->clear();
			delete and_term;
			term = child_term;
		};
		callbacks.push(callback);
	}
}

void OptimizationRuleRunner::visitOr(Or_ptr or_term) {
	delete_list.clear();
	for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
		symbol_table -> push_scope(*iter);
		visit_and_callback(*iter);
		symbol_table -> pop_scope();
		if (delete_list.find(*iter) != delete_list.end() or (*iter) == nullptr) {
			delete_list.erase(*iter);
			delete (*iter);
			iter = or_term->term_list->erase(iter);
			DVLOG(15) << "remove: term from 'or'";
		} else {
			iter++;
		}
	}
	delete_list.clear();

	if (or_term->term_list->empty()) {
		auto callback = [or_term](Term_ptr& term) mutable {
			delete or_term;
			term = nullptr;
//			this->delete_list.insert(term);
		};
		callbacks.push(callback);
	} else if (or_term->term_list->size() == 1) {
		auto callback = [or_term](Term_ptr& term) mutable {
			Term_ptr child_term = or_term->term_list->front();
			or_term->term_list->clear();
			delete or_term;
			term = child_term;
		};
		callbacks.push(callback);
	}
}

void OptimizationRuleRunner::visitNot(Not_ptr not_term) {
	check_and_substitute_var(not_term->term);
	visit_and_callback(not_term->term);
	if (Term::Type::NOT == not_term->term->getType()) {
		auto callback = [not_term](Term_ptr& term) mutable {
			Not_ptr child_not = dynamic_cast<Not_ptr>(not_term->term);
			term = child_not->term;
			child_not->term = nullptr;
			delete not_term;
		};
		callbacks.push(callback);
	}
}

void OptimizationRuleRunner::visitUMinus(UMinus_ptr u_minus_term) {
	check_and_substitute_var(u_minus_term->term);
	visit_and_callback(u_minus_term->term);
	if (Term::Type::UMINUS == u_minus_term->term->getType()) {
		auto callback = [u_minus_term](Term_ptr& term) mutable {
			UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(u_minus_term->term);
			term = child_u_minus->term;
			child_u_minus->term = nullptr;
			delete u_minus_term;
		};
		callbacks.push(callback);
	}
}

void OptimizationRuleRunner::visitMinus(Minus_ptr minus_term) {
	check_and_substitute_var(minus_term->left_term);
	check_and_substitute_var(minus_term->right_term);
	visit_and_callback(minus_term->left_term);
	visit_and_callback(minus_term->right_term);
	if (Term::Type::UMINUS == minus_term->right_term->getType()) {
		// push call back to change (- a (- b)) into (+ a b)
		auto callback = [minus_term](Term_ptr& term) mutable {
			UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(minus_term->right_term);
			term = new Plus(minus_term->left_term, child_u_minus->term);
			minus_term->left_term = nullptr;
			child_u_minus->term = nullptr;
			delete minus_term;
		};
		callbacks.push(callback);
	}
}

void OptimizationRuleRunner::visitPlus(Plus_ptr plus_term) {
	check_and_substitute_var(plus_term->left_term);
	check_and_substitute_var(plus_term->right_term);
	visit_and_callback(plus_term->left_term);
	visit_and_callback(plus_term->right_term);
	if (Term::Type::UMINUS == plus_term->right_term->getType()) {
		// push call back to change (+ a (- b)) into (- a b)
		auto callback = [plus_term](Term_ptr& term) mutable {
			UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(plus_term->right_term);
			term = new Minus(plus_term->left_term, child_u_minus->term);
			plus_term->left_term = nullptr;
			child_u_minus->term = nullptr;
			delete plus_term;
		};
		callbacks.push(callback);
	}
}

void OptimizationRuleRunner::visitEq(Eq_ptr eq_term) {
	check_and_substitute_var(eq_term->left_term);
	check_and_substitute_var(eq_term->right_term);
	visit_and_callback(eq_term->left_term);
	visit_and_callback(eq_term->right_term);


	if (is_equivalent(eq_term->left_term, eq_term->right_term)) {
		this->delete_list.insert(eq_term);
	}
}

void OptimizationRuleRunner::visitGt(Gt_ptr gt_term) {
	check_and_substitute_var(gt_term->left_term);
	check_and_substitute_var(gt_term->right_term);
	visit_and_callback(gt_term->left_term);
	visit_and_callback(gt_term->right_term);

	//TODO syntactic checks can be add here to check for false
}

void OptimizationRuleRunner::visitGe(Ge_ptr ge_term) {
	check_and_substitute_var(ge_term->left_term);
	check_and_substitute_var(ge_term->right_term);
	visit_and_callback(ge_term->left_term);
	visit_and_callback(ge_term->right_term);

	if (is_equivalent(ge_term->left_term, ge_term->right_term)) {
		this->delete_list.insert(ge_term);
	}
}

void OptimizationRuleRunner::visitLt(Lt_ptr lt_term) {
	check_and_substitute_var(lt_term->left_term);
	check_and_substitute_var(lt_term->right_term);
	visit_and_callback(lt_term->left_term);
	visit_and_callback(lt_term->right_term);

	//TODO syntactic checks can be add here to check for false
}

void OptimizationRuleRunner::visitLe(Le_ptr le_term) {
	check_and_substitute_var(le_term->left_term);
	check_and_substitute_var(le_term->right_term);
	visit_and_callback(le_term->left_term);
	visit_and_callback(le_term->right_term);

	if (is_equivalent(le_term->left_term, le_term->right_term)) {
		this->delete_list.insert(le_term);
	}
}

void OptimizationRuleRunner::visitConcat(Concat_ptr concat_term) {
	for (auto& term_ptr : *(concat_term->term_list)) {
		check_and_substitute_var(term_ptr);
		visit_and_callback(term_ptr);
	}
}

void OptimizationRuleRunner::visitIn(In_ptr in_term) {
	check_and_substitute_var(in_term->left_term);
	check_and_substitute_var(in_term->right_term);
	visit_and_callback(in_term->left_term);
	visit_and_callback(in_term->right_term);

	if (is_equivalent(in_term->left_term, in_term->right_term)) {
		this->delete_list.insert(in_term);
	}
}

void OptimizationRuleRunner::visitLen(Len_ptr len_term) {
	check_and_substitute_var(len_term->term);
	visit_and_callback(len_term->term);
}

void OptimizationRuleRunner::visitContains(Contains_ptr contains_term) {
	check_and_substitute_var(contains_term->subject_term);
	check_and_substitute_var(contains_term->search_term);
	visit_and_callback(contains_term->subject_term);
	visit_and_callback(contains_term->search_term);

	if (is_equivalent(contains_term->subject_term, contains_term->search_term)) {
		this->delete_list.insert(contains_term);
	}
}

void OptimizationRuleRunner::visitBegins(Begins_ptr begins_term) {
	check_and_substitute_var(begins_term->subject_term);
	check_and_substitute_var(begins_term->search_term);
	visit_and_callback(begins_term->subject_term);
	visit_and_callback(begins_term->search_term);

	if (is_equivalent(begins_term->subject_term, begins_term->search_term)) {
		this->delete_list.insert(begins_term);
	}
}

void OptimizationRuleRunner::visitEnds(Ends_ptr ends_term) {
	check_and_substitute_var(ends_term->subject_term);
	check_and_substitute_var(ends_term->search_term);
	visit_and_callback(ends_term->subject_term);
	visit_and_callback(ends_term->search_term);

	if (is_equivalent(ends_term->subject_term, ends_term->search_term)) {
		this->delete_list.insert(ends_term);
	}
}

void OptimizationRuleRunner::visitIndexOf(IndexOf_ptr index_of_term) {
	check_and_substitute_var(index_of_term->subject_term);
	check_and_substitute_var(index_of_term->search_term);
	visit_and_callback(index_of_term->subject_term);
	visit_and_callback(index_of_term->search_term);
}

void OptimizationRuleRunner::visitReplace(Replace_ptr replace_term) {
	check_and_substitute_var(replace_term->subject_term);
	check_and_substitute_var(replace_term->search_term);
	check_and_substitute_var(replace_term->replace_term);
	visit_and_callback(replace_term->subject_term);
	visit_and_callback(replace_term->search_term);
	visit_and_callback(replace_term->replace_term);

}

void OptimizationRuleRunner::visitCount(Count_ptr count_term) {
	check_and_substitute_var(count_term->bound_term);
	check_and_substitute_var(count_term->subject_term);
	visit_and_callback(count_term->bound_term);
	visit_and_callback(count_term->subject_term);
}

void OptimizationRuleRunner::visitIte(Ite_ptr ite_term) { }

void OptimizationRuleRunner::visitReConcat(ReConcat_ptr re_concat_term) { }

void OptimizationRuleRunner::visitToRegex(ToRegex_ptr to_regex_term) { }

void OptimizationRuleRunner::visitUnknownTerm(Unknown_ptr unknown_term) {  }

void OptimizationRuleRunner::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void OptimizationRuleRunner::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void OptimizationRuleRunner::visitTermConstant(TermConstant_ptr term_constant) { }

void OptimizationRuleRunner::visitIdentifier(Identifier_ptr identifier) { }

void OptimizationRuleRunner::visitPrimitive(Primitive_ptr primitive) { }

void OptimizationRuleRunner::visitTVariable(TVariable_ptr t_variable) { }

void OptimizationRuleRunner::visitTBool(TBool_ptr t_bool) { }

void OptimizationRuleRunner::visitTInt(TInt_ptr t_int) { }

void OptimizationRuleRunner::visitTString(TString_ptr t_string) { }

void OptimizationRuleRunner::visitVariable(Variable_ptr variable) { }

void OptimizationRuleRunner::visitSort(Sort_ptr sort) { }

void OptimizationRuleRunner::visitAttribute(Attribute_ptr attribute) {  }

void OptimizationRuleRunner::visitSortedVar(SortedVar_ptr sorted_var) { }

void OptimizationRuleRunner::visitVarBinding(VarBinding_ptr var_binding) {  }

void OptimizationRuleRunner::visit_and_callback(Term_ptr& term) {
	visit(term);
	if (not callbacks.empty()) {
		callbacks.front()(term);
		callbacks.pop();

	}
}

bool OptimizationRuleRunner::has_optimization_rules() {
	for (auto& pair : symbol_table -> get_variable_substitution_table()) {
		if (not pair.second.empty()) {
			return true;
		}
	}
	return false;
}

bool OptimizationRuleRunner::is_equivalent(Term_ptr x, Term_ptr y) {
	if ( x == y ) {
		return true;
	}
	return (to_string(x) == to_string(y));
}

std::string OptimizationRuleRunner::to_string(Visitable_ptr visitable) {
	std::stringstream ss;
	Ast2Dot ast2dot(&ss);
	ast2dot.start(visitable);
	return ss.str();
}

Term_ptr OptimizationRuleRunner::generate_dummy_term() {
	std::string var_name;

	for (auto& variable_pair : symbol_table -> getVariables()) {
		var_name = variable_pair.first;
		if (variable_pair.second->isSymbolic()) break;
	}

	if (var_name.empty()) {
		Primitive_ptr primitive = new Primitive("dummy", Primitive::Type::STRING);
		TermConstant_ptr term_constant = new TermConstant(primitive);
		return term_constant;
	} else {
		Primitive_ptr primitive = new Primitive(var_name, Primitive::Type::SYMBOL);
		Identifier_ptr identifier = new Identifier(primitive);
		QualIdentifier_ptr var_ptr = new QualIdentifier(identifier);
		return var_ptr;
	}
}

bool OptimizationRuleRunner::check_and_substitute_var(Term_ptr& term) {
	if (Term::Type::QUALIDENTIFIER == term->getType()) {
		Variable_ptr variable = symbol_table -> getVariable(term);
		Term_ptr subs_term = symbol_table -> get_variable_substitution_term(variable);
		if (subs_term != nullptr) {
			DVLOG(15) << "apply rule: " << *variable << " (" << variable << ") -> " << *subs_term << " (" << subs_term <<" )";
			Term_ptr tmp_term = term;
			term = subs_term->clone();
			delete tmp_term;
		}
	}
	return false;
}

} /* namespace SMT */
} /* namespace Vlab */
