/*
 * SyntacticOptimizer.cpp
 *
 *  Created on: Apr 28, 2015
 *      Author: baki
 */

#include "SyntacticOptimizer.h"

namespace Vlab {
namespace SMT {

SyntacticOptimizer::SyntacticOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table) { }

SyntacticOptimizer::~SyntacticOptimizer() { }

void SyntacticOptimizer::start() {
	visit(root);
	end();
}

void SyntacticOptimizer::end() {
}

void SyntacticOptimizer::visitScript(Script_ptr script) {
	visit_children_of(script);
}

void SyntacticOptimizer::visitCommand(Command_ptr command) {

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

void SyntacticOptimizer::visitTerm(Term_ptr term) {  }

void SyntacticOptimizer::visitSort(Sort_ptr sort) { }

void SyntacticOptimizer::visitAttribute(Attribute_ptr attribute) {  }

void SyntacticOptimizer::visitSortedVar(SortedVar_ptr sorted_var) { }

void SyntacticOptimizer::visitVarBinding(VarBinding_ptr var_binding) {  }

void SyntacticOptimizer::visitIdentifier(Identifier_ptr identifier) { }

void SyntacticOptimizer::visitExclamation(Exclamation_ptr exclamation_term) {  }

void SyntacticOptimizer::visitExists(Exists_ptr exists_term) { }

void SyntacticOptimizer::visitForAll(ForAll_ptr for_all_term) {  }

void SyntacticOptimizer::visitLet(Let_ptr let_term) { }

void SyntacticOptimizer::visitAnd(And_ptr and_term) { }

void SyntacticOptimizer::visitOr(Or_ptr or_term) { }

void SyntacticOptimizer::visitNot(Not_ptr not_term) { }

void SyntacticOptimizer::visitUMinus(UMinus_ptr u_minus_term) { }

void SyntacticOptimizer::visitMinus(Minus_ptr minus_term) { }

void SyntacticOptimizer::visitPlus(Plus_ptr plus_term) { }

void SyntacticOptimizer::visitEq(Eq_ptr eq_term) {  }

void SyntacticOptimizer::visitGt(Gt_ptr gt_term) {  }

void SyntacticOptimizer::visitGe(Ge_ptr ge_term) {  }

void SyntacticOptimizer::visitLt(Lt_ptr lt_term) {  }

void SyntacticOptimizer::visitLe(Le_ptr le_term) {  }

void SyntacticOptimizer::visitConcat(Concat_ptr concat_term) {  }

void SyntacticOptimizer::visitIn(In_ptr in_term) {  }

void SyntacticOptimizer::visitLen(Len_ptr len_term) {  }

void SyntacticOptimizer::visitContains(Contains_ptr contains_term) {  }

void SyntacticOptimizer::visitBegins(Begins_ptr begins_term) {  }

void SyntacticOptimizer::visitEnds(Ends_ptr ends_term) { }

void SyntacticOptimizer::visitIndexOf(IndexOf_ptr index_of_term) { }

void SyntacticOptimizer::visitReplace(Replace_ptr replace_term) {  }

void SyntacticOptimizer::visitCount(Count_ptr count_term) {  }

void SyntacticOptimizer::visitIte(Ite_ptr ite_term) {  }

void SyntacticOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
	for (auto& term_ptr : *(re_concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}

	TermConstant_ptr initial_term_constant = nullptr;
	for (auto iter = re_concat_term->term_list->begin(); iter != re_concat_term->term_list->end(); ) {
		if (Term::Type::TERMCONSTANT == (*iter)->getType()) {
			TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
			if (initial_term_constant == nullptr) {
				initial_term_constant = term_constant;
			} else {
				pre_concat_constants(initial_term_constant, term_constant);
				delete term_constant; // deallocate
				re_concat_term->term_list->erase(iter);
				continue;
			}
		} else {
			initial_term_constant = nullptr;
		}
		iter++;
	}

	if (re_concat_term->term_list->size() == 1 and
			Term::Type::TERMCONSTANT == re_concat_term->term_list->front()->getType()) {
		auto callback = [&re_concat_term](Term_ptr& term) mutable {
			term = re_concat_term->term_list->front();
			re_concat_term->term_list->clear();
			delete re_concat_term;
		};
		callbacks.push(callback);
	}
}

void SyntacticOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
	if (Term::Type::TERMCONSTANT == to_regex_term->term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_regex_term->term);
		if (Primitive::Type::STRING == term_constant->getValueType()) {
			std::string regex_template = "/%s/";
			std::string escaped_regex = escape_regex(term_constant->getValue());
			regex_template.replace(regex_template.find_first_of("%s"), 2, escaped_regex);
			Primitive_ptr regex_primitive = new Primitive(regex_template, Primitive::Type::REGEX);
			delete term_constant->primitive;
			term_constant->primitive = regex_primitive;

			auto callback = [&to_regex_term](Term_ptr& term) mutable {
				term = to_regex_term->term;
				to_regex_term->term = nullptr;
				delete to_regex_term;
			};

			callbacks.push(callback);
		}
	}
}

void SyntacticOptimizer::visitUnknownTerm(Unknown_ptr unknown_term) {  }

void SyntacticOptimizer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void SyntacticOptimizer::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void SyntacticOptimizer::visitTermConstant(TermConstant_ptr term_constant) { }

void SyntacticOptimizer::visitTVariable(TVariable_ptr t_variable) { }

void SyntacticOptimizer::visitTBool(TBool_ptr t_bool) { }

void SyntacticOptimizer::visitTInt(TInt_ptr t_int) { }

void SyntacticOptimizer::visitTString(TString_ptr t_string) { }

void SyntacticOptimizer::visitPrimitive(Primitive_ptr primitive) { }

void SyntacticOptimizer::visitVariable(Variable_ptr variable) { }

void SyntacticOptimizer::visit_and_callback(Term_ptr& term) {
	visit(term);
	if (not callbacks.empty()) {
		callbacks.top()(term);
		callbacks.pop();
	}
}

std::string SyntacticOptimizer::escape_regex(std::string regex) {
	std::stringstream ss;
	for (auto ch : regex) {
		std::string escaper = "";
		// put escaping rules here, nothing for now.
		ss << escaper << ch;
	}
	return ss.str();
}

std::string SyntacticOptimizer::regex_to_str(std::string regex) {
	std::string::size_type last = regex.substr(1).find_last_of("/");
	return regex.substr(1, last);
}

void SyntacticOptimizer::pre_concat_constants(TermConstant_ptr left_constant, TermConstant_ptr right_constant) {
	std::stringstream ss;
	if (Primitive::Type::REGEX == left_constant->getValueType() or
			Primitive::Type::REGEX == right_constant->getValueType()) {
		std::string left_data = (Primitive::Type::REGEX == left_constant->getValueType()) ? regex_to_str(left_constant->getValue()) : left_constant->getValue();
		std::string right_data = (Primitive::Type::REGEX == right_constant->getValueType()) ? regex_to_str(right_constant->getValue()) : right_constant->getValue();
		ss << "/" << left_data << right_data << "/";
		left_constant->primitive->setType(Primitive::Type::REGEX);
		left_constant->primitive->setData( ss.str() );
	}

}

} /* namespace SMT */
} /* namespace Vlab */



