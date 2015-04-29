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
			visit_children_of(command);
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
		visit(term_ptr);
		while(not callbacks.empty()) {
//			callbacks.top()(term_ptr);
			callbacks.pop();
		}
	}
}

void SyntacticOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
	if (Term::Type::TERMCONSTANT == to_regex_term->term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_regex_term->term);
		if (Primitive::Type::STRING == term_constant->getValueType()) {
			std::string regex_template = "/%s/";
			std::string escaped_regex = escape_regex(term_constant->getValue());
			regex_template.replace(regex_template.find_first_of("%s"), 2, escaped_regex);
			Primitive_ptr regex_primitive = new Primitive(escaped_regex, Primitive::Type::REGEX);
			delete term_constant->primitive;
			term_constant->primitive = regex_primitive;

			auto callback = [&to_regex_term](Term_ptr& term) mutable {
				term = to_regex_term->term;
				to_regex_term->term = nullptr;
				delete to_regex_term;
			};

			std::function<void()> f = std::bind(callback,  to_regex_term->term);
//			callbacks.push(std::bind(callback, std::placeholders::_1));
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

std::string SyntacticOptimizer::escape_regex(std::string regex) {
	std::stringstream ss;
	for (auto ch : regex) {
		std::string escaper = "";
		// put escaping rules here, nothing for now.
		ss << escaper << ch;
	}
	return ss.str();
}


} /* namespace SMT */
} /* namespace Vlab */



