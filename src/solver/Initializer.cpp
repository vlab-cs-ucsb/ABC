/*
 * Initializer.cpp
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#include "Initializer.h"

namespace Vlab {
namespace SMT {

Initializer::Initializer(Script_ptr script, SymbolTable_ptr symbol_table)
	: root (script), symbol_table (symbol_table) { }

Initializer::~Initializer() { }

void Initializer::start() {
	CHECK_NOTNULL(root);
	visit(root);
	end();
}

void Initializer::end() {

}

void Initializer::visitScript(Script_ptr script) {

	CommandList_ptr commands = script->commands;

	for (auto iter = commands->begin(); iter != commands->end();) {
		if ((*iter)->getType() != Command::Type::ASSERT) {
			VLOG(1) << (**iter);
			visit (*iter);
			delete (*iter);
			iter = commands->erase(iter);
		} else {
			iter++;
		}
	}

	visit_children_of(script);
}

void Initializer::visitCommand(Command_ptr command) {

	switch (command->getType()) {
	case Command::Type::DECLARE_FUN:
	{
		break;
	}
	case Command::Type::CHECK_SAT:
	{
		break;
	}
	case Command::Type::CHECK_SAT_AND_COUNT:
	{
		break;
	}
	case Command::Type::ASSERT:
	{
		break;
	}
	default:
		LOG(WARNING) << "Command is not handled, skipping: " << *command;
		LOG(WARNING) << "Please contact support for unhandled commands";
		break;
	}
}

void Initializer::visitTerm(Term_ptr term) {  }

void Initializer::visitSort(Sort_ptr sort) {  }

void Initializer::visitAttribute(Attribute_ptr attribute) {  }

void Initializer::visitSortedVar(SortedVar_ptr sorted_var) { }

void Initializer::visitVarBinding(VarBinding_ptr var_binding) {  }

void Initializer::visitIdentifier(Identifier_ptr identifier) { }

void Initializer::visitExclamation(Exclamation_ptr exclamation_term) {  }

void Initializer::visitExists(Exists_ptr exists_term) { }

void Initializer::visitForAll(ForAll_ptr for_all_term) {  }

void Initializer::visitLet(Let_ptr let_term) { }

void Initializer::visitAnd(And_ptr and_term) { }

void Initializer::visitOr(Or_ptr or_term) { }

void Initializer::visitNot(Not_ptr not_term) { }

void Initializer::visitUMinus(UMinus_ptr u_minus_term) { }

void Initializer::visitMinus(Minus_ptr minus_term) { }

void Initializer::visitPlus(Plus_ptr plus_term) { }

void Initializer::visitEq(Eq_ptr eq_term) {  }

void Initializer::visitGt(Gt_ptr gt_term) {  }

void Initializer::visitGe(Ge_ptr ge_term) {  }

void Initializer::visitLt(Lt_ptr lt_term) {  }

void Initializer::visitLe(Le_ptr le_term) {  }

void Initializer::visitConcat(Concat_ptr concat_term) {  }

void Initializer::visitIn(In_ptr in_term) {  }

void Initializer::visitLen(Len_ptr len_term) {  }

void Initializer::visitContains(Contains_ptr contains_term) {  }

void Initializer::visitBegins(Begins_ptr begins_term) {  }

void Initializer::visitEnds(Ends_ptr ends_term) { }

void Initializer::visitIndexOf(IndexOf_ptr index_of_term) { }

void Initializer::visitReplace(Replace_ptr replace_term) {  }

void Initializer::visitCount(Count_ptr count_term) {  }

void Initializer::visitIte(Ite_ptr ite_term) {  }

void Initializer::visitReConcat(ReConcat_ptr re_concat_term) {  }

void Initializer::visitToRegex(ToRegex_ptr to_regex_term) {  }

void Initializer::visitUnknownTerm(Unknown_ptr unknown_term) {  }

void Initializer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) { }

void Initializer::visitQualIdentifier(QualIdentifier_ptr qi_term) { }

void Initializer::visitTermConstant(TermConstant_ptr term_constant) { }

void Initializer::visitTVariable(TVariable_ptr t_variable) { }

void Initializer::visitTBool(TBool_ptr t_bool) { }

void Initializer::visitTInt(TInt_ptr t_int) { }

void Initializer::visitTString(TString_ptr t_string) { }

void Initializer::visitPrimitive(Primitive_ptr primitive) { }

void Initializer::visitVariable(Variable_ptr variable) { }

} /* namespace SMT */
} /* namespace Vlab */
