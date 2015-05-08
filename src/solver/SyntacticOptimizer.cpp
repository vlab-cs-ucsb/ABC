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

void SyntacticOptimizer::end() { }

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

void SyntacticOptimizer::visitExclamation(Exclamation_ptr exclamation_term) {  }

void SyntacticOptimizer::visitExists(Exists_ptr exists_term) { }

void SyntacticOptimizer::visitForAll(ForAll_ptr for_all_term) {  }

void SyntacticOptimizer::visitLet(Let_ptr let_term) { }

void SyntacticOptimizer::visitAnd(And_ptr and_term) {
	for (auto& term : *(and_term->term_list)) {
		visit_and_callback(term);
	}
}

void SyntacticOptimizer::visitOr(Or_ptr or_term) {
	for (auto& term : *(or_term->term_list)) {
		visit_and_callback(term);
	}
}

void SyntacticOptimizer::visitNot(Not_ptr not_term) {
	visit_and_callback(not_term->term);

	if (Term::Type::IN == not_term->term->getType()) {
		In_ptr in_ptr = dynamic_cast<In_ptr>(not_term->term);
		if (check_and_process_in_transformation(in_ptr->right_term, true)) {
			DVLOG(18) << "Transforming operation: '" << *not_term << "'";
			auto callback = [&not_term](Term_ptr& term) mutable {
				term = not_term->term;
				not_term->term = nullptr;
				delete not_term;
			};

			callbacks.push(callback);
		}
	}
}

void SyntacticOptimizer::visitUMinus(UMinus_ptr u_minus_term) {
	visit_and_callback(u_minus_term->term);
}

void SyntacticOptimizer::visitMinus(Minus_ptr minus_term) {
	visit_and_callback(minus_term->left_term);
	visit_and_callback(minus_term->right_term);

	if (Term::Type::TERMCONSTANT == minus_term->right_term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
		if (term_constant->getValue() == "0") {
			auto callback = [minus_term](Term_ptr& term) mutable {
				term = minus_term->left_term;
				minus_term->left_term = nullptr;
				delete minus_term;
			};
			callbacks.push(callback);
		}
	}
}

void SyntacticOptimizer::visitPlus(Plus_ptr plus_term) {
	visit_and_callback(plus_term->left_term);
	visit_and_callback(plus_term->right_term);

	if (Term::Type::TERMCONSTANT == plus_term->right_term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(plus_term->right_term);
		if (term_constant->getValue() == "0") {
			auto callback = [plus_term](Term_ptr& term) mutable {
				term = plus_term->left_term;
				plus_term->left_term = nullptr;
				delete plus_term;
			};
			callbacks.push(callback);
		}
	} else if (Term::Type::TERMCONSTANT == plus_term->left_term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(plus_term->left_term);
		if (term_constant->getValue() == "0") {
			auto callback = [plus_term](Term_ptr& term) mutable {
				term = plus_term->right_term;
				plus_term->right_term = nullptr;
				delete plus_term;
			};
			callbacks.push(callback);
		}
	}
}

void SyntacticOptimizer::visitEq(Eq_ptr eq_term) {
	visit_and_callback(eq_term->left_term);
	visit_and_callback(eq_term->right_term);

	if ( check_and_process_len_transformation(eq_term, eq_term->left_term, eq_term->right_term) ) {
		DVLOG(18) << "Applying len transformation: '" << *eq_term << "'";
	}
}

void SyntacticOptimizer::visitGt(Gt_ptr gt_term) {
	visit_and_callback(gt_term->left_term);
	visit_and_callback(gt_term->right_term);

	if ( check_and_process_len_transformation(gt_term, gt_term->left_term, gt_term->right_term) ) {
		DVLOG(18) << "Applying len transformation: '" << *gt_term << "'";
		auto callback = [gt_term](Term_ptr& term) mutable {
			term = new Eq(gt_term->left_term, gt_term->right_term);
			gt_term->left_term = nullptr;
			gt_term->right_term = nullptr;
			delete gt_term;
		};
		callbacks.push(callback);
	}
}

void SyntacticOptimizer::visitGe(Ge_ptr ge_term) {
	visit_and_callback(ge_term->left_term);
	visit_and_callback(ge_term->right_term);

	if ( check_and_process_len_transformation(ge_term, ge_term->left_term, ge_term->right_term) ) {
		DVLOG(18) << "Applying len transformation: '" << *ge_term << "'";
		auto callback = [ge_term](Term_ptr& term) mutable {
			term = new Eq(ge_term->left_term, ge_term->right_term);
			ge_term->left_term = nullptr;
			ge_term->right_term = nullptr;
			delete ge_term;
		};
		callbacks.push(callback);
	}
}

void SyntacticOptimizer::visitLt(Lt_ptr lt_term) {
	visit_and_callback(lt_term->left_term);
	visit_and_callback(lt_term->right_term);

	if ( check_and_process_len_transformation(lt_term, lt_term->left_term, lt_term->right_term) ) {
		DVLOG(18) << "Applying len transformation: '" << *lt_term << "'";
		auto callback = [lt_term](Term_ptr& term) mutable {
			term = new Eq(lt_term->left_term, lt_term->right_term);
			lt_term->left_term = nullptr;
			lt_term->right_term = nullptr;
			delete lt_term;
		};
		callbacks.push(callback);
	}
}

void SyntacticOptimizer::visitLe(Le_ptr le_term) {
	visit_and_callback(le_term->left_term);
	visit_and_callback(le_term->right_term);

	if ( check_and_process_len_transformation(le_term, le_term->left_term, le_term->right_term) ) {
		DVLOG(18) << "Applying len transformation: '" << *le_term << "'";
		auto callback = [le_term](Term_ptr& term) mutable {
			term = new Eq(le_term->left_term, le_term->right_term);
			le_term->left_term = nullptr;
			le_term->right_term = nullptr;
			delete le_term;
		};
		callbacks.push(callback);
	}
}

void SyntacticOptimizer::visitConcat(Concat_ptr concat_term) {
	for (auto& term_ptr : *(concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}
}

void SyntacticOptimizer::visitIn(In_ptr in_term) {
	visit_and_callback(in_term->left_term);
	visit_and_callback(in_term->right_term);
}

void SyntacticOptimizer::visitLen(Len_ptr len_term) {
	visit_and_callback(len_term->term);
}

void SyntacticOptimizer::visitContains(Contains_ptr contains_term) {
	visit_and_callback(contains_term->subject_term);
	visit_and_callback(contains_term->search_term);
}

void SyntacticOptimizer::visitBegins(Begins_ptr begins_term) {
	visit_and_callback(begins_term->subject_term);
	visit_and_callback(begins_term->search_term);
}

void SyntacticOptimizer::visitEnds(Ends_ptr ends_term) {
	visit_and_callback(ends_term->subject_term);
	visit_and_callback(ends_term->search_term);
}

void SyntacticOptimizer::visitIndexOf(IndexOf_ptr index_of_term) {
	visit_and_callback(index_of_term->subject_term);
	visit_and_callback(index_of_term->search_term);
}

void SyntacticOptimizer::visitReplace(Replace_ptr replace_term) {
	visit_and_callback(replace_term->subject_term);
	visit_and_callback(replace_term->search_term);
	visit_and_callback(replace_term->replace_term);
}

void SyntacticOptimizer::visitCount(Count_ptr count_term) {
	visit_and_callback(count_term->bound_term);
	visit_and_callback(count_term->subject_term);
}

void SyntacticOptimizer::visitIte(Ite_ptr ite_term) {
	visit_and_callback(ite_term->cond);
	visit_and_callback(ite_term->then_branch);
	visit_and_callback(ite_term->else_branch);

	DVLOG(18) << "Transforming operation: '" << *ite_term << "' into 'or'";
	auto callback = [ite_term](Term_ptr& term) mutable {
		And_ptr then_branch = dynamic_cast<And_ptr>(ite_term->then_branch);
		And_ptr else_branch = dynamic_cast<And_ptr>(ite_term->else_branch);
		then_branch->term_list->push_back(ite_term->cond->clone());
		then_branch->term_list->insert(then_branch->term_list->begin(), ite_term->cond->clone());
		if (Not_ptr not_term = dynamic_cast<Not_ptr>(ite_term->cond)) {
//			else_branch->term_list->push_back(not_term->term->clone());
			else_branch->term_list->insert(else_branch->term_list->begin(), not_term->term->clone());
		} else {
			not_term = new Not(ite_term->cond);
//			else_branch->term_list->push_back(not_term->clone());
			else_branch->term_list->insert(else_branch->term_list->begin(), not_term->clone());
		}

		TermList_ptr term_list = new TermList();
		term_list->push_back(then_branch);
		term_list->push_back(else_branch);
		term = new Or(term_list);
		ite_term->then_branch = nullptr;
		ite_term->else_branch = nullptr;
		delete ite_term;
	};
	callbacks.push(callback);
}

void SyntacticOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
	for (auto& term_ptr : *(re_concat_term->term_list)) {
		visit_and_callback(term_ptr);
	}

	DVLOG(18) << "Transforming operation: '" << *re_concat_term << "' into 'concat'";
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

	auto callback = [re_concat_term](Term_ptr& term) mutable {
		if (re_concat_term->term_list->size() == 1) {
			term = re_concat_term->term_list->front();
			re_concat_term->term_list->clear();
		} else {
			term = new Concat(re_concat_term->term_list);
			re_concat_term->term_list = nullptr;
		}
		delete re_concat_term;
	};
	callbacks.push(callback);
}

void SyntacticOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
	if (Term::Type::TERMCONSTANT == to_regex_term->term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_regex_term->term);
		if (Primitive::Type::STRING == term_constant->getValueType()) {
			DVLOG(18) << "Transforming operation: '" << *to_regex_term << "'";
			std::string regex_template = "/%s/";
			std::string escaped_regex = escape_regex(term_constant->getValue());
			regex_template.replace(regex_template.find_first_of("%s"), 2, escaped_regex);
			Primitive_ptr regex_primitive = new Primitive(regex_template, Primitive::Type::REGEX);
			delete term_constant->primitive;
			term_constant->primitive = regex_primitive;

			auto callback = [to_regex_term](Term_ptr& term) mutable {
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

void SyntacticOptimizer::visitIdentifier(Identifier_ptr identifier) { }

void SyntacticOptimizer::visitPrimitive(Primitive_ptr primitive) { }

void SyntacticOptimizer::visitTVariable(TVariable_ptr t_variable) { }

void SyntacticOptimizer::visitTBool(TBool_ptr t_bool) { }

void SyntacticOptimizer::visitTInt(TInt_ptr t_int) { }

void SyntacticOptimizer::visitTString(TString_ptr t_string) { }

void SyntacticOptimizer::visitVariable(Variable_ptr variable) { }

void SyntacticOptimizer::visitSort(Sort_ptr sort) { }

void SyntacticOptimizer::visitAttribute(Attribute_ptr attribute) {  }

void SyntacticOptimizer::visitSortedVar(SortedVar_ptr sorted_var) { }

void SyntacticOptimizer::visitVarBinding(VarBinding_ptr var_binding) {  }


void SyntacticOptimizer::visit_and_callback(Term_ptr& term) {
	visit(term);
	if (not callbacks.empty()) {
		callbacks.front()(term);
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

bool SyntacticOptimizer::check_and_process_in_transformation(Term_ptr term, bool isComplement) {
	if (Term::Type::TERMCONSTANT == term->getType()) {
		TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term);
		if (Primitive::Type::REGEX == term_constant->getValueType() and isComplement){
			std::string data = regex_to_str(term_constant->getValue());
			if (data.find_first_of("~(") == 0 and data.back() == ')') {
				data.replace(0, 2, "");
				data.pop_back();
			} else {
				std::string regex_template = "/~(%s)/";
				regex_template.replace(regex_template.find_first_of("%s"), 2, data);
				data = regex_template;
			}
			term_constant->primitive->setData(data);
			return true;
		} else if (Primitive::Type::STRING == term_constant->getValueType()  and isComplement) {
			std::string regex_template = "/~(%s)/";
			regex_template.replace(regex_template.find_first_of("%s"), 2, escape_regex(term_constant->getValue()));
			term_constant->primitive->setData(regex_template);
			term_constant->primitive->setType(Primitive::Type::REGEX);
			return true;
		}
	}

	return false;
}

bool SyntacticOptimizer::check_and_process_len_transformation(Term_ptr operation, Term_ptr& left_term,Term_ptr& right_term) {
	return __check_and_process_len_transformation(operation->str(), left_term, right_term) ||
			__check_and_process_len_transformation(syntactic_reverse_relation(operation->str()), right_term, left_term);
}

bool SyntacticOptimizer::__check_and_process_len_transformation(std::string operation, Term_ptr& left_term,Term_ptr& right_term) {
	if (Term::Type::LEN == left_term->getType()) {
		Len_ptr len_ptr = dynamic_cast<Len_ptr>(left_term);
		if (Term::Type::TERMCONSTANT == right_term->getType()) {
			TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(right_term);
			if (term_constant->getValueType() == Primitive::Type::NUMERAL) {
				int value = std::stoi(term_constant->getValue());
				std::string regex_template = "/.{%s,%s}/";
				std::string l_value = "";
				std::string r_value = "";
				if (operation == "=") {
					l_value = std::to_string( value );
					r_value = std::to_string( value );
				} else if (operation == "<") {
					l_value = "0";
					r_value = std::to_string( value - 1 );
				} else if (operation == "<=") {
					l_value = "0";
					r_value = std::to_string( value );
				} else if (operation == ">") {
					l_value = std::to_string( value + 1 );
				} else if (operation == ">=") {
					l_value = std::to_string( value );
				} else {
					return false;
				}
				regex_template.replace(regex_template.find_first_of("%s"), 2, l_value); // replace l
				regex_template.replace(regex_template.find_first_of("%s"), 2, r_value); // replace r
				term_constant->primitive->setData(regex_template);
				term_constant->primitive->setType(Primitive::Type::REGEX);
				left_term = len_ptr->term;
				len_ptr->term = nullptr;
				delete len_ptr;
				return true;
			}
		}
	}
	return false;
}


std::string SyntacticOptimizer::syntactic_reverse_relation(std::string operation) {
	if (operation == "<") {
		return ">";
	} else if (operation == "<=") {
		return ">=";
	} else if (operation == ">") {
		return "<";
	} else if (operation == ">=") {
		return "<=";
	} else {
		return operation;
	}
}

} /* namespace SMT */
} /* namespace Vlab */



