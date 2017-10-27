#include "ImplicationRunner.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
const int ImplicationRunner::VLOG_LEVEL = 20;

ImplicationRunner::ImplicationRunner(Script_ptr script, SymbolTable_ptr symbol_table, ConstraintInformation_ptr constraint_information)
  : AstTraverser(script),
    symbol_table_(symbol_table),
		constraint_information_(constraint_information) {
  setCallbacks();
  formula = nullptr;
}

ImplicationRunner::~ImplicationRunner() {
}

void ImplicationRunner::start() {
  DVLOG(VLOG_LEVEL) << "Starting the Implication Runner";

  symbol_table_->push_scope(root_, false);
  visitScript(root_);
  symbol_table_->pop_scope();

  end();
}

void ImplicationRunner::end() {

}

void ImplicationRunner::setCallbacks() {
  auto term_callback = [this] (Term_ptr term) -> bool {
    switch (term->type()) {
    case Term::Type::TERMCONSTANT: {
      return false;
    }
    default:
      return true;
    }
  };

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  setCommandPreCallback(command_callback);
  setTermPreCallback(term_callback);
}

void ImplicationRunner::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void ImplicationRunner::visitAnd(And_ptr and_term) {
	int i = 0;
	while(i < and_term->term_list->size()) {
		auto& term = and_term->term_list->at(i);
		current_and_ = and_term;
		visit(term);
		current_and_ = nullptr;
		i++;
	}

	// remove bad terms
	for(auto it = and_term->term_list->begin(); it != and_term->term_list->end();) {
		if(terms_to_remove.find(*it) != terms_to_remove.end()) {
			*it = nullptr;
			it = and_term->term_list->erase(it);
		} else{
			it++;
		}
	}

	if(Option::Solver::ENABLE_LEN_IMPLICATIONS) {
		AddLengthHeuristic(and_term);
		ResetHeuristicData();
	}


}

void ImplicationRunner::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table_->push_scope(term, false);
    visit(term);
    symbol_table_->pop_scope();
  }
}

// TODO separate len implications and string implications
void ImplicationRunner::visitEq(Eq_ptr eq_term) {

	if(Option::Solver::ENABLE_LEN_IMPLICATIONS) {
		CollectHeuristicInfo(eq_term);
	}

  if (Concat_ptr left_id = dynamic_cast<Concat_ptr>(eq_term->left_term)) {
    if (!is_precise(left_id) or !dynamic_cast<QualIdentifier_ptr>(eq_term->right_term)) {
//      if (Option::Solver::ENABLE_LEN_IMPLICATIONS) {
//        Term_ptr implication_term = new Eq(get_length(left_id), get_length(eq_term->right_term));
//        current_and_->term_list->push_back(implication_term);
//      }
      if (Option::Solver::USE_MULTITRACK_AUTO) {
      	if (QualIdentifier_ptr right_variable = dynamic_cast<QualIdentifier_ptr>(left_id->term_list->front())) {
					if (QualIdentifier_ptr left_variable = dynamic_cast<QualIdentifier_ptr>(eq_term->right_term)) {
						std::string left_name = left_variable->getVarName();
						std::string right_name = right_variable->getVarName();
						auto left_formula = constraint_information_->get_var_formula(left_name);
						auto right_formula = constraint_information_->get_var_formula(right_name);
						auto formula = left_formula->clone();
						formula->MergeVariables(right_formula);
						// only add begins term if it doesn't cause too many variables in one string formula
						if(formula->GetNumberOfVariables() <= 7) {
							if(left_formula != right_formula) {
								delete left_formula;
								delete right_formula;
							} else {
								delete left_formula;
							}
							for(auto iter : formula->GetVariableCoefficientMap()) {
								constraint_information_->set_var_formula(iter.first,formula);
							}
							Term_ptr implication_term_begins = new Begins(left_variable->clone(), left_id->term_list->front()->clone());
							current_and_->term_list->push_back(implication_term_begins);
						} else {
							DVLOG(VLOG_LEVEL) << "Can't add begins implication, would cause too many variables in one formula";
							delete formula;
						}
					}
				}
      }
      return;
    }
    return;
  }

  if (Concat_ptr right_id = dynamic_cast<Concat_ptr>(eq_term->right_term)) {
    if (!is_precise(right_id) or !dynamic_cast<QualIdentifier_ptr>(eq_term->left_term)) {
//    	if (Option::Solver::ENABLE_LEN_IMPLICATIONS) {
//				Term_ptr implication_term = new Eq(get_length(eq_term->left_term), get_length(right_id));
//				current_and_->term_list->push_back(implication_term);
//			}

      if (Option::Solver::USE_MULTITRACK_AUTO) {
        if (QualIdentifier_ptr left_variable = dynamic_cast<QualIdentifier_ptr>(eq_term->left_term)) {
          if (QualIdentifier_ptr right_variable = dynamic_cast<QualIdentifier_ptr>(right_id->term_list->front())) {

//          	auto query_var = symbol_table_->get_count_variable();
//          	auto v = symbol_table_->get_variable(left_variable);
//
//
//          	auto var_terms = constraint_information_->get_var_constraints(symbol_table_->get_variable(right_variable));
//          	if(var_terms.size() <= 1) {
//          		if(Eq_ptr eq_term2 = dynamic_cast<Eq_ptr>((*var_terms.begin()))) {
//          			if(Concat_ptr eq_right = dynamic_cast<Concat_ptr>(eq_term2->right_term)) {
//          				QualIdentifier_ptr inner_var = dynamic_cast<QualIdentifier_ptr>(eq_right->term_list->front());
//          				if(inner_var != nullptr) {
//          					auto inner_var_terms = constraint_information_->get_var_constraints(symbol_table_->get_variable(inner_var));
//          					if(inner_var_terms.size() == 1 and (*inner_var_terms.begin())->type() == Term::Type::NOTEQ) {
//          						NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>((*inner_var_terms.begin()));
//          						if(not_eq_term->right_term->type() == Term::Type::TERMCONSTANT) {
//
//
//          							auto eq_right_clone = eq_right->clone();
//          							eq_right_clone->term_list->push_back((*right_id->term_list)[1]->clone());
//
//          							TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(not_eq_term->right_term);
//
//          							std::string most_common = constraint_information_->most_common_string;
//          							int num = constraint_information_->strings[most_common];
//
////          							LOG(INFO) << "MOST COMMON: " << most_common;
////          							std::cin.get();
//          							if(num > 20) {
//          								if(term_constant->getValue() != constraint_information_->most_common_string) {
//          									//eq_term->right_term = eq_right_clone;
//														//terms_to_remove.insert(eq_term2);
//														//right_variable = inner_var->clone();
////														LOG(INFO) << "Yep!";
////														std::cin.get();
//														//return;
//          								} else {
//          									//return;
//
//          								}
//          							} else {
//          								if(term_constant->getValue() == constraint_information_->most_common_string) {
//          									eq_term->right_term = eq_right_clone;
//														terms_to_remove.insert(eq_term2);
//														return;
//													} else {
//														//eq_term->right_term = eq_right_clone;
//														//terms_to_remove.insert(eq_term2);
//														//right_variable = inner_var->clone();
//													}
//          							}
//          						}
//          					}
//          				}
//          			}
//          		}
//          	}




          	std::string left_name = left_variable->getVarName();
						std::string right_name = right_variable->getVarName();

						auto left_formula = constraint_information_->get_var_formula(left_name);
						auto right_formula = constraint_information_->get_var_formula(right_name);
						if(left_formula == nullptr) {
							LOG(FATAL) << "LEFT FORMULA NULL";
						}
						if(right_formula == nullptr) {
							LOG(FATAL) << "RIGHT FORMULA NULL";
						}
						auto formula = left_formula->clone();
						formula->MergeVariables(right_formula);
						// only add begins term if it doesn't cause too many variables in one string formula
						if(formula->GetNumberOfVariables() <= 9) {
							if(left_formula != right_formula) {
								delete left_formula;
								delete right_formula;
							} else {
								delete left_formula;
							}
							for(auto iter : formula->GetVariableCoefficientMap()) {
								constraint_information_->set_var_formula(iter.first,formula);
							}
							Term_ptr implication_term_begins = new Begins(left_variable->clone(), right_variable->clone());
							current_and_->term_list->push_back(implication_term_begins);
						} else {
							DVLOG(VLOG_LEVEL) << "Can't add begins implication, would cause too many variables in one formula";
							delete formula;
						}
          }
        }
      }
      return;
    }
    return;
  }


}


void ImplicationRunner::visitContains(Contains_ptr contains) {
  if (Term::Type::TERMCONSTANT not_eq contains->subject_term->type()
      and Term::Type::TERMCONSTANT not_eq contains->search_term->type()) {
    Term_ptr subject_length = get_length(contains->subject_term);
    Term_ptr search_length = get_length(contains->search_term);
    Term_ptr implication_term = new Ge(subject_length, search_length);
    current_and_->term_list->push_back(implication_term);
  }
}

void ImplicationRunner::visitEnds(Ends_ptr ends) {
//  if (Term::Type::TERMCONSTANT not_eq ends->subject_term->type()
//        and Term::Type::TERMCONSTANT not_eq ends->search_term->type()) {
//    Term_ptr subject_length = get_length(ends->subject_term);
//    Term_ptr search_length = get_length(ends->search_term);
//    Term_ptr implication_term = new Ge(subject_length, search_length);
//    current_and_->term_list->push_back(implication_term);
//  }
}


void ImplicationRunner::visitNotContains(NotContains_ptr not_contains) {
  if (Option::Solver::USE_MULTITRACK_AUTO) {
    if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(not_contains->subject_term)) {
      if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(not_contains->search_term)) {
          NotBegins_ptr implication_term = new NotBegins(not_contains->subject_term->clone(), not_contains->search_term->clone());
          current_and_->term_list->push_back(implication_term);
      }
    }
  }

}

void ImplicationRunner::visitNotEnds(NotEnds_ptr not_ends) {
  if (Option::Solver::USE_MULTITRACK_AUTO) {
    if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(not_ends->subject_term)) {
      if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(not_ends->search_term)) {
          NotEq_ptr implication_term = new NotEq(not_ends->subject_term->clone(), not_ends->search_term->clone());
          current_and_->term_list->push_back(implication_term);
      }
    }
  }

}

Term_ptr ImplicationRunner::get_length(Term_ptr term) {
  if (TermConstant_ptr constant = dynamic_cast<TermConstant_ptr>(term)) {
    if (Primitive::Type::STRING == constant->getValueType()) {
      return get_length_constant(constant);
    }
  } else if (Concat_ptr concat = dynamic_cast<Concat_ptr>(term)) {
    return get_length_concat(concat);
  }
  return new Len(term->clone());
}

TermConstant_ptr ImplicationRunner::get_length_constant(TermConstant_ptr term_constant) {
  int len = term_constant->getValue().length();
  std::string str_len = std::to_string(len);
  return new TermConstant(new Primitive(str_len, Primitive::Type::NUMERAL));

}

Plus_ptr ImplicationRunner::get_length_concat(Concat_ptr concat) {
  TermList_ptr term_list = new TermList();
  for (auto& term_ptr : * (concat->term_list)) {
    //Convert length directly to an integer if the term is a constant.
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term_ptr)) {
      term_list->push_back(get_length(term_constant));
    } else {
      term_list->push_back(new Len(term_ptr->clone()));
    }
  }
  return new Plus(term_list);
}


bool ImplicationRunner::is_precise(Concat_ptr concat) {
  if (TermConstant_ptr right = dynamic_cast<TermConstant_ptr>(concat->term_list->back())) {
    //is of the form x."a" and x."a" = y is aleady precise. 
    return true;
  }
  return false;
}

void ImplicationRunner::CollectHeuristicInfo(Eq_ptr eq_term) {
	if(QualIdentifier_ptr left_var = dynamic_cast<QualIdentifier_ptr>(eq_term->left_term)) {
		if(Concat_ptr right_id = dynamic_cast<Concat_ptr>(eq_term->right_term)) {
			Theory::ArithmeticFormula_ptr f = new Theory::ArithmeticFormula();
			f->AddVariable(left_var->getVarName(),-1);

			for(auto iter : *right_id->term_list) {
				if(TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(iter)) {
					int constant = term_constant->getValue().length();
					f->SetConstant(constant);
				} else if(QualIdentifier_ptr last_var = dynamic_cast<QualIdentifier_ptr>(iter)) {
					f->AddVariable(last_var->getVarName(),1);
				}

//				if(TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(right_id->term_list->at(1))) {
//					int constant = term_constant->getValue().length();
//					f->SetConstant(constant);
//				} else if(QualIdentifier_ptr last_var = dynamic_cast<QualIdentifier_ptr>(right_id->term_list->at(1))) {
//					f->AddVariable(last_var->getVarName(),1);
//				}
			}



			f->SetType(Theory::ArithmeticFormula::Type::EQ);
			if(formula == nullptr) {
				formula = f->clone();
			} else {
				auto new_formula = formula->Add(f);
				delete formula;
				formula = new_formula;
			}
			if(variable_formulas.find(left_var->getVarName()) != variable_formulas.end()) {
				auto new_formula = variable_formulas[left_var->getVarName()]->Subtract(f);
				delete variable_formulas[left_var->getVarName()];
				variable_formulas[left_var->getVarName()] = new_formula;
				delete f;
			} else {
				variable_formulas[left_var->getVarName()] = f;
			}
		}
	} else if(Len_ptr len_term = dynamic_cast<Len_ptr>(eq_term->left_term)) {
		if(QualIdentifier_ptr len_var = dynamic_cast<QualIdentifier_ptr>(len_term->term)) {
			auto f = new Theory::ArithmeticFormula();
			f->AddVariable(len_var->getVarName(),-1);
			if(TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(eq_term->right_term)) {
				int constant = std::stoi(term_constant->getValue());
				f->SetConstant(constant);
			} else if(QualIdentifier_ptr right_var = dynamic_cast<QualIdentifier_ptr>(eq_term->right_term)) {
				f->AddVariable(right_var->getVarName(),1);
			} else {
				delete f;
				return;
			}
			f->SetType(Theory::ArithmeticFormula::Type::EQ);
			if(variable_formulas.find(len_var->getVarName()) != variable_formulas.end()) {
				auto new_formula = variable_formulas[len_var->getVarName()]->Subtract(f);
				delete variable_formulas[len_var->getVarName()];
				variable_formulas[len_var->getVarName()] = new_formula;
				delete f;
			} else {
				variable_formulas[len_var->getVarName()] = f;
			}
			variables_to_expand.insert(len_var->getVarName());
		}
	}
}

void ImplicationRunner::AddLengthHeuristic(And_ptr and_term) {
	for(auto iter : variables_to_expand) {
		std::set<std::string> seen_variables;
		std::queue<std::string> variable_formulas_needed;
		std::vector<Theory::ArithmeticFormula_ptr> formulas;

		std::string variable_name = iter;

		if(variable_formulas.find(variable_name) == variable_formulas.end()) {
			continue;
		}
		variable_formulas_needed.push(variable_name);

		while(variable_formulas_needed.size() > 0) {
			// get the next variable name who's formula is needed
			auto current_var = variable_formulas_needed.front();
			variable_formulas_needed.pop();
			seen_variables.insert(current_var);
			// variable might not have formula; then continue if so
			if(variable_formulas.find(current_var) == variable_formulas.end()) {
				continue;
			}

			// get the current variable's formula and add it to our vector of formulas
			Theory::ArithmeticFormula_ptr current_formula = variable_formulas[current_var];
			formulas.push_back(current_formula);

			for(auto coeff_iter : current_formula->GetVariableCoefficientMap()) {
				// if variable has already been seen or is not needed, skip
				if(coeff_iter.second == 0 || seen_variables.find(coeff_iter.first) != seen_variables.end()) {
					continue;
				}
				// mark as seen, insert into variable's needed queue
				seen_variables.insert(coeff_iter.first);
				variable_formulas_needed.push(coeff_iter.first);
			}
		}

		Theory::ArithmeticFormula_ptr new_variable_formula = new Theory::ArithmeticFormula();
		new_variable_formula->SetType(Theory::ArithmeticFormula::Type::EQ);
		Theory::ArithmeticFormula_ptr tmp_formula = nullptr;
		int flag = 0;
		for(auto iter : formulas) {
			tmp_formula = new_variable_formula->Add(iter);
			delete new_variable_formula;
			new_variable_formula = tmp_formula;
		}

		delete variable_formulas[variable_name];
		variable_formulas[variable_name] = new_variable_formula;
	}

	if(formula != nullptr) {
		variable_formulas["base"] = formula;
		variables_to_expand.insert("base");
		formula = nullptr;
	}

	for(auto iter : variables_to_expand) {
//		DVLOG(VLOG_LEVEL) << iter << " has formula: ";
//		DVLOG(VLOG_LEVEL) << *variable_formulas[iter];

		int num_vars = 0;
		for(auto coeff_iter : variable_formulas[iter]->GetVariableCoefficientMap()) {
			if(coeff_iter.second != 0) {
				num_vars++;
			}
		}

		if(num_vars > 10) {
			DVLOG(VLOG_LEVEL) << "Too many variables to implement length heuristic";
			continue;
		} else if(num_vars == 0 || (num_vars == 1 && variable_formulas[iter]->GetVariableCoefficient(iter) != 0)) {
			continue;
		}

		TermList_ptr term_list = new TermList();
		for(auto coeff_iter : variable_formulas[iter]->GetVariableCoefficientMap()) {
			// don't add length term for variables not appearing in formula
			if(coeff_iter.second == 0) {
				continue;
			}
			TermList_ptr inner_term_list = new TermList();
			QualIdentifier_ptr qualid = new QualIdentifier(new Identifier(new Primitive(coeff_iter.first,Primitive::Type::SYMBOL)));
			Len_ptr len_term = new Len(qualid);
			inner_term_list->push_back(len_term);
			if(coeff_iter.second < 0) {
				TermConstant_ptr term_constant = new TermConstant(new Primitive(std::to_string(coeff_iter.second*(-1)),Primitive::Type::NUMERAL));
				UMinus_ptr uminus_term = new UMinus(term_constant);
				inner_term_list->push_back(uminus_term);
			} else {
				TermConstant_ptr term_constant = new TermConstant(new Primitive(std::to_string(coeff_iter.second),Primitive::Type::NUMERAL));
				inner_term_list->push_back(term_constant);
			}

			Times_ptr times_term = new Times(inner_term_list);
			term_list->push_back(times_term);
		}

		int constant = variable_formulas[iter]->GetConstant();
		if(constant < 0) {
			TermConstant_ptr term_constant = new TermConstant(new Primitive(std::to_string(constant*(-1)),Primitive::Type::NUMERAL));
			UMinus_ptr uminus_term = new UMinus(term_constant);
			term_list->push_back(uminus_term);
		} else {
			TermConstant_ptr term_constant = new TermConstant(new Primitive(std::to_string(constant),Primitive::Type::NUMERAL));
			term_list->push_back(term_constant);
		}
		Plus_ptr plus_term = new Plus(term_list);
		Eq_ptr eq_term = new Eq(new TermConstant(new Primitive("0",Primitive::Type::NUMERAL)),plus_term);

		and_term->term_list->push_back(eq_term);
	}
}

void ImplicationRunner::ResetHeuristicData() {
	if(formula) {
		delete formula;
		formula = nullptr;
	}

	variables_to_expand.clear();
	for(auto iter : variable_formulas) {
		delete iter.second;
		iter.second = nullptr;
	}
	variable_formulas.clear();
}


}  //Vlab
}  //Solver
