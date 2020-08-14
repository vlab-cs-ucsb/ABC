/*
 * StringFormulaGenerator.cpp
 *
 *  Created on: Jan 22, 2017
 *      Author: baki
 */

#include "StringFormulaGenerator.h"

namespace Vlab {
namespace Solver {


using namespace SMT;
using namespace Theory;

const int StringFormulaGenerator::VLOG_LEVEL = 12;

/**
 * Generates atomic string formulae and formulae for boolean connectives
 *
 */
StringFormulaGenerator::StringFormulaGenerator(Script_ptr script, SymbolTable_ptr symbol_table,
                                                       ConstraintInformation_ptr constraint_information)
    : root_(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      has_mixed_constraint_{false} {
}

StringFormulaGenerator::~StringFormulaGenerator() {
  for (auto& el : term_formula_) {
    delete el.second;
  }

  for (auto& el : group_formula_) {
    delete el.second;
  }
}

void StringFormulaGenerator::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "String constraint extraction starts at node: " << node;
  visit(node);
  set_group_mappings();
  end();
}

void StringFormulaGenerator::start() {
  DVLOG(VLOG_LEVEL) << "String constraint extraction starts at root";
  visit(root_);
  set_group_mappings();
  end();
}

void StringFormulaGenerator::end() {
}

void StringFormulaGenerator::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void StringFormulaGenerator::visitCommand(Command_ptr command) {
}

void StringFormulaGenerator::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void StringFormulaGenerator::visitTerm(Term_ptr term) {
}

void StringFormulaGenerator::visitExclamation(Exclamation_ptr exclamation_term) {
}

void StringFormulaGenerator::visitExists(Exists_ptr exists_term) {
}

void StringFormulaGenerator::visitForAll(ForAll_ptr for_all_term) {
}

// TODO add formula generation for let scope
void StringFormulaGenerator::visitLet(Let_ptr let_term) {

}

void StringFormulaGenerator::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;

//<<<<<<< HEAD
//  if (not constraint_information_->is_component(and_term)) {
//    current_group_ = "";
//    has_mixed_constraint_ = false;
//    return;
//  }
//=======
//  LOG(INFO) << "VISIT AND ";

  if (constraint_information_->is_component(and_term)) {
//    LOG(INFO) << "  IS component";
    if(current_group_.empty()) {

      current_group_ = symbol_table_->get_var_name_for_node(and_term, Variable::Type::STRING);
//      LOG(INFO) << "  no current group, creating: " << current_group_;
      subgroups_[current_group_] = std::set<std::string>();
      has_mixed_constraint_ = false;
    } else {
//      LOG(INFO) << "  current group: " << current_group_;
    }
    visit_children_of(and_term);
  } else {
//    LOG(INFO) << "  NOT component";
    for(auto it : *and_term->term_list) {
      current_group_ = "";
      visit(it);
//      std::cin.get();
    }
    return;
  }
//>>>>>>> policy

  StringFormula_ptr temp_formula = new StringFormula();

//  LOG(INFO) << "--- GROUP: " << current_group_ << " ------";
//  LOG(INFO) << "";
  auto subgroups = get_group_subgroups(current_group_);
  for(auto it : subgroups) {
//    LOG(INFO) << "subgroup: " << it;
    auto f = get_group_formula(it);
    temp_formula->MergeVariables(f);
//    LOG(INFO) << "formula: ";
//    for(auto var : f->GetVariableCoefficientMap()) {
//      LOG(INFO) << "  " << var.first;
//    }
  }

  if(temp_formula->GetNumberOfVariables() <= 6) {
    std::string temp_subgroup_name = generate_group_name(and_term,current_group_);
    for(auto &sg_it : subgroups) {
      auto f = get_group_formula(sg_it);

      for(auto var_iter : f->GetVariableCoefficientMap()) {
        variable_group_map_[var_iter.first] = temp_subgroup_name;
      }

      for(auto &term_group_iter : term_group_map_) {
        if(term_group_iter.second == sg_it) {
          term_group_iter.second = temp_subgroup_name;
        }
      }

      auto formula_iter = group_formula_.find(sg_it);
      if(StringFormula::Type::NONE == formula_iter->second->GetType() ||
              StringFormula::Type::VAR == formula_iter->second->GetType()) {
        delete formula_iter->second; formula_iter->second = nullptr;
        group_formula_.erase(formula_iter);
        subgroups_[current_group_].erase(sg_it);
      }
    }

    subgroups_[current_group_].insert(temp_subgroup_name);
    group_formula_[temp_subgroup_name] = temp_formula;
  } else {
    LOG(FATAL) << "Too big!";
    delete temp_formula;
    temp_formula = nullptr;
  }

  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

//  if (not constraint_information_->is_component(and_term)) {
//
//    current_group_ = "";
//    has_mixed_constraint_ = false;
//    return;
//  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *and_term << "@" << and_term;



//  auto group_formula = get_group_formula(current_group_);
//  if (group_formula not_eq nullptr and group_formula->GetNumberOfVariables() > 0) {
//  	LOG(INFO) << "AND HAS FORMULA";
//    auto formula = group_formula->clone();
//    formula->SetType(StringFormula::Type::INTERSECT);
//    set_term_formula(and_term, formula);
//    term_group_map_[and_term] = current_group_;
//    constraint_information_->add_string_constraint(and_term);
//    if (has_mixed_constraint_) {
//      constraint_information_->add_mixed_constraint(and_term);
//    }
//  } else if(has_mixed_constraint_) {
//  	constraint_information_->add_mixed_constraint(and_term);
//  }

  bool has_string_formula = true;
	for (auto term : *and_term->term_list) {
		has_string_formula = constraint_information_->has_string_constraint(term)
				or has_string_formula;
	}

  if(has_string_formula and subgroups_[current_group_].size() > 0 ) {
		term_group_map_[and_term] = current_group_;
		constraint_information_->add_string_constraint(and_term);
	}
  if (has_mixed_constraint_) {
		constraint_information_->add_mixed_constraint(and_term);
	}

  DVLOG(VLOG_LEVEL) << "post visit end: " << *and_term << "@" << and_term;
}


void StringFormulaGenerator::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;

//  LOG(INFO) << "VISIT OR ";
//  LOG(INFO) << "  is component? " << (constraint_information_->is_component(or_term) ? "Y" : "N");
//  LOG(INFO) << "  current_group = " << current_group_;

  if (constraint_information_->is_component(or_term) and current_group_.empty()) {
    current_group_ = symbol_table_->get_var_name_for_node(or_term, Variable::Type::STRING);
    subgroups_[current_group_] = std::set<std::string>();
    has_mixed_constraint_ = false;
  }

	visit_children_of(or_term);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;

  // @deprecated check, all or terms must be a component
  // will be removed after careful testing
//  if (not constraint_information_->is_component(or_term)) {
//    current_group_ = "";
//    has_mixed_constraint_ = false;
//    return;
//  }


  /**
   * If an or term does not have a child that has string formula, but we end up being here:
   * If or term does not have a group formula we are fine.
   * If or term has a group formula, that means or term is under a conjunction where other
   * conjunctive terms has string formula. We don't really need to set a formula for this
   * or term in this case (if has_string_formula var remains false).
   * ! Instead we can let it generate a formula for this or term  and handle this case in
   * String constraint solver by generating a Sigma* automaton, but this will be an
   * unneccessary intersection with other terms.
   */
  bool has_string_formula = true;
  for (auto term : *or_term->term_list) {
    has_string_formula = constraint_information_->has_string_constraint(term)
        or has_string_formula;
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *or_term << "@" << or_term;



  //  auto group_formula = get_group_formula(current_group_);
//  if (has_string_formula and group_formula not_eq nullptr and group_formula->GetNumberOfVariables() > 0) {
//  	LOG(INFO) << "OR HAS FORMULA";
//    auto formula = group_formula->clone();
//    formula->SetType(StringFormula::Type::UNION);
//    set_term_formula(or_term, formula);
//    term_group_map_[or_term] = current_group_;
//    constraint_information_->add_string_constraint(or_term);
//    if (has_mixed_constraint_) {
//      constraint_information_->add_mixed_constraint(or_term);
//    }
//  }

  if(has_string_formula and subgroups_[current_group_].size() > 0 ) {
//    LOG(INFO) << "Subgroup size is good!";
  	term_group_map_[or_term] = current_group_;
    constraint_information_->add_string_constraint(or_term);

//    LOG(INFO) << "  BEFORE ";
//  	for(auto it : group_formula_) {
//  	  LOG(INFO) << it.first << ", " << it.second;
//  	}


//    StringFormula_ptr temp_formula = new StringFormula();
//    std::string temp_name = generate_group_name(or_term,"my_new_group");
//
//    for(auto it : subgroups_[current_group_]) {
//      if(group_formula_.find(it) == group_formula_.end()) {
//        LOG(FATAL) << "Could not find group formula of subgroup!";
//      }
//
//      temp_formula->MergeVariables(group_formula_[it]);
//    }
//
//    if(temp_formula->GetNumberOfVariables() <= 6) {
//      LOG(INFO) << "Deleting subgroups of current group [" << current_group_ << "]";
//      for(auto it : subgroups_[current_group_]) {
//        if(group_formula_.find(it) == group_formula_.end()) {
//          LOG(FATAL) << "Delete failed! Could not find group formula of subgroup!";
//        }
//
//        LOG(INFO) << "Deleting " << it;
//
//        for(auto& term_group_iter : term_group_map_) {
//          if(it == term_group_iter.second) {
//            term_group_iter.second = temp_name;
//          }
//        }
//
//        delete group_formula_[it];
//        group_formula_.erase(it);
//      }
//
//      for(auto it : temp_formula->GetVariableCoefficientMap()) {
//        variable_group_map_[it.first] = temp_name;
//      }
//
//      group_formula_[temp_name] = temp_formula;
//
//      subgroups_[current_group_] = std::set<std::string>();
//      subgroups_[current_group_].insert(temp_name);
//
//      for(auto it : *or_term->term_list) {
//        if(it->type() != Term::Type::AND) term_group_map_[it] = temp_name;
//      }
//
//    } else {
//      LOG(INFO) << "IMPRECISE!";
//      std::cin.get();
//      delete temp_formula;
//      temp_formula = nullptr;
//    }

//  	std::string subgroup_name = "";
//  	StringFormula_ptr subgroup_formula = nullptr;
//
//    for(auto it : subgroups_[current_group_]) {
//      if(subgroup_formula == nullptr) {
//        subgroup_name = it;
//        subgroup_formula = group_formula_[subgroup_name];
////        LOG(INFO) << "SETTING: " << group_formula_[subgroup_name];
//      } else {
////        LOG(INFO) << "DELETEING " << group_formula_[it];
//        subgroup_formula->MergeVariables(group_formula_[it]);
//        delete group_formula_[it];
//        group_formula_.erase(it);
//      }
//    }
//
//
//    subgroups_[current_group_] = std::set<std::string>();
//    subgroups_[current_group_].insert(subgroup_name);
//
//    for(auto it : *or_term->term_list) {
//      if(it->type() != Term::Type::AND) term_group_map_[it] = subgroup_name;
//    }

//    LOG(INFO) << "  AFTER ";
//    for(auto it : group_formula_) {
//  	  LOG(INFO) << it.first << ", " << it.second;
//  	}
//
//  	LOG(INFO) << "In group: " << current_group_;
//  	for(auto it : subgroups_[current_group_]) {
//  	  LOG(INFO) << "  " << it;
//
//
//  	}
//  	std::cin.get();

  }
  if (has_mixed_constraint_) {
		constraint_information_->add_mixed_constraint(or_term);
	}
  DVLOG(VLOG_LEVEL) << "post visit end: " << *or_term << "@" << or_term;
}

void StringFormulaGenerator::visitNot(Not_ptr not_term) {
//  visit_children_of(not_term);
//  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_term << "@" << not_term;
//
//  auto child_formula = get_term_formula(not_term->term);
//
//  if (child_formula not_eq nullptr) {
//    auto formula = child_formula->negate();
//    set_term_formula(not_term, formula);
//    term_group_map_[not_term] = current_group_;
//    if (string_terms_.size() > 0) {
//      string_terms_map_[not_term] = string_terms_;
//      string_terms_.clear();
//      constraint_information_->add_mixed_constraint(not_term);
//      has_mixed_constraint_ = true;
//    } else {
//      auto it = string_terms_map_.find(not_term->term);
//      if (it not_eq string_terms_map_.end()) {
//        string_terms_map_[not_term] = it->second;
//        string_terms_map_.erase(it);
//      }
//    }
//    constraint_information_->add_arithmetic_constraint(not_term);
//    term_group_map_.erase(not_term->term);
//    delete_term_formula(not_term->term);  // safe to call even there is no formula set
//  }
//  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_term << "@" << not_term;
}

void StringFormulaGenerator::visitUMinus(UMinus_ptr u_minus_term) {
}

void StringFormulaGenerator::visitMinus(Minus_ptr minus_term) {
}

void StringFormulaGenerator::visitPlus(Plus_ptr plus_term) {
}

void StringFormulaGenerator::visitTimes(Times_ptr times_term) {
}

void StringFormulaGenerator::visitDiv(Div_ptr div_term) {
}

// TODO make decision based on the formula type
void StringFormulaGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *eq_term << "@" << eq_term;

  auto left_formula = get_term_formula(eq_term->left_term);
  auto right_formula = get_term_formula(eq_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    StringFormula_ptr formula = nullptr;
  	if (StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
      formula = left_formula->clone();
    	formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::EQ);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(eq_term);
    }
  	else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType()
    		  //and right_formula->GetConstant() != constraint_information_->most_common_string
					) {
    	formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::EQ);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(eq_term);
    }
  	else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::VAR == right_formula->GetType()) {
    	formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::EQ);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(eq_term);
    }
    else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::EQ);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(eq_term);
		}
    else if(StringFormula::Type::VAR == right_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
							&& (StringFormula::Type::STRING_CONSTANT == left_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == left_formula->GetType())) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::EQ);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,1);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(eq_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::CHARAT == right_formula->GetType()
							&& (left_formula->GetConstant() == right_formula->GetConstant())) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::EQ_CHARAT);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var, 2);
      constraint_information_->add_string_constraint(eq_term);
    } else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
      formula = left_formula->clone();
      formula->SetConstant(right_formula->GetConstant());
      formula->SetConstant2(left_formula->GetConstant());
      formula->SetType(StringFormula::Type::EQ_CHARAT);
			constraint_information_->add_string_constraint(eq_term);
    } else if(StringFormula::Type::LEN == left_formula->GetType() && StringFormula::Type::LEN == right_formula->GetType()) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::EQ_LEN);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(eq_term);
		} else {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::NONRELATIONAL);
      has_mixed_constraint_ = true;
      constraint_information_->add_mixed_constraint(eq_term);
    }

  	delete_term_formula(eq_term->left_term);
		delete_term_formula(eq_term->right_term);
		set_term_formula(eq_term, formula);
		add_string_variables(current_group_, eq_term);
  } else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
    auto formula = left_formula->clone();
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(eq_term->left_term);
    set_term_formula(eq_term, formula);
    add_string_variables(current_group_, eq_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(eq_term);
  } else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
    auto formula = right_formula->clone();
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(eq_term->left_term);
    set_term_formula(eq_term, formula);
    add_string_variables(current_group_, eq_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(eq_term);
  }

  StringFormula_ptr temp_formula = new StringFormula();

  auto subgroups = get_group_subgroups(current_group_);
  for(auto it : subgroups) {
//    LOG(INFO) << "subgroup: " << it;
    auto f = get_group_formula(it);
    temp_formula->MergeVariables(f);
//    LOG(INFO) << "formula: ";
//    for(auto var : f->GetVariableCoefficientMap()) {
//      LOG(INFO) << "  " << var.first;
//    }
  }

  if(temp_formula->GetNumberOfVariables() <= 6) {
    std::string temp_subgroup_name = generate_group_name(eq_term,current_group_);
    for(auto &sg_it : subgroups) {
      auto f = get_group_formula(sg_it);

      for(auto var_iter : f->GetVariableCoefficientMap()) {
        variable_group_map_[var_iter.first] = temp_subgroup_name;
      }

      for(auto &term_group_iter : term_group_map_) {
        if(term_group_iter.second == sg_it) {
          term_group_iter.second = temp_subgroup_name;
        }
      }

      auto formula_iter = group_formula_.find(sg_it);
      if(StringFormula::Type::NONE == formula_iter->second->GetType() ||
              StringFormula::Type::VAR == formula_iter->second->GetType()) {
        delete formula_iter->second; formula_iter->second = nullptr;
        group_formula_.erase(formula_iter);
        subgroups_[current_group_].erase(sg_it);
      }
    }

    subgroups_[current_group_].insert(temp_subgroup_name);
    group_formula_[temp_subgroup_name] = temp_formula;
  } else {
    LOG(FATAL) << "Too big!";
    delete temp_formula;
    temp_formula = nullptr;
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *eq_term << "@" << eq_term;
}

void StringFormulaGenerator::visitNotEq(NotEq_ptr not_eq_term) {
	visit_children_of(not_eq_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *not_eq_term << "@" << not_eq_term;

	auto left_formula = get_term_formula(not_eq_term->left_term);
	auto right_formula = get_term_formula(not_eq_term->right_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if (StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NOTEQ);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(not_eq_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NOTEQ);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(not_eq_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::VAR == right_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::NOTEQ);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(not_eq_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NOTEQ);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(not_eq_term);
		}	else if(StringFormula::Type::VAR == right_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
							&& (StringFormula::Type::STRING_CONSTANT == left_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == left_formula->GetType())) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::NOTEQ);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,1);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(not_eq_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::CHARAT == right_formula->GetType()
							&& (left_formula->GetConstant() == right_formula->GetConstant())) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::NOTEQ_CHARAT);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var, 2);
      constraint_information_->add_string_constraint(not_eq_term);
    } else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
      formula = left_formula->clone();
      formula->SetConstant(right_formula->GetConstant());
      formula->SetConstant2(left_formula->GetConstant());
      formula->SetType(StringFormula::Type::NOTEQ_CHARAT);
			constraint_information_->add_string_constraint(not_eq_term);
		} else if(StringFormula::Type::LEN == left_formula->GetType() && StringFormula::Type::LEN == right_formula->GetType()) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::NOTEQ_LEN);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(not_eq_term);
		} else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(not_eq_term);
		}
		delete_term_formula(not_eq_term->left_term);
		delete_term_formula(not_eq_term->right_term);
		set_term_formula(not_eq_term, formula);
		add_string_variables(current_group_, not_eq_term);
	} else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(not_eq_term->left_term);
		set_term_formula(not_eq_term, formula);
		add_string_variables(current_group_, not_eq_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(not_eq_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(not_eq_term->left_term);
		set_term_formula(not_eq_term, formula);
		add_string_variables(current_group_, not_eq_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(not_eq_term);
	}

	StringFormula_ptr temp_formula = new StringFormula();

  auto subgroups = get_group_subgroups(current_group_);
  for(auto it : subgroups) {
//    LOG(INFO) << "subgroup: " << it;
    auto f = get_group_formula(it);
    temp_formula->MergeVariables(f);
//    LOG(INFO) << "formula: ";
//    for(auto var : f->GetVariableCoefficientMap()) {
//      LOG(INFO) << "  " << var.first;
//    }
  }

  if(temp_formula->GetNumberOfVariables() <= 6) {
    std::string temp_subgroup_name = generate_group_name(not_eq_term,current_group_);
    for(auto &sg_it : subgroups) {
      auto f = get_group_formula(sg_it);

      for(auto var_iter : f->GetVariableCoefficientMap()) {
        variable_group_map_[var_iter.first] = temp_subgroup_name;
      }

      for(auto &term_group_iter : term_group_map_) {
        if(term_group_iter.second == sg_it) {
          term_group_iter.second = temp_subgroup_name;
        }
      }

      auto formula_iter = group_formula_.find(sg_it);
      if(StringFormula::Type::NONE == formula_iter->second->GetType() ||
              StringFormula::Type::VAR == formula_iter->second->GetType()) {
        delete formula_iter->second; formula_iter->second = nullptr;
        group_formula_.erase(formula_iter);
        subgroups_[current_group_].erase(sg_it);
      }
    }

    subgroups_[current_group_].insert(temp_subgroup_name);
    group_formula_[temp_subgroup_name] = temp_formula;
  } else {
    LOG(FATAL) << "Too big!";
    delete temp_formula;
    temp_formula = nullptr;
  }

	DVLOG(VLOG_LEVEL) << "post visit end: " << *not_eq_term << "@" << not_eq_term;
}

void StringFormulaGenerator::visitGt(Gt_ptr gt_term) {
	visit_children_of(gt_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *gt_term << "@" << gt_term;

	auto left_formula = get_term_formula(gt_term->left_term);
	auto right_formula = get_term_formula(gt_term->right_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if (StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::VAR == right_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetVariableCoefficient(right_var,1);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		}	else if(StringFormula::Type::VAR == right_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
							&& (StringFormula::Type::STRING_CONSTANT == left_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == left_formula->GetType())) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::CHARAT == right_formula->GetType()
									&& (left_formula->GetConstant() == right_formula->GetConstant())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GT_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GT_CHARAT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::CHARAT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GT_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(gt_term);
		} else if(StringFormula::Type::LEN == left_formula->GetType() && StringFormula::Type::LEN == right_formula->GetType()
		          && left_formula->GetNumberOfVariables() > 0 && right_formula->GetNumberOfVariables() > 0) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::GT_LEN);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(gt_term);
		} else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(gt_term);
		}
    delete_term_formula(gt_term->left_term);
		delete_term_formula(gt_term->right_term);
		set_term_formula(gt_term, formula);
		add_string_variables(current_group_, gt_term);

	} else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(gt_term->left_term);
		set_term_formula(gt_term, formula);
		add_string_variables(current_group_, gt_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(gt_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(gt_term->left_term);
		set_term_formula(gt_term, formula);
		add_string_variables(current_group_, gt_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(gt_term);
	}

	DVLOG(VLOG_LEVEL) << "post visit end: " << *gt_term << "@" << gt_term;
}

void StringFormulaGenerator::visitGe(Ge_ptr ge_term) {
	visit_children_of(ge_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *ge_term << "@" << ge_term;

	auto left_formula = get_term_formula(ge_term->left_term);
	auto right_formula = get_term_formula(ge_term->right_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if (StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::VAR == right_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LE);
			auto left_var = left_formula->GetVariableAtIndex(0);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetVariableCoefficient(right_var,1);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LE);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GE);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		}	else if(StringFormula::Type::VAR == right_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
							&& (StringFormula::Type::STRING_CONSTANT == left_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == left_formula->GetType())) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::CHARAT == right_formula->GetType()
											&& (left_formula->GetConstant() == right_formula->GetConstant())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GE_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(ge_term);
		}else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GE_CHARAT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::CHARAT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GE_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(ge_term);
		} else if(StringFormula::Type::LEN == left_formula->GetType() && StringFormula::Type::LEN == right_formula->GetType()
		          && left_formula->GetNumberOfVariables() > 0 && right_formula->GetNumberOfVariables() > 0) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::GE_LEN);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(ge_term);
		}  else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(ge_term);
		}

		delete_term_formula(ge_term->left_term);
		delete_term_formula(ge_term->right_term);
		set_term_formula(ge_term, formula);
		add_string_variables(current_group_, ge_term);
	} else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(ge_term->left_term);
		set_term_formula(ge_term, formula);
		add_string_variables(current_group_, ge_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(ge_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(ge_term->left_term);
		set_term_formula(ge_term, formula);
		add_string_variables(current_group_, ge_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(ge_term);
	}

	DVLOG(VLOG_LEVEL) << "post visit end: " << *ge_term << "@" << ge_term;
}

void StringFormulaGenerator::visitLt(Lt_ptr lt_term) {
	visit_children_of(lt_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *lt_term << "@" << lt_term;

	auto left_formula = get_term_formula(lt_term->left_term);
	auto right_formula = get_term_formula(lt_term->right_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if (StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::VAR == right_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetVariableCoefficient(right_var,1);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		}	else if(StringFormula::Type::VAR == right_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
							&& (StringFormula::Type::STRING_CONSTANT == left_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == left_formula->GetType())) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::CHARAT == right_formula->GetType()
											&& (left_formula->GetConstant() == right_formula->GetConstant())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LT_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LT_CHARAT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::CHARAT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LT_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(lt_term);
		} else if(StringFormula::Type::LEN == left_formula->GetType() && StringFormula::Type::LEN == right_formula->GetType()
		          && left_formula->GetNumberOfVariables() > 0 && right_formula->GetNumberOfVariables() > 0) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::LT_LEN);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(lt_term);
		} else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(lt_term);
		}

		delete_term_formula(lt_term->left_term);
		delete_term_formula(lt_term->right_term);
		set_term_formula(lt_term, formula);
		add_string_variables(current_group_, lt_term);
	} else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(lt_term->left_term);
		set_term_formula(lt_term, formula);
		add_string_variables(current_group_, lt_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(lt_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(lt_term->left_term);
		set_term_formula(lt_term, formula);
		add_string_variables(current_group_, lt_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(lt_term);
	}

	DVLOG(VLOG_LEVEL) << "post visit end: " << *lt_term << "@" << lt_term;
}

void StringFormulaGenerator::visitLe(Le_ptr le_term) {
	visit_children_of(le_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *le_term << "@" << le_term;

	auto left_formula = get_term_formula(le_term->left_term);
	auto right_formula = get_term_formula(le_term->right_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if (StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::VAR == right_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::GE);
			auto left_var = left_formula->GetVariableAtIndex(0);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetVariableCoefficient(right_var,1);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::GE);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,2);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::CONCAT_VAR_CONSTANT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LE);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant(right_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		}	else if(StringFormula::Type::VAR == right_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
							&& (StringFormula::Type::STRING_CONSTANT == left_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == left_formula->GetType())) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LE);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(left_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::CHARAT == right_formula->GetType()
											&& (left_formula->GetConstant() == right_formula->GetConstant())) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LE_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::CHARAT == left_formula->GetType() && StringFormula::Type::STRING_CONSTANT == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::LE_CHARAT);
			auto left_var = left_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(left_var,1);
			formula->SetConstant2(right_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::CHARAT == right_formula->GetType() && StringFormula::Type::STRING_CONSTANT == left_formula->GetType()) {
			formula = right_formula->clone();
			formula->MergeVariables(left_formula);
			formula->SetType(StringFormula::Type::LE_CHARAT);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant2(left_formula->GetConstant());
			constraint_information_->add_string_constraint(le_term);
		} else if(StringFormula::Type::LEN == left_formula->GetType() && StringFormula::Type::LEN == right_formula->GetType()
		          && left_formula->GetNumberOfVariables() > 0 && right_formula->GetNumberOfVariables() > 0) {
      formula = left_formula->clone();
      formula->MergeVariables(right_formula);
      formula->SetType(StringFormula::Type::LE_LEN);
      auto right_var = right_formula->GetVariableAtIndex(0);
      formula->SetVariableCoefficient(right_var,2);
      constraint_information_->add_string_constraint(le_term);
		} else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(le_term);
		}

		delete_term_formula(le_term->left_term);
		delete_term_formula(le_term->right_term);
		set_term_formula(le_term, formula);
		add_string_variables(current_group_, le_term);
	} else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(le_term->left_term);
		set_term_formula(le_term, formula);
		add_string_variables(current_group_, le_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(le_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(le_term->left_term);
		set_term_formula(le_term, formula);
		add_string_variables(current_group_, le_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(le_term);
	}

	DVLOG(VLOG_LEVEL) << "post visit end: " << *le_term << "@" << le_term;
}

void StringFormulaGenerator::visitConcat(Concat_ptr concat_term) {
  visit_children_of(concat_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *concat_term;

  StringFormula_ptr concat_formula = nullptr;
  if(concat_term->term_list->size() == 2 and concat_term->term_list->at(0)->type() == Term::Type::QUALIDENTIFIER
         and concat_term->term_list->at(1)->type() == Term::Type::TERMCONSTANT) {
    auto left_formula = get_term_formula(concat_term->term_list->at(0));
    auto right_formula = get_term_formula(concat_term->term_list->at(1));
    concat_formula = left_formula->clone();
    concat_formula->SetConstant(right_formula->GetConstant());
    concat_formula->SetType(StringFormula::Type::CONCAT_VAR_CONSTANT);
    delete_term_formula(concat_term->term_list->at(0));
    delete_term_formula(concat_term->term_list->at(1));
    constraint_information_->add_string_constraint(concat_term);
  } else {
    for(auto &iter : *concat_term->term_list) {
      if(get_term_formula(iter) == nullptr) {
        continue;
      }

      if(concat_formula == nullptr) {
        concat_formula = get_term_formula(iter)->clone();
      } else {
        concat_formula->MergeVariables(get_term_formula(iter));
        delete_term_formula(iter);
      }
    }

    if(concat_formula == nullptr) {
      concat_formula = new StringFormula();
    }
    concat_formula->SetType(StringFormula::Type::NONRELATIONAL);
    constraint_information_->add_mixed_constraint(concat_term);
  }
  set_term_formula(concat_term,concat_formula);
}


void StringFormulaGenerator::visitIn(In_ptr in_term) {

  visit_children_of(in_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *in_term << "@" << in_term;

  auto left_formula = get_term_formula(in_term->left_term);
  auto right_formula = get_term_formula(in_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(in_term->left_term);
    delete_term_formula(in_term->right_term);
    set_term_formula(in_term, formula);
    add_string_variables(current_group_, in_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(in_term);
  }

  StringFormula_ptr temp_formula = new StringFormula();

  auto subgroups = get_group_subgroups(current_group_);
  for(auto it : subgroups) {
//    LOG(INFO) << "subgroup: " << it;
    auto f = get_group_formula(it);
    temp_formula->MergeVariables(f);
//    LOG(INFO) << "formula: ";
//    for(auto var : f->GetVariableCoefficientMap()) {
//      LOG(INFO) << "  " << var.first;
//    }
  }

  if(temp_formula->GetNumberOfVariables() <= 6) {
    std::string temp_subgroup_name = generate_group_name(in_term,current_group_);
    for(auto &sg_it : subgroups) {
      auto f = get_group_formula(sg_it);

      for(auto var_iter : f->GetVariableCoefficientMap()) {
        variable_group_map_[var_iter.first] = temp_subgroup_name;
      }

      for(auto &term_group_iter : term_group_map_) {
        if(term_group_iter.second == sg_it) {
          term_group_iter.second = temp_subgroup_name;
        }
      }

      auto formula_iter = group_formula_.find(sg_it);
      if(StringFormula::Type::NONE == formula_iter->second->GetType() ||
              StringFormula::Type::VAR == formula_iter->second->GetType()) {
        delete formula_iter->second; formula_iter->second = nullptr;
        group_formula_.erase(formula_iter);
        subgroups_[current_group_].erase(sg_it);
      }
    }

    subgroups_[current_group_].insert(temp_subgroup_name);
    group_formula_[temp_subgroup_name] = temp_formula;
  } else {
    LOG(FATAL) << "Too big!";
    delete temp_formula;
    temp_formula = nullptr;
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *in_term << "@" << in_term;
}


void StringFormulaGenerator::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_in_term << "@" << not_in_term;

  auto left_formula = get_term_formula(not_in_term->left_term);
  auto right_formula = get_term_formula(not_in_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(not_in_term->left_term);
    delete_term_formula(not_in_term->right_term);
    set_term_formula(not_in_term, formula);
    add_string_variables(current_group_, not_in_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(not_in_term);
  }

  StringFormula_ptr temp_formula = new StringFormula();

  auto subgroups = get_group_subgroups(current_group_);
  for(auto it : subgroups) {
//    LOG(INFO) << "subgroup: " << it;
    auto f = get_group_formula(it);
    temp_formula->MergeVariables(f);
//    LOG(INFO) << "formula: ";
//    for(auto var : f->GetVariableCoefficientMap()) {
//      LOG(INFO) << "  " << var.first;
//    }
  }

  if(temp_formula->GetNumberOfVariables() <= 6) {
    std::string temp_subgroup_name = generate_group_name(not_in_term,current_group_);
    for(auto &sg_it : subgroups) {
      auto f = get_group_formula(sg_it);

      for(auto var_iter : f->GetVariableCoefficientMap()) {
        variable_group_map_[var_iter.first] = temp_subgroup_name;
      }

      for(auto &term_group_iter : term_group_map_) {
        if(term_group_iter.second == sg_it) {
          term_group_iter.second = temp_subgroup_name;
        }
      }

      auto formula_iter = group_formula_.find(sg_it);
      if(StringFormula::Type::NONE == formula_iter->second->GetType() ||
              StringFormula::Type::VAR == formula_iter->second->GetType()) {
        delete formula_iter->second; formula_iter->second = nullptr;
        group_formula_.erase(formula_iter);
        subgroups_[current_group_].erase(sg_it);
      }
    }

    subgroups_[current_group_].insert(temp_subgroup_name);
    group_formula_[temp_subgroup_name] = temp_formula;
  } else {
    LOG(FATAL) << "Too big!";
    delete temp_formula;
    temp_formula = nullptr;
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_in_term << "@" << not_in_term;
}

void StringFormulaGenerator::visitLen(Len_ptr len_term) {
  visit(len_term->term);
  auto inner_formula = get_term_formula(len_term->term);
  if(inner_formula != nullptr) {
    auto formula = inner_formula->clone();
    formula->SetType(StringFormula::Type::LEN);
    delete_term_formula(len_term->term);
    set_term_formula(len_term,formula);
    constraint_information_->add_string_constraint(len_term);
  } else {
    // I dont think we need anything here... right?
  }
//  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;
//
//  std::string name = symbol_table_->get_var_name_for_expression(len_term, Variable::Type::INT);
//
//  auto formula = new StringFormula();
//  formula->add_variable(name, 1);
//  formula->SetType(StringFormula::Type::VAR);
//  formula->add_relation_to_mixed_term(name, StringFormula::Type::NONE, len_term);
//
//  set_term_formula(len_term, formula);
//
//  string_terms_.push_back(len_term);
}

void StringFormulaGenerator::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *contains_term << "@" << contains_term;

  auto left_formula = get_term_formula(contains_term->subject_term);
  auto right_formula = get_term_formula(contains_term->search_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(contains_term->subject_term);
    delete_term_formula(contains_term->subject_term);
    set_term_formula(contains_term, formula);
    add_string_variables(current_group_, contains_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(contains_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *contains_term << "@" << contains_term;
}

void StringFormulaGenerator::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_contains_term << "@" << not_contains_term;

  auto left_formula = get_term_formula(not_contains_term->subject_term);
  auto right_formula = get_term_formula(not_contains_term->search_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(not_contains_term->subject_term);
    delete_term_formula(not_contains_term->subject_term);
    set_term_formula(not_contains_term, formula);
    add_string_variables(current_group_, not_contains_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(not_contains_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_contains_term << "@" << not_contains_term;
}

void StringFormulaGenerator::visitBegins(Begins_ptr begins_term) {
	visit_children_of(begins_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *begins_term << "@" << begins_term;

	auto left_formula = get_term_formula(begins_term->subject_term);
	auto right_formula = get_term_formula(begins_term->search_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::BEGINS);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(begins_term);
//<<<<<<< HEAD
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::SUBSTRING == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::BEGINS_SUBSTRING);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			formula->SetConstant2(right_formula->GetConstant2());
			constraint_information_->add_string_constraint(begins_term);
//=======
//    } else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
//						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
//			formula = left_formula->clone();
//			formula->MergeVariables(right_formula);
//			formula->SetType(StringFormula::Type::BEGINS);
//			auto left_var = left_formula->GetVariableAtIndex(0);
//			formula->SetVariableCoefficient(left_var,1);
//			formula->SetConstant(right_formula->GetConstant());
//			constraint_information_->add_string_constraint(begins_term);
//>>>>>>> policy
		} else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(begins_term);
		}
		delete_term_formula(begins_term->subject_term);
		delete_term_formula(begins_term->search_term);
		set_term_formula(begins_term, formula);
		add_string_variables(current_group_, begins_term);
	}	else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(begins_term->subject_term);
		set_term_formula(begins_term, formula);
		add_string_variables(current_group_, begins_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(begins_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(begins_term->search_term);
		set_term_formula(begins_term, formula);
		add_string_variables(current_group_, begins_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(begins_term);
	}

	DVLOG(VLOG_LEVEL) << "post visit end: " << *begins_term << "@" << begins_term;
}

void StringFormulaGenerator::visitNotBegins(NotBegins_ptr not_begins_term) {
	visit_children_of(not_begins_term);
	DVLOG(VLOG_LEVEL) << "post visit start: " << *not_begins_term << "@" << not_begins_term;

	auto left_formula = get_term_formula(not_begins_term->subject_term);
	auto right_formula = get_term_formula(not_begins_term->search_term);

	if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		StringFormula_ptr formula = nullptr;
		if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::VAR == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NOTBEGINS);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			constraint_information_->add_string_constraint(not_begins_term);
//<<<<<<< HEAD
		} else if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::SUBSTRING == right_formula->GetType()) {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NOTBEGINS_SUBSTRING);
			auto right_var = right_formula->GetVariableAtIndex(0);
			formula->SetVariableCoefficient(right_var,2);
			formula->SetConstant(right_formula->GetConstant());
			formula->SetConstant2(right_formula->GetConstant2());
			constraint_information_->add_string_constraint(not_begins_term);
//=======
//    }else if(StringFormula::Type::VAR == left_formula->GetType() //&& right_formula->GetConstant() == constraint_information_->most_common_string
//						&& (StringFormula::Type::STRING_CONSTANT == right_formula->GetType() || StringFormula::Type::REGEX_CONSTANT == right_formula->GetType())) {
//			formula = left_formula->clone();
//			formula->MergeVariables(right_formula);
//			formula->SetType(StringFormula::Type::NOTBEGINS);
//			auto left_var = left_formula->GetVariableAtIndex(0);
//			formula->SetVariableCoefficient(left_var,1);
//			formula->SetConstant(right_formula->GetConstant());
//			constraint_information_->add_string_constraint(not_begins_term);
//
//>>>>>>> policy
		} else {
			formula = left_formula->clone();
			formula->MergeVariables(right_formula);
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			has_mixed_constraint_ = true;
			constraint_information_->add_mixed_constraint(not_begins_term);
		}
		delete_term_formula(not_begins_term->subject_term);
		delete_term_formula(not_begins_term->search_term);
		set_term_formula(not_begins_term, formula);
		add_string_variables(current_group_, not_begins_term);
	}	else if (left_formula not_eq nullptr and left_formula->GetNumberOfVariables() > 0) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(not_begins_term->subject_term);
		set_term_formula(not_begins_term, formula);
		add_string_variables(current_group_, not_begins_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(not_begins_term);
	} else if (right_formula not_eq nullptr and right_formula->GetNumberOfVariables() > 0) {
		auto formula = right_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(not_begins_term->search_term);
		set_term_formula(not_begins_term, formula);
		add_string_variables(current_group_, not_begins_term);
		has_mixed_constraint_ = true;
		constraint_information_->add_mixed_constraint(not_begins_term);
	}

	DVLOG(VLOG_LEVEL) << "post visit end: " << *not_begins_term << "@" << not_begins_term;
}

void StringFormulaGenerator::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *ends_term << "@" << ends_term;

  auto left_formula = get_term_formula(ends_term->subject_term);
  auto right_formula = get_term_formula(ends_term->search_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(ends_term->subject_term);
    delete_term_formula(ends_term->subject_term);
    set_term_formula(ends_term, formula);
    add_string_variables(current_group_, ends_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(ends_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *ends_term << "@" << ends_term;
}

void StringFormulaGenerator::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_ends_term << "@" << not_ends_term;

  auto left_formula = get_term_formula(not_ends_term->subject_term);
  auto right_formula = get_term_formula(not_ends_term->search_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(not_ends_term->subject_term);
    delete_term_formula(not_ends_term->subject_term);
    set_term_formula(not_ends_term, formula);
    add_string_variables(current_group_, not_ends_term);
    has_mixed_constraint_ = true;
    constraint_information_->add_mixed_constraint(not_ends_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_ends_term << "@" << not_ends_term;
}

void StringFormulaGenerator::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *index_of_term << "@" << index_of_term;

  auto left_formula = get_term_formula(index_of_term->subject_term);
  auto right_formula = get_term_formula(index_of_term->search_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(index_of_term->subject_term);
    delete_term_formula(index_of_term->subject_term);
    set_term_formula(index_of_term, formula);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *index_of_term << "@" << index_of_term;
}

void StringFormulaGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *last_index_of_term << "@" << last_index_of_term;

  auto left_formula = get_term_formula(last_index_of_term->subject_term);
  auto right_formula = get_term_formula(last_index_of_term->search_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->clone();
    formula->MergeVariables(right_formula);
    formula->SetType(StringFormula::Type::NONRELATIONAL);
    delete_term_formula(last_index_of_term->subject_term);
    delete_term_formula(last_index_of_term->subject_term);
    set_term_formula(last_index_of_term, formula);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *last_index_of_term << "@" << last_index_of_term;
}


void StringFormulaGenerator::visitCharAt(CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *char_at_term << "@" << char_at_term;

  auto left_formula = get_term_formula(char_at_term->subject_term);
	auto right_formula = get_term_formula(char_at_term->index_term);
  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
		if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::INTEGER_CONSTANT == right_formula->GetType()) {
			// can maybe support, assume we can going forward
			auto formula = left_formula->clone();
			formula->SetType(StringFormula::Type::CHARAT);
			formula->SetConstant(right_formula->GetConstant());
			delete_term_formula(char_at_term->subject_term);
			delete_term_formula(char_at_term->index_term);
			set_term_formula(char_at_term,formula);
			constraint_information_->add_string_constraint(char_at_term);
		} else {
			// not supported yet, just delete both formulas and solve non-relational
			auto formula = left_formula->clone();
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			delete_term_formula(char_at_term->subject_term);
			delete_term_formula(char_at_term->index_term);
			set_term_formula(char_at_term, formula);
			constraint_information_->add_mixed_constraint(char_at_term);
		}
  } else if(left_formula not_eq nullptr) {
		auto formula = left_formula->clone();
		formula->SetType(StringFormula::Type::NONRELATIONAL);
		delete_term_formula(char_at_term->subject_term);
		set_term_formula(char_at_term,formula);
		constraint_information_->add_mixed_constraint(char_at_term);
	} else {
//		auto formula = right_formula->clone();
//		formula->SetType(StringFormula::Type::NONRELATIONAL);
//		delete_term_formula(char_at_term->index_term);
//		set_term_formula(char_at_term,formula);
//		constraint_information_->add_mixed_constraint(char_at_term);
	}

  DVLOG(VLOG_LEVEL) << "post visit end: " << *char_at_term << "@" << char_at_term;
}

void StringFormulaGenerator::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *sub_string_term << "@" << sub_string_term;

  auto left_formula = get_term_formula(sub_string_term->subject_term);
  auto start_index_formula = get_term_formula(sub_string_term->start_index_term);
  auto end_index_formula = get_term_formula(sub_string_term->end_index_term);

  if (left_formula not_eq nullptr and start_index_formula not_eq nullptr and end_index_formula not_eq nullptr) {
		if(StringFormula::Type::VAR == left_formula->GetType() and StringFormula::Type::INTEGER_CONSTANT == start_index_formula->GetType()
																and start_index_formula->GetConstant() == "0"
																and StringFormula::Type::INTEGER_CONSTANT == end_index_formula->GetType()) {
			auto formula = left_formula->clone();
			formula->SetType(StringFormula::Type::SUBSTRING);
			formula->SetConstant(start_index_formula->GetConstant());
			formula->SetConstant2(end_index_formula->GetConstant());
			set_term_formula(sub_string_term,formula);
			delete_term_formula(sub_string_term->subject_term);
			delete_term_formula(sub_string_term->start_index_term);
			delete_term_formula(sub_string_term->end_index_term);
			constraint_information_->add_string_constraint(sub_string_term);
		} else {
			auto formula = left_formula->clone();
			formula->SetType(StringFormula::Type::NONRELATIONAL);
			delete_term_formula(sub_string_term->subject_term);
			set_term_formula(sub_string_term, formula);
		}
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *sub_string_term << "@" << sub_string_term;
}

void StringFormulaGenerator::visitToUpper(ToUpper_ptr to_upper_term) {
}

void StringFormulaGenerator::visitToLower(ToLower_ptr to_lower_term) {
}

void StringFormulaGenerator::visitTrim(Trim_ptr trim_term) {
}

void StringFormulaGenerator::visitToString(ToString_ptr to_string_term) {
}

void StringFormulaGenerator::visitToInt(ToInt_ptr to_int_term) {
//  DVLOG(VLOG_LEVEL) << "visit: " << *to_int_term;
//
//  std::string name = symbol_table_->get_var_name_for_expression(to_int_term, Variable::Type::INT);
//
//  auto formula = new StringFormula();
//  formula->add_variable(name, 1);
//  formula->SetType(StringFormula::Type::VAR);
//  formula->add_relation_to_mixed_term(name, StringFormula::Type::NONE, to_int_term);
//
//  set_term_formula(to_int_term, formula);
//
//  string_terms_.push_back(to_int_term);
}

void StringFormulaGenerator::visitReplace(Replace_ptr replace_term) {
}

void StringFormulaGenerator::visitCount(Count_ptr count_term) {
}

void StringFormulaGenerator::visitIte(Ite_ptr ite_term) {
}

void StringFormulaGenerator::visitReConcat(ReConcat_ptr re_concat_term) {
}

void StringFormulaGenerator::visitReUnion(ReUnion_ptr re_union_term) {
}

void StringFormulaGenerator::visitReInter(ReInter_ptr re_inter_term) {
}

void StringFormulaGenerator::visitReStar(ReStar_ptr re_star_term) {
}

void StringFormulaGenerator::visitRePlus(RePlus_ptr re_plus_term) {
}

void StringFormulaGenerator::visitReOpt(ReOpt_ptr re_opt_term) {
}

void StringFormulaGenerator::visitReLoop(ReLoop_ptr re_loop_term) {
}

void StringFormulaGenerator::visitToRegex(ToRegex_ptr to_regex_term) {
}

void StringFormulaGenerator::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void StringFormulaGenerator::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void StringFormulaGenerator::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  Variable_ptr variable = symbol_table_->get_variable(qi_term->getVarName());
  if (Variable::Type::STRING == variable->getType()) {
    auto formula = new StringFormula();
    formula->AddVariable(variable->getName(), 1);
    formula->SetType(StringFormula::Type::VAR);
    set_term_formula(qi_term, formula);
  }
}

void StringFormulaGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  switch (term_constant->getValueType()) {
    case Primitive::Type::STRING: {
      auto formula = new StringFormula();
      formula->SetType(StringFormula::Type::STRING_CONSTANT);
      formula->SetConstant(term_constant->getValue());
      set_term_formula(term_constant, formula);
      break;
    }
    case Primitive::Type::REGEX: {
      auto formula = new StringFormula();
      formula->SetType(StringFormula::Type::REGEX_CONSTANT);
      formula->SetConstant(term_constant->getValue());
      set_term_formula(term_constant, formula);
      break;
    }
		case Primitive::Type::NUMERAL: {
      auto formula = new StringFormula();
			formula->SetType(StringFormula::Type::INTEGER_CONSTANT);
			formula->SetConstant(term_constant->getValue());
			set_term_formula(term_constant, formula);
      break;
    }
    default:
      break;
  }
}

void StringFormulaGenerator::visitIdentifier(Identifier_ptr identifier) {
}

void StringFormulaGenerator::visitPrimitive(Primitive_ptr primitive) {
}

void StringFormulaGenerator::visitTVariable(TVariable_ptr t_variable) {
}

void StringFormulaGenerator::visitTBool(TBool_ptr t_bool) {
}

void StringFormulaGenerator::visitTInt(TInt_ptr t_int) {
}

void StringFormulaGenerator::visitTString(TString_ptr t_string) {
}

void StringFormulaGenerator::visitVariable(Variable_ptr variable) {
}

void StringFormulaGenerator::visitSort(Sort_ptr sort) {
}

void StringFormulaGenerator::visitAttribute(Attribute_ptr attribute) {
}

void StringFormulaGenerator::visitSortedVar(SortedVar_ptr sorted_var) {
}

void StringFormulaGenerator::visitVarBinding(VarBinding_ptr var_binding) {
}

StringFormula_ptr StringFormulaGenerator::get_term_formula(Term_ptr term) {
  auto it = term_formula_.find(term);
  if (it == term_formula_.end()) {
    return nullptr;
  }
  return it->second;
}

StringFormula_ptr StringFormulaGenerator::get_group_formula(std::string group_name) {
  auto it = group_formula_.find(group_name);
  if (it == group_formula_.end()) {
    return nullptr;
  }
  return it->second;
}

bool StringFormulaGenerator::has_integer_terms(Term_ptr term) {
  return (integer_terms_map_.find(term) not_eq integer_terms_map_.end());
}

std::map<Term_ptr, TermList> StringFormulaGenerator::get_integer_terms_map() {
  return integer_terms_map_;
}

TermList& StringFormulaGenerator::get_integer_terms_in(Term_ptr term) {
  return integer_terms_map_[term];
}

void StringFormulaGenerator::clear_term_formula(Term_ptr term) {
  auto it = term_formula_.find(term);
  if (it != term_formula_.end()) {
    delete it->second;
    term_formula_.erase(it);
    //term_group_map_.erase(term);
  }
}

void StringFormulaGenerator::clear_term_formulas() {
  for (auto& pair : term_formula_) {
    delete pair.second;
  }
  term_formula_.clear();
}

std::string StringFormulaGenerator::get_term_group_name(Term_ptr term) {
  auto it = term_group_map_.find(term);
  if (it not_eq term_group_map_.end()) {
    return it->second;
  }
  return "";
}

std::string StringFormulaGenerator::get_variable_group_name(Variable_ptr variable) {
  std::string var_name = variable->getName();
  if(variable_group_map_.find(var_name) == variable_group_map_.end()) {
    DVLOG(VLOG_LEVEL) << var_name << " has no group";
    return "";
  }
  return variable_group_map_[var_name];
}

std::set<std::string> StringFormulaGenerator::get_group_subgroups(std::string group_name) {
  if(subgroups_.find(group_name) == subgroups_.end()) {
		return std::set<std::string>();
	}
	return subgroups_[group_name];
}


void StringFormulaGenerator::add_string_variables(std::string group_name, Term_ptr term) {
	auto formula = get_term_formula(term);
	if(StringFormula::Type::NONRELATIONAL == formula->GetType()) {
		// just make sure each variable has a group, and if not, create a lone group for it
		auto variables = formula->GetVariableCoefficientMap();
		for(auto &var : variables) {
			if(variable_group_map_.find(var.first) == variable_group_map_.end()) {
				std::string var_group = var.first + generate_group_name(term,var.first);
				StringFormula_ptr var_formula = new StringFormula();
				var_formula->SetType(StringFormula::Type::VAR);
				var_formula->AddVariable(var.first,1);
				variable_group_map_[var.first] = var_group;
				group_formula_[var_group] = var_formula;
				subgroups_[group_name].insert(var_group);
			}
		}
		clear_term_formula(term);
	} else {
		std::string start_group;
		StringFormula_ptr group_formula = nullptr;
		std::vector<std::string> groups_to_be_removed;
		auto variables = formula->GetVariableCoefficientMap();
		// get a starting group for the variable list
		for(auto &var : variables) {
			if(variable_group_map_.find(var.first) != variable_group_map_.end()) {
				start_group = variable_group_map_[var.first];
				group_formula = group_formula_[start_group];
				if(group_formula == nullptr) {
					LOG(FATAL) << "BAD";
				}
				break;
			}
		}
		// if no group is found, create one
		if (start_group.empty()) {
		  //LOG(INFO) << "NO START GROUP";
			start_group = generate_group_name(term,variables.begin()->first);
			group_formula = new StringFormula();
			group_formula_[start_group] = group_formula;
			subgroups_[group_name].insert(start_group);
		}
		if(group_formula == nullptr) {
			LOG(FATAL) << "BAD";
		}
		// merge each variable's groups together into start group

		//TODO: Update Automata here!?

		for(auto &var : variables) {
			if(variable_group_map_.find(var.first) == variable_group_map_.end()) {
				// variable has no group, add it
				variable_group_map_[var.first] = start_group;
				group_formula->AddVariable(var.first,0);
			} else if(variable_group_map_[var.first] != start_group) {
				// merge the two groups
				std::string var_group = variable_group_map_[var.first];
				auto var_group_formula = group_formula_[var_group];
				group_formula->MergeVariables(var_group_formula);
				for(auto &var_group_iter : variable_group_map_) {
					if(var_group_iter.second == var_group) {
						var_group_iter.second = start_group;
					}
				}
				for(auto &var_group_iter : term_group_map_) {
					if(var_group_iter.second == var_group) {
						var_group_iter.second = start_group;
					}
				}
				// keep relational formulas so we can construct them; they will get destroyed afterwards.
				auto formula_iter = group_formula_.find(var_group);
				if(StringFormula::Type::NONE == formula_iter->second->GetType() ||
								StringFormula::Type::VAR == formula_iter->second->GetType()) {
					delete formula_iter->second; formula_iter->second = nullptr;
					group_formula_.erase(formula_iter);
					subgroups_[group_name].erase(var_group);
				}
			}
		}
		term_group_map_[term] = start_group;
	}
}

std::string StringFormulaGenerator::generate_group_name(SMT::Term_ptr term, std::string var_name) {
  std::string group_name = symbol_table_->get_var_name_for_node(term,SMT::Variable::Type::STRING);
  group_name += var_name;
  return group_name;
}

bool StringFormulaGenerator::set_term_formula(Term_ptr term, StringFormula_ptr formula) {
  auto result = term_formula_.insert(std::make_pair(term, formula));
  if (result.second == false) {
    for(auto it : formula->GetVariableCoefficientMap()) {
      LOG(INFO) << it.first << "," << it.second;
    }
    LOG(FATAL)<< "formula is already computed for term: " << *term;
  }
  return result.second;
}

void StringFormulaGenerator::delete_term_formula(Term_ptr term) {
  auto formula = get_term_formula(term);
  if (formula not_eq nullptr) {
    delete formula;
    term_formula_.erase(term);
  }
}

void StringFormulaGenerator::set_group_mappings() {
//  LOG(INFO) << "# subgroups = " << subgroups_.size();
//  for(auto it : subgroups_) {
//    LOG(INFO) << "  " << it.first;
//  }

  DVLOG(VLOG_LEVEL)<< "start setting string group for components";
	//TODO: Is this necessary?
  //for (auto& el : term_group_map_) {
  	// only subgroups have formulas
//<<<<<<< HEAD
    //if(subgroups_.find(el.second) == subgroups_.end()) {
    //	term_formula_[el.first]->MergeVariables(group_formula_[el.second]);
    //}
  //}

  std::map<Variable_ptr,Value_ptr> var_vals_to_add;
  std::vector<Variable_ptr> var_vals_to_erase;

  for (auto& el: subgroups_) {

    symbol_table_->add_variable(new Variable(el.first, Variable::Type::NONE));
  }
  // get values of previous solve (if any)
  auto  &variable_values = symbol_table_->get_values_at_scope(symbol_table_->top_scope());
  // update groups and their values in symbol table
  for(auto group_iter : group_formula_) {
    //LOG(INFO) << "Group: " << group_iter.first;
    if(symbol_table_->get_variable_unsafe(group_iter.first) == nullptr) {
      symbol_table_->add_variable(new Variable(group_iter.first, Variable::Type::NONE));
    }

    std::set<Variable_ptr> previous_group_variables;
    for (const auto& var_entry : group_iter.second->GetVariableCoefficientMap()) {
      //LOG(INFO) << "--> " << var_entry.first;
      Variable_ptr variable = symbol_table_->get_variable(var_entry.first);
      Variable_ptr group_variable = symbol_table_->get_group_variable_of(variable);

      // if group variable in variable_values, then a previous value was computed;
      if(variable_values.find(group_variable) != variable_values.end()) {
        previous_group_variables.insert(group_variable);
        if(true) {
          group_iter.second->MergeVariables(variable_values[group_variable]->getStringAutomaton()->GetFormula());
          for(auto vv : variable_values[group_variable]->getStringAutomaton()->GetFormula()->GetVariableCoefficientMap()) {
            symbol_table_->set_variable_group_mapping(vv.first,group_iter.first);
          }
        }
      }
      // update variable group mapping in symbol table
      symbol_table_->set_variable_group_mapping(var_entry.first, group_iter.first);
    }


//    if(Option::Solver::SUB_FORMULA_CACHING && previous_group_variables.empty()) continue;

    //LOG(INFO) << "# previous group vars: " << previous_group_variables.size();
    StringAutomaton_ptr initial_auto = StringAutomaton::MakeAnyStringUnaligned(group_iter.second->clone());
		initial_auto->GetFormula()->SetType(StringFormula::Type::NA);
    for(auto previous_group: previous_group_variables) {
      //LOG(INFO) << "--> previous group = " << previous_group->getName();
      StringAutomaton_ptr previous_group_auto = variable_values[previous_group]->getStringAutomaton();
      StringAutomaton_ptr remapped_auto = previous_group_auto->ChangeIndicesMap(group_iter.second->clone());
      StringAutomaton_ptr temp_auto = initial_auto->Intersect(remapped_auto);
	    //temp_auto->GetFormula()->SetType(StringFormula::Type::NA);
      //temp_auto->inspectAuto(false,true);
      delete initial_auto;
      delete remapped_auto;
      initial_auto = temp_auto;

      // remove previous variable value from symbol table's value map
//      delete variable_values[previous_group];
//      variable_values[previous_group] = nullptr;
//      variable_values.erase(previous_group);
      var_vals_to_erase.push_back(previous_group);
//=======
//    if(subgroups_.find(el.second) == subgroups_.end()) {
//    	//LOG(INFO) << "group: " << el.second;
//    	term_formula_[el.first]->MergeVariables(group_formula_[el.second]);
//    }
//    //LOG(INFO) << "";
//  }
////  LOG(INFO) << 1;
//  for (auto& el: subgroups_) {
//  	symbol_table_->add_variable(new Variable(el.first, Variable::Type::NONE));
//  }
////  LOG(INFO) << 2;
//  // add a variable entry to symbol table for each group
//  // define a variable mapping for a group
//  for (auto& el : group_formula_) {
////  	LOG(INFO) << "Formula : " << el.first;
////  	LOG(INFO) << "  has size: " << el.second->GetVariableCoefficientMap().size();
//    symbol_table_->add_variable(new Variable(el.first, Variable::Type::NONE));
//    auto init_val = StringAutomaton::MakeAnyStringUnaligned(el.second->clone());
////    LOG(INFO) << el.second->GetNumberOfVariables();
//    Value_ptr val = new Value(init_val);
//    symbol_table_->push_scope(root_);
//    symbol_table_->set_value(el.first,val);
//    delete val;
//		symbol_table_->pop_scope();
//
//    //LOG(INFO) << "Group " << el.first << " Initial Value: " << symbol_table_->get_value_at_scope(root_,symbol_table_->get_variable(el.first));
//    for (const auto& var_entry : el.second->GetVariableCoefficientMap()) {
//    	//val->getStringAutomaton()->inspectAuto(false,true);
////    	LOG(INFO) << "Setting Mapping: " << var_entry.first << " -> " << el.first;
//      symbol_table_->add_variable_group_mapping(var_entry.first, el.first);
////      LOG(INFO) << "-- " << var_entry.first;
//>>>>>>> policy
    }

    Value_ptr initial_value = new Value(initial_auto);
    auto group_iter_var = symbol_table_->get_variable(group_iter.first);
    //symbol_table_->set_value(group_iter.first,initial_value);
//    variable_values[group_iter_var] = initial_value;
    var_vals_to_add[group_iter_var] = initial_value;
//    delete initial_value;
  }

  // make sure no data race
  while(symbol_table_->AreValuesLocked()) std::this_thread::yield();

  for(auto it : var_vals_to_erase) {
    delete variable_values[it];
    variable_values[it] = nullptr;
    variable_values.erase(it);
  }

  for(auto it : var_vals_to_add) {
    symbol_table_->set_value(it.first,it.second, false);
  }

  DVLOG(VLOG_LEVEL) << "done setting string group for components";
//  std::cin.get();
}

} /* namespace Solver */
} /* namespace Vlab */
