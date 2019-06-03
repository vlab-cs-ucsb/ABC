/*
 * ArithmeticFormulaGenerator.cpp
 *
 *  Created on: Oct 19, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "ArithmeticFormulaGenerator.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int ArithmeticFormulaGenerator::VLOG_LEVEL = 12;

/**
 * Generates a coefficient vector for all int and str->int terms that are in same component
 *
 */
ArithmeticFormulaGenerator::ArithmeticFormulaGenerator(Script_ptr script, SymbolTable_ptr symbol_table,
                                                       ConstraintInformation_ptr constraint_information)
    : root_(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      has_mixed_constraint_{false} {

  no_visit_or = false;


//  current_group_ = symbol_table_->get_var_name_for_node(root_, Variable::Type::INT);
//  if(symbol_table_->get_variable_unsafe(current_group_) == nullptr) {
//    symbol_table_->add_variable(new Variable(current_group_, Variable::Type::NONE));
//  } else {
//    LOG(FATAL) << "Should not already have group var";
//  }
//
//  auto start = std::chrono::steady_clock::now();
//  auto end = std::chrono::steady_clock::now();
//  diff = end-start;

//  subgroups_[current_group_] = std::set<std::string>();
//
//	auto variables = symbol_table_->get_variables();
//	for(auto& iter : variables) {
//	  auto group_var = symbol_table_->get_group_variable_of(iter.second);
//	  if(iter.second->getType() != Variable::Type::INT or group_var == iter.second) {
//	    continue;
//	  }
//
//  	auto group_value = symbol_table_->get_value(iter.first);
//  	auto group_formula = group_value->getBinaryIntAutomaton()->GetFormula();
//
//  	if(group_formula != nullptr) {
//  		subgroups_[current_group_].insert(group_var->getName());
//  		variable_group_map_[iter.second->getName()] = group_var->getName();
//  		if(group_formula_.find(group_var->getName()) == group_formula_.end()) {
//				group_formula_[group_var->getName()] = group_formula->clone();
//				group_formula_[group_var->getName()]->SetType(ArithmeticFormula::Type::NONE);
//			}
//  	}
//	}

}

ArithmeticFormulaGenerator::~ArithmeticFormulaGenerator() {
  for (auto& el : term_formula_) {
    delete el.second;
  }

  for (auto& el : group_formula_) {
    delete el.second;
  }
}

void ArithmeticFormulaGenerator::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts at node: " << node;
//  auto start = std::chrono::steady_clock::now();

  visit(node);
  set_group_mappings();
  end();

//  auto end2 = std::chrono::steady_clock::now();
//  diff += end2-start;
}

void ArithmeticFormulaGenerator::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts at root";
  visit(root_);
  set_group_mappings();
  end();
}

void ArithmeticFormulaGenerator::end() {
}

void ArithmeticFormulaGenerator::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void ArithmeticFormulaGenerator::visitCommand(Command_ptr command) {
}

void ArithmeticFormulaGenerator::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void ArithmeticFormulaGenerator::visitTerm(Term_ptr term) {
}

void ArithmeticFormulaGenerator::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ArithmeticFormulaGenerator::visitExists(Exists_ptr exists_term) {
}

void ArithmeticFormulaGenerator::visitForAll(ForAll_ptr for_all_term) {
}

// TODO add formula generation for let scope
void ArithmeticFormulaGenerator::visitLet(Let_ptr let_term) {

}

void ArithmeticFormulaGenerator::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;
  if (constraint_information_->is_component(and_term) and current_group_.empty()) {
    current_group_ = symbol_table_->get_var_name_for_node(and_term, Variable::Type::INT);
    subgroups_[current_group_] = std::set<std::string>();
    has_mixed_constraint_ = false;

  }
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

  if (not constraint_information_->is_component(and_term)) {
    current_group_ = "";
    has_mixed_constraint_ = false;
    return;
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *and_term << "@" << and_term;

//  auto group_formula = get_group_formula(current_group_);
//  if (group_formula not_eq nullptr and group_formula->GetNumberOfVariables() > 0) {
//    auto formula = group_formula->clone();
//    formula->SetType(ArithmeticFormula::Type::INTERSECT);
//    set_term_formula(and_term, formula);
//    term_group_map_[and_term] = current_group_;
//    constraint_information_->add_arithmetic_constraint(and_term);
//    if (has_mixed_constraint_) {
//      constraint_information_->add_mixed_constraint(and_term);
//    }
//  }
//  if(Option::Solver::SUB_FORMULA_CACHING) {
//    if(subgroups_[current_group_].size() > 0 ) {
//      term_group_map_[and_term] = current_group_;
//      constraint_information_->add_arithmetic_constraint(and_term);
//    }
//  } else {
    if(subgroups_[current_group_].size() > 0 ) {
      term_group_map_[and_term] = current_group_;
      constraint_information_->add_arithmetic_constraint(and_term);
    }
//  }

  if (has_mixed_constraint_) {
		constraint_information_->add_mixed_constraint(and_term);
	}

  DVLOG(VLOG_LEVEL) << "post visit end: " << *and_term << "@" << and_term;
}


void ArithmeticFormulaGenerator::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;
  if (constraint_information_->is_component(or_term) and current_group_.empty()) {
    current_group_ = symbol_table_->get_var_name_for_node(or_term, Variable::Type::INT);
    subgroups_[current_group_] = std::set<std::string>();
    has_mixed_constraint_ = false;
  }

  if(!no_visit_or)
  visit_children_of(or_term);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;

  // @deprecated check, all or terms must be a component
  // will be removed after careful testing
  if (not constraint_information_->is_component(or_term)) {
    current_group_ = "";
    has_mixed_constraint_ = false;
    return;
  }

  /**
   * If an or term does not have a child that has arithmetic formula, but we end up being here:
   * If or term does not have a group formula we are fine.
   * If or term has a group formula, that means or term is under a conjunction where other
   * conjunctive terms has arithmetic formula. We don't really need to set a formula for this
   * or term in this case (if has_arithmetic_formula var remains false).
   * ! Instead we can let it generate a formula for this or term  and handle this case in
   * Arithmetic constraint solver by generating a Sigma* automaton, but this will be an
   * unneccessary intersection with other terms.
   */
  bool has_arithmetic_formula = false;
  for (auto term : *or_term->term_list) {
    has_arithmetic_formula = constraint_information_->has_arithmetic_constraint(term) or has_arithmetic_formula;
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *or_term << "@" << or_term;
//  auto group_formula = get_group_formula(current_group_);
//  if (has_arithmetic_formula and group_formula not_eq nullptr and group_formula->GetNumberOfVariables() > 0) {
//    auto formula = group_formula->clone();
//    formula->SetType(ArithmeticFormula::Type::UNION);
//    set_term_formula(or_term, formula);
//    term_group_map_[or_term] = current_group_;
//    constraint_information_->add_arithmetic_constraint(or_term);
//    if (has_mixed_constraint_) {
//      constraint_information_->add_mixed_constraint(or_term);
//    }
//  }
  if(has_arithmetic_formula and subgroups_[current_group_].size() > 0 ) {
		term_group_map_[or_term] = current_group_;
		constraint_information_->add_arithmetic_constraint(or_term);
	}
  if (has_mixed_constraint_) {
		constraint_information_->add_mixed_constraint(or_term);
	}

  DVLOG(VLOG_LEVEL) << "post visit end: " << *or_term << "@" << or_term;
}

void ArithmeticFormulaGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_term << "@" << not_term;

  auto child_formula = get_term_formula(not_term->term);

  if (child_formula not_eq nullptr) {
    auto formula = child_formula->negate();
    set_term_formula(not_term, formula);
    term_group_map_[not_term] = term_group_map_[not_term->term];
    if (string_terms_.size() > 0) {
      string_terms_map_[not_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(not_term);
      has_mixed_constraint_ = true;
    } else {
      auto it = string_terms_map_.find(not_term->term);
      if (it not_eq string_terms_map_.end()) {
        string_terms_map_[not_term] = it->second;
        string_terms_map_.erase(it);
      }
    }
    constraint_information_->add_arithmetic_constraint(not_term);
    term_group_map_.erase(not_term->term);
    delete_term_formula(not_term->term);  // safe to call even there is no formula set
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_term << "@" << not_term;
}

void ArithmeticFormulaGenerator::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *u_minus_term << "@" << u_minus_term;

  auto child_formula = get_term_formula(u_minus_term->term);
  auto formula = child_formula->Multiply(-1);
  delete_term_formula(u_minus_term->term);
  set_term_formula(u_minus_term, formula);

  DVLOG(VLOG_LEVEL) << "post visit end: " << *u_minus_term << "@" << u_minus_term;
}

void ArithmeticFormulaGenerator::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *minus_term << "@" << minus_term;

  auto left_formula = get_term_formula(minus_term->left_term);
  auto right_formula = get_term_formula(minus_term->right_term);
  auto formula = left_formula->Subtract(right_formula);
  formula->SetType(ArithmeticFormula::Type::EQ);
  delete_term_formula(minus_term->left_term);
  delete_term_formula(minus_term->right_term);
  set_term_formula(minus_term, formula);

  DVLOG(VLOG_LEVEL) << "post visit end: " << *minus_term << "@" << minus_term;
}

void ArithmeticFormulaGenerator::visitPlus(Plus_ptr plus_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *plus_term << "@" << plus_term;
  ArithmeticFormula_ptr formula = nullptr,
      plus_formula = nullptr,
      param_formula = nullptr;
  for (auto term_ptr : *(plus_term->term_list)) {
    visit(term_ptr);
    param_formula = get_term_formula(term_ptr);
    if (formula == nullptr) {
      formula = param_formula->clone();
    } else {
      plus_formula = formula->Add(param_formula);
      delete formula;
      formula = plus_formula;
    }
    delete_term_formula(term_ptr);
  }
  set_term_formula(plus_term, formula);

  DVLOG(VLOG_LEVEL) << "visit children end: " << *plus_term << "@" << plus_term;
}

/**
 * All the parameters must be a constant integer except one.
 */
void ArithmeticFormulaGenerator::visitTimes(Times_ptr times_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *times_term << "@" << times_term;
  int multiplicant = 1;
  ArithmeticFormula_ptr times_formula = nullptr;
  for (auto term_ptr : *(times_term->term_list)) {
    visit(term_ptr);
    auto param_formula = get_term_formula(term_ptr);
    if (param_formula->IsConstant()) {
      multiplicant = multiplicant * param_formula->GetConstant();
    } else if (times_formula == nullptr) {
      times_formula = param_formula->clone();
    } else {
      LOG(FATAL)<< "Does not support non-linear multiplication";
    }
    delete_term_formula(term_ptr);
  }
  auto formula = times_formula->Multiply(multiplicant);
  delete times_formula;
  set_term_formula(times_term, formula);

  DVLOG(VLOG_LEVEL) << "visit children end: " << *times_term << "@" << times_term;
}

void ArithmeticFormulaGenerator::visitDiv(Div_ptr div_term) {
  LOG(FATAL) << "implement me";
}

void ArithmeticFormulaGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *eq_term << "@" << eq_term;

  auto left_formula = get_term_formula(eq_term->left_term);
  auto right_formula = get_term_formula(eq_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->SetType(ArithmeticFormula::Type::EQ);
    delete_term_formula(eq_term->left_term);
    delete_term_formula(eq_term->right_term);
    set_term_formula(eq_term, formula);
    add_int_variables(current_group_, eq_term);
    if (string_terms_.size() > 0) {
      formula->UpdateMixedConstraintRelations();
      string_terms_map_[eq_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(eq_term);
      has_mixed_constraint_ = true;

    }
    constraint_information_->add_arithmetic_constraint(eq_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *eq_term << "@" << eq_term;
}

void ArithmeticFormulaGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_eq_term << "@" << not_eq_term;

  auto left_formula = get_term_formula(not_eq_term->left_term);
  auto right_formula = get_term_formula(not_eq_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->SetType(ArithmeticFormula::Type::NOTEQ);
    delete_term_formula(not_eq_term->left_term);
    delete_term_formula(not_eq_term->right_term);
    set_term_formula(not_eq_term, formula);
    add_int_variables(current_group_, not_eq_term);
    if (string_terms_.size() > 0) {
      string_terms_map_[not_eq_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(not_eq_term);
      has_mixed_constraint_ = true;
    }
    constraint_information_->add_arithmetic_constraint(not_eq_term);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_eq_term << "@" << not_eq_term;
}

void ArithmeticFormulaGenerator::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *gt_term << "@" << gt_term;

  auto left_formula = get_term_formula(gt_term->left_term);
  auto right_formula = get_term_formula(gt_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->SetType(ArithmeticFormula::Type::GT);
    delete_term_formula(gt_term->left_term);
    delete_term_formula(gt_term->right_term);
    set_term_formula(gt_term, formula);
    add_int_variables(current_group_, gt_term);
    if (string_terms_.size() > 0) {
      string_terms_map_[gt_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(gt_term);
      has_mixed_constraint_ = true;
    }
    constraint_information_->add_arithmetic_constraint(gt_term);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *gt_term << "@" << gt_term;
}

void ArithmeticFormulaGenerator::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *ge_term << "@" << ge_term;

  auto left_formula = get_term_formula(ge_term->left_term);
  auto right_formula = get_term_formula(ge_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->SetType(ArithmeticFormula::Type::GE);
    delete_term_formula(ge_term->left_term);
    delete_term_formula(ge_term->right_term);
    set_term_formula(ge_term, formula);
    add_int_variables(current_group_, ge_term);
    if (string_terms_.size() > 0) {
      string_terms_map_[ge_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(ge_term);
      has_mixed_constraint_ = true;
    }
    constraint_information_->add_arithmetic_constraint(ge_term);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *ge_term << "@" << ge_term;
}

void ArithmeticFormulaGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *lt_term << "@" << lt_term;

  auto left_formula = get_term_formula(lt_term->left_term);
  auto right_formula = get_term_formula(lt_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->SetType(ArithmeticFormula::Type::LT);
    delete_term_formula(lt_term->left_term);
    delete_term_formula(lt_term->right_term);
    set_term_formula(lt_term, formula);
    add_int_variables(current_group_, lt_term);
    if (string_terms_.size() > 0) {
      string_terms_map_[lt_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(lt_term);
      has_mixed_constraint_ = true;
    }
    constraint_information_->add_arithmetic_constraint(lt_term);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *lt_term << "@" << lt_term;
}

void ArithmeticFormulaGenerator::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *le_term << "@" << le_term;

  auto left_formula = get_term_formula(le_term->left_term);
  auto right_formula = get_term_formula(le_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->SetType(ArithmeticFormula::Type::LE);
    delete_term_formula(le_term->left_term);
    delete_term_formula(le_term->right_term);
    set_term_formula(le_term, formula);
    add_int_variables(current_group_, le_term);
    if (string_terms_.size() > 0) {
      string_terms_map_[le_term] = string_terms_;
      string_terms_.clear();
      constraint_information_->add_mixed_constraint(le_term);
      has_mixed_constraint_ = true;
    }
    constraint_information_->add_arithmetic_constraint(le_term);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *le_term << "@" << le_term;
}

void ArithmeticFormulaGenerator::visitConcat(Concat_ptr concat_term) {
}


void ArithmeticFormulaGenerator::visitIn(In_ptr in_term) {
}


void ArithmeticFormulaGenerator::visitNotIn(NotIn_ptr not_in_term) {
}

void ArithmeticFormulaGenerator::visitLen(Len_ptr len_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;

  std::string name = symbol_table_->get_var_name_for_expression(len_term, Variable::Type::INT);
  // not sure if this is a good idea, but it works for now...
  symbol_table_->add_variable(new Variable(name,Variable::Type::INT));

  auto formula = new ArithmeticFormula();
  formula->AddVariable(name, 1);
  formula->SetType(ArithmeticFormula::Type::VAR);
  formula->AddRelationToMixedTerm(name, ArithmeticFormula::Type::NONE, len_term);

  set_term_formula(len_term, formula);

  string_terms_.push_back(len_term);
}

void ArithmeticFormulaGenerator::visitContains(Contains_ptr contains_term) {
}

void ArithmeticFormulaGenerator::visitNotContains(NotContains_ptr not_contains_term) {
}

void ArithmeticFormulaGenerator::visitBegins(Begins_ptr begins_term) {
}

void ArithmeticFormulaGenerator::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void ArithmeticFormulaGenerator::visitEnds(Ends_ptr ends_term) {
}

void ArithmeticFormulaGenerator::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void ArithmeticFormulaGenerator::visitIndexOf(IndexOf_ptr index_of_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *index_of_term;

  std::string name = symbol_table_->get_var_name_for_expression(index_of_term, Variable::Type::INT);

  auto formula = new ArithmeticFormula();
  formula->AddVariable(name, 1);
  formula->SetType(ArithmeticFormula::Type::VAR);
  formula->AddRelationToMixedTerm(name, ArithmeticFormula::Type::NONE, index_of_term);

  set_term_formula(index_of_term, formula);

  string_terms_.push_back(index_of_term);
}

void ArithmeticFormulaGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  std::string name = symbol_table_->get_var_name_for_expression(last_index_of_term, Variable::Type::INT);

  auto formula = new ArithmeticFormula();
  formula->AddVariable(name, 1);
  formula->SetType(ArithmeticFormula::Type::VAR);
  formula->AddRelationToMixedTerm(name, ArithmeticFormula::Type::NONE, last_index_of_term);

  set_term_formula(last_index_of_term, formula);

  string_terms_.push_back(last_index_of_term);
}

void ArithmeticFormulaGenerator::visitCharAt(CharAt_ptr char_at_term) {
}

void ArithmeticFormulaGenerator::visitSubString(SubString_ptr sub_string_term) {
}

void ArithmeticFormulaGenerator::visitToUpper(ToUpper_ptr to_upper_term) {
}

void ArithmeticFormulaGenerator::visitToLower(ToLower_ptr to_lower_term) {
}

void ArithmeticFormulaGenerator::visitTrim(Trim_ptr trim_term) {
}

void ArithmeticFormulaGenerator::visitToString(ToString_ptr to_string_term) {
}

void ArithmeticFormulaGenerator::visitToInt(ToInt_ptr to_int_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *to_int_term;

  std::string name = symbol_table_->get_var_name_for_expression(to_int_term, Variable::Type::INT);

  auto formula = new ArithmeticFormula();
  formula->AddVariable(name, 1);
  formula->SetType(ArithmeticFormula::Type::VAR);
  formula->AddRelationToMixedTerm(name, ArithmeticFormula::Type::NONE, to_int_term);

  set_term_formula(to_int_term, formula);

  string_terms_.push_back(to_int_term);
}

void ArithmeticFormulaGenerator::visitReplace(Replace_ptr replace_term) {
}

void ArithmeticFormulaGenerator::visitCount(Count_ptr count_term) {
}

void ArithmeticFormulaGenerator::visitIte(Ite_ptr ite_term) {
}

void ArithmeticFormulaGenerator::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ArithmeticFormulaGenerator::visitReUnion(ReUnion_ptr re_union_term) {
}

void ArithmeticFormulaGenerator::visitReInter(ReInter_ptr re_inter_term) {
}

void ArithmeticFormulaGenerator::visitReStar(ReStar_ptr re_star_term) {
}

void ArithmeticFormulaGenerator::visitRePlus(RePlus_ptr re_plus_term) {
}

void ArithmeticFormulaGenerator::visitReOpt(ReOpt_ptr re_opt_term) {
}

void ArithmeticFormulaGenerator::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ArithmeticFormulaGenerator::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void ArithmeticFormulaGenerator::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ArithmeticFormulaGenerator::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  Variable_ptr variable = symbol_table_->get_variable(qi_term->getVarName());
  if (Variable::Type::INT == variable->getType()) {
    auto formula = new ArithmeticFormula();
    formula->AddVariable(variable->getName(), 1);
    formula->SetType(ArithmeticFormula::Type::VAR);
    set_term_formula(qi_term, formula);
  } else if(Variable::Type::BOOL == variable->getType()) {
		auto formula = new ArithmeticFormula();
		formula->AddBoolean(variable->getName());
		formula->AddVariable(variable->getName(), 1);
		formula->SetType(ArithmeticFormula::Type::BOOL);
		set_term_formula(qi_term, formula);
		add_int_variables(current_group_,qi_term);
	}
}

void ArithmeticFormulaGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  switch (term_constant->getValueType()) {
    case Primitive::Type::NUMERAL: {
      int constant = std::stoi(term_constant->getValue());
      //if(constant <= 300) {
        auto formula = new ArithmeticFormula();
        formula->SetConstant(constant);
        set_term_formula(term_constant, formula);
      //}
      break;
    }
    default:
      break;
  }
}

void ArithmeticFormulaGenerator::visitIdentifier(Identifier_ptr identifier) {
}

void ArithmeticFormulaGenerator::visitPrimitive(Primitive_ptr primitive) {
}

void ArithmeticFormulaGenerator::visitTVariable(TVariable_ptr t_variable) {
}

void ArithmeticFormulaGenerator::visitTBool(TBool_ptr t_bool) {
}

void ArithmeticFormulaGenerator::visitTInt(TInt_ptr t_int) {
}

void ArithmeticFormulaGenerator::visitTString(TString_ptr t_string) {
}

void ArithmeticFormulaGenerator::visitVariable(Variable_ptr variable) {
}

void ArithmeticFormulaGenerator::visitSort(Sort_ptr sort) {
}

void ArithmeticFormulaGenerator::visitAttribute(Attribute_ptr attribute) {
}

void ArithmeticFormulaGenerator::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ArithmeticFormulaGenerator::visitVarBinding(VarBinding_ptr var_binding) {
}

ArithmeticFormula_ptr ArithmeticFormulaGenerator::get_term_formula(Term_ptr term) {
  auto it = term_formula_.find(term);
  if (it == term_formula_.end()) {
    return nullptr;
  }
  return it->second;
}

ArithmeticFormula_ptr ArithmeticFormulaGenerator::get_group_formula(std::string group_name) {
  auto it = group_formula_.find(group_name);
  if (it == group_formula_.end()) {
    return nullptr;
  }
  return it->second;
}

bool ArithmeticFormulaGenerator::has_string_terms(Term_ptr term) {
  return (string_terms_map_.find(term) not_eq string_terms_map_.end());
}

std::map<Term_ptr, TermList> ArithmeticFormulaGenerator::get_string_terms_map() {
  return string_terms_map_;
}

TermList& ArithmeticFormulaGenerator::get_string_terms_in(Term_ptr term) {
  return string_terms_map_[term];
}

void ArithmeticFormulaGenerator::clear_term_formula(Term_ptr term) {
  auto it = term_formula_.find(term);
  if (it != term_formula_.end()) {
    delete it->second;
    term_formula_.erase(it);
//    if(Option::Solver::SUB_FORMULA_CACHING) {
//      term_group_map_.erase(term);
//    }
  }
}

void ArithmeticFormulaGenerator::clear_term_formulas() {
  for (auto& pair : term_formula_) {
    delete pair.second;
  }
  term_formula_.clear();
}

std::string ArithmeticFormulaGenerator::get_term_group_name(Term_ptr term) {
  auto it = term_group_map_.find(term);
  if (it not_eq term_group_map_.end()) {
    return it->second;
  }
  return "";
}

std::string ArithmeticFormulaGenerator::get_variable_group_name(Variable_ptr variable) {
  std::string var_name = variable->getName();
  if(variable_group_map_.find(var_name) == variable_group_map_.end()) {
    DVLOG(VLOG_LEVEL) << var_name << " has no group";
    return "";
  }
  return variable_group_map_[var_name];
}

std::set<std::string> ArithmeticFormulaGenerator::get_group_subgroups(std::string group_name) {
	if(subgroups_.find(group_name) == subgroups_.end()) {
		return std::set<std::string>();
	}
	return subgroups_[group_name];
}

void ArithmeticFormulaGenerator::add_int_variables(std::string group_name, Term_ptr term) {
//  ArithmeticFormula_ptr group_formula = nullptr;
//  auto it = group_formula_.find(group_name);
//  if (it == group_formula_.end()) {
//    group_formula = new ArithmeticFormula();
//    group_formula_[group_name] = group_formula;
//  } else {
//    group_formula = it->second;
//  }
//  auto formula = get_term_formula(term);
//  group_formula->MergeVariables(formula);
//  term_group_map_[term] = group_name;
	auto formula = get_term_formula(term);

	std::string start_group;
	ArithmeticFormula_ptr group_formula = nullptr;
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

//	if(subgroups_[group_name].size() > 0) {
//	  start_group = *subgroups_[group_name].begin();
//	  group_formula = group_formula_[start_group];
//	}

	// if no group is found, create one
	if (start_group.empty()) {
//	  LOG(INFO) << "Empty start group";
		start_group = generate_group_name(term,variables.begin()->first);
		group_formula = new ArithmeticFormula();
		group_formula_[start_group] = group_formula;
		subgroups_[group_name].insert(start_group);
	}
	if(group_formula == nullptr) {
		LOG(FATAL) << "BAD";
	}
	// merge each variable's groups together into start group
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
			if(ArithmeticFormula::Type::NONE == formula_iter->second->GetType()) {
				delete formula_iter->second; formula_iter->second = nullptr;
				group_formula_.erase(formula_iter);
				subgroups_[group_name].erase(var_group);
			}
		}
	}
	term_group_map_[term] = start_group;
}

std::string ArithmeticFormulaGenerator::generate_group_name(SMT::Term_ptr term, std::string var_name) {
  std::string group_name = symbol_table_->get_var_name_for_node(term,SMT::Variable::Type::INT);
  group_name += var_name;
  return group_name;
}

bool ArithmeticFormulaGenerator::set_term_formula(Term_ptr term, ArithmeticFormula_ptr formula) {
  auto result = term_formula_.insert(std::make_pair(term, formula));
  if (result.second == false) {
    LOG(FATAL)<< "formula is already computed for term: " << *term;
  }
  return result.second;
}

void ArithmeticFormulaGenerator::delete_term_formula(Term_ptr term) {
  auto formula = get_term_formula(term);
  if (formula not_eq nullptr) {
    delete formula;
    term_formula_.erase(term);
//    term_group_map_.erase(term);
  }
}

void ArithmeticFormulaGenerator::set_group_mappings() {
/*
  for (auto& el : term_group_map_) {
  	// only subgroups have formulas
    if(subgroups_.find(el.second) == subgroups_.end()) {
    	term_formula_[el.first]->MergeVariables(group_formula_[el.second]);
    }
  }
*/


  std::map<Variable_ptr,Value_ptr> var_vals_to_add;
  std::vector<Variable_ptr> var_vals_to_erase;

  for (auto& el: subgroups_) {

    symbol_table_->add_variable(new Variable(el.first, Variable::Type::NONE));
  }
  // get values of previous solve (if any)
  auto  &variable_values = symbol_table_->get_values_at_scope(symbol_table_->top_scope());
  // update groups and their values in symbol table
  for(auto group_iter : group_formula_) {
//    LOG(INFO) << "Group: " << group_iter.first;
    if(symbol_table_->get_variable_unsafe(group_iter.first) == nullptr) {
      symbol_table_->add_variable(new Variable(group_iter.first, Variable::Type::NONE));
    }

    std::set<Variable_ptr> previous_group_variables;
    for (const auto& var_entry : group_iter.second->GetVariableCoefficientMap()) {
//      LOG(INFO) << "--> " << var_entry.first;
      Variable_ptr variable = symbol_table_->get_variable(var_entry.first);
      Variable_ptr group_variable = symbol_table_->get_group_variable_of(variable);

      // if group variable in variable_values, then a previous value was computed;
      if(variable_values.find(group_variable) != variable_values.end()) {
        previous_group_variables.insert(group_variable);
        if(true) {
          group_iter.second->MergeVariables(variable_values[group_variable]->getBinaryIntAutomaton()->GetFormula());
          for(auto vv : variable_values[group_variable]->getBinaryIntAutomaton()->GetFormula()->GetVariableCoefficientMap()) {
            symbol_table_->set_variable_group_mapping(vv.first,group_iter.first);
          }
        }
      }
      // update variable group mapping in symbol table
      symbol_table_->set_variable_group_mapping(var_entry.first, group_iter.first);
//      LOG(INFO) << "setting mapping " << var_entry.first << " -> " << group_iter.first;
    }

//    LOG(INFO) << "# previous group vars: " << previous_group_variables.size();

    BinaryIntAutomaton_ptr initial_auto = BinaryIntAutomaton::MakeAnyInt(group_iter.second->clone(),not Option::Solver::USE_SIGNED_INTEGERS);
//	  initial_auto->GetFormula()->SetType(StringFormula::Type::NA);
    for(auto previous_group: previous_group_variables) {
//      if(variable_values.find(previous_group) == variable_values.end() || variable_values[previous_group] == nullptr) {
//        LOG(INFO) << "FOUND NOTHING";
//      } else {
//        LOG(INFO) << "Found value for " << previous_group->getName() << " with type " << variable_values[previous_group]->str();
//      }
//      LOG(INFO) << "--> previous group = " << previous_group->getName();
      BinaryIntAutomaton_ptr previous_group_auto = variable_values[previous_group]->getBinaryIntAutomaton();
      BinaryIntAutomaton_ptr remapped_auto = previous_group_auto->ChangeIndicesMap(group_iter.second->clone());

      BinaryIntAutomaton_ptr temp_auto = initial_auto->Intersect(remapped_auto);
//	    LOG(INFO) << previous_group_auto->getId();
//	    LOG(INFO) << remapped_auto->getId();
//	    LOG(INFO) << initial_auto->getId();
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
//      LOG(INFO) << "gonna erase " << previous_group->getName() << " with id " << previous_group_auto->getId();
    }

    Value_ptr initial_value = new Value(initial_auto);
    auto group_iter_var = symbol_table_->get_variable(group_iter.first);
    //symbol_table_->set_value(group_iter.first,initial_value);
//    variable_values[group_iter_var] = initial_value;
    var_vals_to_add[group_iter_var] = initial_value;
//    delete initial_value;
  }

  // make sure no data race

//  LOG(INFO) << "before";
while(symbol_table_->values_lock_) std::this_thread::yield();
  for(auto it : var_vals_to_erase) {
    delete variable_values[it];
    variable_values[it] = nullptr;
    variable_values.erase(it);
  }
//  LOG(INFO) << "after";

  for(auto it : var_vals_to_add) {
    symbol_table_->set_value(it.first,it.second, false);
  }

//  auto start = std::chrono::steady_clock::now();
//  DVLOG(VLOG_LEVEL)<< "start setting int group for components";
//  for (auto& el : term_group_map_) {
//    if(term_formula_.find(el.first) != term_formula_.end()) {
//      term_formula_[el.first]->MergeVariables(group_formula_[el.second]);
//      group_formula_[el.second]->MergeVariables(term_formula_[el.first]);
//    }
//  }
//
//
////  // add a variable entry to symbol table for each group
////  // define a variable mapping for a group
////  for (auto& el : group_formula_) {
////    symbol_table_->add_variable(new Variable(el.first, Variable::Type::NONE));
////    for (const auto& var_entry : el.second->GetVariableCoefficientMap()) {
////      symbol_table_->add_variable_group_mapping(var_entry.first, el.first);
////    }
////  }
//
//  // TODO: Do we really need this?
////  for (auto& el : term_group_map_) {
////		LOG(INFO) << *el.first << "@" << el.first;
////		// only subgroups have formulas
////		if(subgroups_.find(el.second) == subgroups_.end()) {
////			LOG(INFO) << "group: " << el.second;
////			term_formula_[el.first]->MergeVariables(group_formula_[el.second]);
////		}
////		LOG(INFO) << "";
////	}
//
////	for (auto& el: subgroups_) {
////		symbol_table_->add_variable(new Variable(el.first, Variable::Type::NONE));
////	}
//	// add a variable entry to symbol table for each group
////LOG(INFO) << 1;
//
//
//  // define a variable mapping for a group
//
//  if(group_formula_.size() > 1) {
//    LOG(FATAL) << "Failed invariant for having a single binary auto";
//  }
//
//
////LOG(INFO) << 2;
//	for (auto group_iter : group_formula_) {
////    if(symbol_table_->get_variable_unsafe(group_iter.first) == nullptr) {
////      symbol_table_->add_variable(new Variable(group_iter.first, Variable::Type::NONE));
////    }
//
//
//    std::set<Variable_ptr> previous_group_variables;
//    Variable_ptr previous_var = nullptr;
////    LOG(INFO) << 3;
//    for (const auto& var_entry : group_iter.second->GetVariableCoefficientMap()) {
////      LOG(INFO) << "--> " << var_entry.first;
////      Variable_ptr variable = symbol_table_->get_variable(var_entry.first);
////      Variable_ptr group_variable = symbol_table_->get_group_variable_of(variable);
////
////      // if group variable in variable_values, then a previous value was computed;
////      if(variable_values.find(group_variable) != variable_values.end()) {
////        previous_group_variables.insert(group_variable);
////        previous_var = group_variable;
////      }
//      // update variable group mapping in symbol table
//      symbol_table_->set_variable_group_mapping(var_entry.first, current_group_);
//    }
//
//    if(previous_group_variables.size() > 1) {
//      LOG(FATAL) << "Should only be one binary auto for all int variables";
//    }
//  }
//
//	auto  &variable_values = symbol_table_->get_values_at_scope(symbol_table_->top_scope());
//  auto previous_var = symbol_table_->get_variable(current_group_);
//  while(symbol_table_->values_lock_) std::this_thread::yield();
//  if(variable_values.find(previous_var) != variable_values.end()) {
//    if(previous_var != nullptr) {
//      auto previous_group_auto = variable_values[previous_var]->getBinaryIntAutomaton();
//      auto remapped_auto = previous_group_auto->ChangeIndicesMap(group_formula_[current_group_]->clone(),false);
//      variable_values[previous_var]->setData(remapped_auto);
//    }
//  }
////	auto end = std::chrono::steady_clock::now();
////  diff += end-start;
//  DVLOG(VLOG_LEVEL)<< "end setting int group for components";
}

} /* namespace Solver */
} /* namespace Vlab */
