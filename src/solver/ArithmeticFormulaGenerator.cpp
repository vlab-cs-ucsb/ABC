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
      has_arithmetic_formula_{false},
      current_component_ { nullptr } {

}

ArithmeticFormulaGenerator::~ArithmeticFormulaGenerator() {
  for (auto& pair : formulas_) {
    delete pair.second;
    pair.second = nullptr;
  }
}

void ArithmeticFormulaGenerator::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts at node: " << node;
  has_arithmetic_formula_ = false;
  visit(node);
  end();
}

void ArithmeticFormulaGenerator::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts at root";
  has_arithmetic_formula_ = false;
  visit(root_);
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
  for (auto& term : * (and_term->term_list)) {
    current_component_ = and_term;
    visit(term);
  }
  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

  current_component_ = nullptr;
  if (not constraint_information_->is_component(and_term)) {
    return;
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *and_term << "@" << and_term;

  bool has_arithmetic_constraint = false;
  for (const auto term : *(and_term->term_list)) {
    auto param_formula = get_term_formula(term);
    if (param_formula not_eq nullptr) {
      if (param_formula->get_number_of_variables() > 0) {
        std::string group_name = get_variable_group_name(and_term, param_formula->get_variable_coefficient_map().begin()->first);
        param_formula->merge_variables(group_formula_[group_name]);
        term_group_map_[term] = group_name;
      }
      has_arithmetic_constraint = true;
    }
  }

  /**
   * If that component is under disjunction we will need to create an automaton for all variables appearing in this term
   * Create a formula for the term and decide on group and variables appear in formula during automata construction
   */
  if (has_arithmetic_constraint) {
    auto and_formula = new ArithmeticFormula();
    and_formula->set_type(ArithmeticFormula::Type::INTERSECT);
    set_term_formula(and_term, and_formula);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *and_term << "@" << and_term;
}


void ArithmeticFormulaGenerator::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;
  for (auto& term : * (or_term->term_list)) {
    current_component_ = or_term;
    visit(term);
  }
  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;

  current_component_ = nullptr;
  if (not constraint_information_->is_component(or_term)) { // a rare case, see dependency slicer
    return;
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *or_term << "@" << or_term;

  bool has_arithmetic_constraint = false;
  for (const auto term : *(or_term->term_list)) {
    auto param_formula = get_term_formula(term);
    if (param_formula not_eq nullptr) {
      if (param_formula->get_number_of_variables() > 0) {
        std::string group_name = get_variable_group_name(or_term, param_formula->get_variable_coefficient_map().begin()->first);
        param_formula->merge_variables(group_formula_[group_name]);
        term_group_map_[term] = group_name;
      }
      has_arithmetic_constraint = true;
    }
  }

  /**
   * If that component is under disjunction we will need to create an automaton for all variables appearing in this term
   * Create a formula for the term and decide on group and variables appear in formula during automata construction
   */
  if (has_arithmetic_constraint) {
    auto and_formula = new ArithmeticFormula();
    and_formula->set_type(ArithmeticFormula::Type::UNION);
    set_term_formula(or_term, and_formula);
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

    if (string_terms_.size() > 0) {
      string_terms_map_[not_term] = string_terms_;
      string_terms_.clear();
    } else {
      auto it = string_terms_map_.find(not_term->term);
      if (it not_eq string_terms_map_.end()) {
        string_terms_map_[not_term] = it->second;
        string_terms_map_.erase(it);
      }
    }
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
  formula->set_type(ArithmeticFormula::Type::EQ);
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
    if (param_formula->is_constant()) {
      multiplicant = multiplicant * param_formula->get_constant();
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

void ArithmeticFormulaGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *eq_term << "@" << eq_term;

  auto left_formula = get_term_formula(eq_term->left_term);
  auto right_formula = get_term_formula(eq_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    auto formula = left_formula->Subtract(right_formula);
    formula->set_type(ArithmeticFormula::Type::EQ);
    delete_term_formula(eq_term->left_term);
    delete_term_formula(eq_term->right_term);
    set_term_formula(eq_term, formula);
    AddIntVariables(current_component_, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[eq_term] = string_terms_;
      string_terms_.clear();
    }
    has_arithmetic_formula_ = true;
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
    formula->set_type(ArithmeticFormula::Type::NOTEQ);
    delete_term_formula(not_eq_term->left_term);
    delete_term_formula(not_eq_term->right_term);
    set_term_formula(not_eq_term, formula);
    AddIntVariables(current_component_, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[not_eq_term] = string_terms_;
      string_terms_.clear();
    }
    has_arithmetic_formula_ = true;
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
    formula->set_type(ArithmeticFormula::Type::GT);
    delete_term_formula(gt_term->left_term);
    delete_term_formula(gt_term->right_term);
    set_term_formula(gt_term, formula);
    AddIntVariables(current_component_, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[gt_term] = string_terms_;
      string_terms_.clear();
    }
    has_arithmetic_formula_ = true;
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
    formula->set_type(ArithmeticFormula::Type::GE);
    delete_term_formula(ge_term->left_term);
    delete_term_formula(ge_term->right_term);
    set_term_formula(ge_term, formula);
    AddIntVariables(current_component_, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[ge_term] = string_terms_;
      string_terms_.clear();
    }
    has_arithmetic_formula_ = true;
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
    formula->set_type(ArithmeticFormula::Type::LT);
    delete_term_formula(lt_term->left_term);
    delete_term_formula(lt_term->right_term);
    set_term_formula(lt_term, formula);
    AddIntVariables(current_component_, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[lt_term] = string_terms_;
      string_terms_.clear();
    }
    has_arithmetic_formula_ = true;
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
    formula->set_type(ArithmeticFormula::Type::LE);
    delete_term_formula(le_term->left_term);
    delete_term_formula(le_term->right_term);
    set_term_formula(le_term, formula);
    AddIntVariables(current_component_, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[le_term] = string_terms_;
      string_terms_.clear();
    }
    has_arithmetic_formula_ = true;
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

  auto formula = new ArithmeticFormula();
  formula->add_variable(name, 1);

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
  formula->add_variable(name, 1);

  set_term_formula(index_of_term, formula);

  string_terms_.push_back(index_of_term);
}

void ArithmeticFormulaGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  std::string name = symbol_table_->get_var_name_for_expression(last_index_of_term, Variable::Type::INT);

  auto formula = new ArithmeticFormula();
  formula->add_variable(name, 1);

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
  formula->add_variable(name, 1);

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

  Variable_ptr variable = symbol_table_->getVariable(qi_term->getVarName());
  if (Variable::Type::INT == variable->getType()) {
    auto formula = new ArithmeticFormula();
    formula->add_variable(variable->getName(), 1);
    formula->set_type(ArithmeticFormula::Type::VAR);
    set_term_formula(qi_term, formula);
  }
}

void ArithmeticFormulaGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  switch (term_constant->getValueType()) {
    case Primitive::Type::NUMERAL: {
      int constant = std::stoi(term_constant->getValue());
      auto formula = new ArithmeticFormula();
      formula->set_constant(constant);
      set_term_formula(term_constant, formula);
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

bool ArithmeticFormulaGenerator::has_arithmetic_formula() {
  return has_arithmetic_formula_;
}

ArithmeticFormula_ptr ArithmeticFormulaGenerator::get_term_formula(Term_ptr term) {
  auto iter = formulas_.find(term);
  if (iter == formulas_.end()) {
    return nullptr;
  }
  return iter->second;
}

bool ArithmeticFormulaGenerator::has_string_terms(Term_ptr term) {
  return (string_terms_map_.find(term) not_eq string_terms_map_.end());
}

std::map<SMT::Term_ptr, SMT::TermList> ArithmeticFormulaGenerator::get_string_terms_map() {
  return string_terms_map_;
}

TermList& ArithmeticFormulaGenerator::get_string_terms_in(Term_ptr term) {
  return string_terms_map_[term];
}

void ArithmeticFormulaGenerator::clear_term_formulas() {
  for (auto& pair : formulas_) {
    delete pair.second;
  }
  formulas_.clear();
}

std::string ArithmeticFormulaGenerator::get_variable_group_name(Term_ptr term, Variable_ptr variable) {
  return get_variable_group_name(term, variable->getName());
}

std::string ArithmeticFormulaGenerator::get_variable_group_name(Term_ptr term, std::string var_name) {
  if (variable_group_table_[term].find(var_name) == variable_group_table_[term].end()) {
    LOG(FATAL)<< "Variable must have a group";
  }
  return variable_group_table_[term][var_name];
}

std::string ArithmeticFormulaGenerator::get_term_group_name(SMT::Term_ptr term) {
  if (term_group_map_.find(term) == term_group_map_.end()) {
    return "";
  }
  return term_group_map_[term];
}

void ArithmeticFormulaGenerator::AddIntVariables(Term_ptr component_term, ArithmeticFormula_ptr formula) {
  std::string group_name;

  variable_group_table_[component_term]; // make sure we have the entry
  auto term_table_entry = variable_group_table_.find(component_term); // optimize multiple access
  auto& variable_group_map = term_table_entry->second; // optimize map entry access for given term

  auto variable_coefficient_map = formula->get_variable_coefficient_map();
  for (const auto& el : variable_coefficient_map) {
    auto it = variable_group_map.find(el.first);
    if (it != variable_group_map.end()) {
      group_name = it->second;
      break;
    }
  }

  // if no group is found at all, create new one
  if (group_name.empty()) {
    group_name = generate_group_name(component_term, variable_coefficient_map.begin()->first);
    group_formula_[group_name] = new ArithmeticFormula();
  }

  auto current_group_formula = group_formula_[group_name];
  // merge each variable's groups together into group_name
  for (const auto& el : variable_coefficient_map) {
    auto it = variable_group_map.find(el.first);
    if (it == variable_group_map.end()) {
      variable_group_map[el.first] = group_name;
      current_group_formula->merge_variables(formula);
    } else if (group_name not_eq it->second) {
      // merge the two groups
      auto other_group_formula = group_formula_[it->second];
      current_group_formula->merge_variables(other_group_formula);
      for (const auto& el : other_group_formula->get_variable_coefficient_map()) {
        variable_group_map[el.first] = group_name;
      }
      group_formula_.erase(it->second);
      delete other_group_formula;
    }
  }
}

std::string ArithmeticFormulaGenerator::generate_group_name(SMT::Term_ptr term, std::string var_name) {
  std::string group_name = symbol_table_->get_var_name_for_node(term, SMT::Variable::Type::INT);
  group_name += var_name;
  return group_name;
}

std::map<std::string, int> ArithmeticFormulaGenerator::get_group_trackmap(std::string name) {
  if (group_formula_.find(name) == group_formula_.end()) {
    DVLOG(VLOG_LEVEL) << "no trackmap for group: " << name;
    return std::map<std::string, int>();
  }
  return std::map<std::string, int>();
}

bool ArithmeticFormulaGenerator::set_term_formula(Term_ptr term, ArithmeticFormula_ptr formula) {
  auto result = formulas_.insert(std::make_pair(term, formula));
  if (result.second == false) {
    LOG(FATAL)<< "formula is already computed for term: " << *term;
  }
  return result.second;
}

void ArithmeticFormulaGenerator::delete_term_formula(Term_ptr term) {
  auto formula = get_term_formula(term);
  if (formula not_eq nullptr) {
    delete formula;
    formulas_.erase(term);
  }
}

} /* namespace Solver */
} /* namespace Vlab */
