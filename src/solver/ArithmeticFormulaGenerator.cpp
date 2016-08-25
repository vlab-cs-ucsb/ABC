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
#include "options/Solver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int ArithmeticFormulaGenerator::VLOG_LEVEL = 12;

/**
 * Generates a coefficient vector for all int and str->int terms that are in same component
 *
 */
ArithmeticFormulaGenerator::ArithmeticFormulaGenerator( Script_ptr script, SymbolTable_ptr symbol_table, ConstraintInformation_ptr constraint_information) :
        root_ (script), symbol_table_ (symbol_table), constraint_information_(constraint_information) {

}

ArithmeticFormulaGenerator::~ArithmeticFormulaGenerator() {
  for (auto& pair : formulas_) {
    delete pair.second;
    pair.second = nullptr;
  }
}

void ArithmeticFormulaGenerator::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts at node: " << node;
  visit(node);
  end();
}

void ArithmeticFormulaGenerator::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts at root";
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

/**
 * Right most formula that contains arithmetic constraint has all variable coefficients,
 * update others based on that
 */
void ArithmeticFormulaGenerator::visitAnd(And_ptr and_term) {
  current_term_ = and_term;
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;

  if (not constraint_information_->is_component(and_term)) {
    return;
  }

  ArithmeticFormula_ptr param_formula = nullptr;
  for (auto& term : *(and_term->term_list)) {
    param_formula = get_term_formula(term);
    if (param_formula not_eq nullptr) {
      if(term->type() == Term::Type::QUALIDENTIFIER) {
        delete_term_formula(term);
        continue;
      }

      // POSSIBLE SOURCE OF ERROR FOR NON-DNF VERSIONS!!!
      std::string group_name = get_variable_group_name(current_term_,param_formula->get_var_coeff_map().begin()->first);
      if(group_name.empty()) {
        std::string group_name = get_variable_group_name(current_term_, symbol_table_->getVariable(param_formula->get_var_coeff_map().begin()->first));
      }
      term_group_map[term] = group_name;
      VariableTrackMap trackmap = get_group_trackmap(group_name);
      param_formula->set_variable_trackmap(trackmap);
    }
  }
}

/**
 * Right most formula that contains arithmetic constraint has all variable coefficients,
 * update others based on that
 */
void ArithmeticFormulaGenerator::visitOr(Or_ptr or_term) {
  current_term_ = or_term;
  for (auto &term : *(or_term->term_list)) {
    visit(term);
  }
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
}

void ArithmeticFormulaGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  ArithmeticFormula_ptr formula = nullptr, child_formula = nullptr;

  child_formula = get_term_formula(not_term->term);

  if (child_formula not_eq nullptr and child_formula->get_number_of_variables() > 0) {
    formula = child_formula->NegateOperation();
    set_term_formula(not_term, formula);
  }

  delete_term_formula(not_term->term); // safe to call even there is no formula set

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
}

void ArithmeticFormulaGenerator::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *u_minus_term;
  ArithmeticFormula_ptr formula = nullptr, child_formula = nullptr;

  child_formula = get_term_formula(u_minus_term->term);

  if (child_formula not_eq nullptr) {
    formula = child_formula->Multiply(-1);
    delete_term_formula(u_minus_term->term);
    set_term_formula(u_minus_term, formula);
  }
}

void ArithmeticFormulaGenerator::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *minus_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(minus_term->left_term);
  right_formula = get_term_formula(minus_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    formula = left_formula->Subtract(right_formula);
    formula->set_type(ArithmeticFormula::Type::EQ);
    delete_term_formula(minus_term->left_term);
    delete_term_formula(minus_term->right_term);
    set_term_formula(minus_term, formula);
  }
}

void ArithmeticFormulaGenerator::visitPlus(Plus_ptr plus_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *plus_term;
  ArithmeticFormula_ptr formula = nullptr, plus_formula = nullptr, param_formula = nullptr;
  for (auto& term_ptr : *(plus_term->term_list)) {
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
}

/**
 * All the parameters must be a constant integer except one.
 */
void ArithmeticFormulaGenerator::visitTimes(Times_ptr times_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *times_term;
  int multiplicant = 1;
  ArithmeticFormula_ptr formula = nullptr, times_formula = nullptr, param_formula = nullptr;
  for (auto& term_ptr : *(times_term->term_list)) {
    visit(term_ptr);
    param_formula = get_term_formula(term_ptr);
    if (param_formula->is_constant()) {
      multiplicant = multiplicant * param_formula->get_constant();
    } else if (times_formula == nullptr) {
      times_formula = param_formula->clone();
    } else {
      LOG(FATAL)<< "Does not support non-linear multiplication";
    }
    delete_term_formula(term_ptr);
  }

  formula = times_formula->Multiply(multiplicant);
  delete times_formula; times_formula = nullptr;
  set_term_formula(times_term, formula);
}

void ArithmeticFormulaGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(eq_term->left_term);
  right_formula = get_term_formula(eq_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    formula = left_formula->Subtract(right_formula);
    formula->set_type(ArithmeticFormula::Type::EQ);
    delete_term_formula(eq_term->left_term);
    delete_term_formula(eq_term->right_term);
    if (formula->get_number_of_variables() > 0) {
      set_term_formula(eq_term, formula);
      add_int_variables(current_term_,formula->get_var_coeff_map());
      if (string_terms_.size() > 0) {
        string_terms_map_[eq_term] = string_terms_;
      }
    }
  }
  string_terms_.clear();
}


void ArithmeticFormulaGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(not_eq_term->left_term);
  right_formula = get_term_formula(not_eq_term->right_term);

  if (left_formula not_eq nullptr and right_formula not_eq nullptr) {
    formula = left_formula->Subtract(right_formula);
    formula->set_type(ArithmeticFormula::Type::NOTEQ);
    delete_term_formula(not_eq_term->left_term);
    delete_term_formula(not_eq_term->right_term);
    if (formula->get_number_of_variables() > 0) {
      set_term_formula(not_eq_term, formula);
      add_int_variables(current_term_,formula->get_var_coeff_map());
      if (string_terms_.size() > 0) {
        string_terms_map_[not_eq_term] = string_terms_;
      }
    }
  }
  string_terms_.clear();
}

void ArithmeticFormulaGenerator::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(gt_term->left_term);
  right_formula = get_term_formula(gt_term->right_term);

  formula = left_formula->Subtract(right_formula);
  formula->set_type(ArithmeticFormula::Type::GT);
  delete_term_formula(gt_term->left_term);
  delete_term_formula(gt_term->right_term);

  if (formula->get_number_of_variables() > 0) {
    set_term_formula(gt_term, formula);
    add_int_variables(current_term_,formula->get_var_coeff_map());
    if (string_terms_.size() > 0) {
      string_terms_map_[gt_term] = string_terms_;
      string_terms_.clear();
    }
  }
}

void ArithmeticFormulaGenerator::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(ge_term->left_term);
  right_formula = get_term_formula(ge_term->right_term);

  formula = left_formula->Subtract(right_formula);
  formula->set_type(ArithmeticFormula::Type::GE);
  delete_term_formula(ge_term->left_term);
  delete_term_formula(ge_term->right_term);

  if (formula->get_number_of_variables() > 0) {
    set_term_formula(ge_term, formula);
    add_int_variables(current_term_,formula->get_var_coeff_map());
    if (string_terms_.size() > 0) {
      string_terms_map_[ge_term] = string_terms_;
      string_terms_.clear();
    }
  }
}

void ArithmeticFormulaGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(lt_term->left_term);
  right_formula = get_term_formula(lt_term->right_term);

  formula = left_formula->Subtract(right_formula);
  formula->set_type(ArithmeticFormula::Type::LT);
  delete_term_formula(lt_term->left_term);
  delete_term_formula(lt_term->right_term);

  if (formula->get_number_of_variables() > 0) {
    set_term_formula(lt_term, formula);
    add_int_variables(current_term_,formula->get_var_coeff_map());
    if (string_terms_.size() > 0) {
      string_terms_map_[lt_term] = string_terms_;
      string_terms_.clear();
    }
  }
}

void ArithmeticFormulaGenerator::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(le_term->left_term);
  right_formula = get_term_formula(le_term->right_term);

  formula = left_formula->Subtract(right_formula);
  formula->set_type(ArithmeticFormula::Type::LE);
  delete_term_formula(le_term->left_term);
  delete_term_formula(le_term->right_term);

  if (formula->get_number_of_variables() > 0) {
    set_term_formula(le_term, formula);
    add_int_variables(current_term_,formula->get_var_coeff_map());
    if (string_terms_.size() > 0) {
      string_terms_map_[le_term] = string_terms_;
      string_terms_.clear();
    }
  }
}

void ArithmeticFormulaGenerator::visitConcat(Concat_ptr concat_term) {
}

// TODO add membership operation for integers
void ArithmeticFormulaGenerator::visitIn(In_ptr in_term) {
}

// TODO add non-membership operation for integers
void ArithmeticFormulaGenerator::visitNotIn(NotIn_ptr not_in_term) {
}

void ArithmeticFormulaGenerator::visitLen(Len_ptr len_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;

  ArithmeticFormula_ptr formula = nullptr;

  std::string name = symbol_table_->get_var_name_for_expression(len_term, Variable::Type::INT);

  formula = new ArithmeticFormula();
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

  ArithmeticFormula_ptr formula = nullptr;

  std::string name = symbol_table_->get_var_name_for_expression(index_of_term, Variable::Type::INT);

  formula = new ArithmeticFormula();
  formula->add_variable(name, 1);

  set_term_formula(index_of_term, formula);

  string_terms_.push_back(index_of_term);
}

void ArithmeticFormulaGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  ArithmeticFormula_ptr formula = nullptr;

  std::string name = symbol_table_->get_var_name_for_expression(last_index_of_term, Variable::Type::INT);

  formula = new ArithmeticFormula();
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
}

void ArithmeticFormulaGenerator::visitReplace(Replace_ptr replace_term) {
}

void ArithmeticFormulaGenerator::visitCount(Count_ptr count_term) {
  LOG(FATAL) << "implement me";
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

  ArithmeticFormula_ptr formula = nullptr;

  Variable_ptr variable = symbol_table_->getVariable(qi_term->getVarName());
  if (Variable::Type::INT == variable->getType()) {
    formula = new ArithmeticFormula();
    formula->add_variable(variable->getName(),1);
    formula->set_type(ArithmeticFormula::Type::VAR);
  }

  set_term_formula(qi_term, formula);
}

void ArithmeticFormulaGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  ArithmeticFormula_ptr formula = nullptr;

  // Use fresh coeff maps for constants
  switch (term_constant->getValueType()) {
    case Primitive::Type::NUMERAL: {
      int constant = std::stoi(term_constant->getValue());
      formula = new ArithmeticFormula();
      formula->set_constant(constant);
      break;
    }
    default:
      break;
  }

  set_term_formula(term_constant, formula);
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

std::string ArithmeticFormulaGenerator::get_variable_group_name(Term_ptr term,Variable_ptr variable) {
  std::string var_name = variable->getName();
  if(variable_group_table_[term].find(var_name) == variable_group_table_[term].end()) {
    DVLOG(VLOG_LEVEL) << var_name << " has no group";
    return "";
  }
  return variable_group_table_[term][var_name];
}

std::string ArithmeticFormulaGenerator::get_variable_group_name(Term_ptr term,std::string var_name) {
  if(variable_group_table_[term].find(var_name) == variable_group_table_[term].end()) {
    DVLOG(VLOG_LEVEL) << var_name << " has no group";
    return "";
  }
  return variable_group_table_[term][var_name];
}

std::string ArithmeticFormulaGenerator::get_term_group_name(SMT::Term_ptr term) {
  if(term_group_map.find(term) == term_group_map.end()) {
    return "";
  }
  return term_group_map[term];
}

void ArithmeticFormulaGenerator::add_int_variables(Term_ptr term, std::map<std::string,int> variables) {
//  if (Option::Solver::ENABLE_DEPENDENCY) {
//    std::string start_group;
//    // get a starting group from the variable list
//    for (auto &var : variables) {
//      if (variable_group_table_[term].find(var.first) != variable_group_table_[term].end()) {
//        start_group = variable_group_table_[term][var.first];
//        break;
//      }
//    }
//    // if no group is found at all, create new one
//    if (start_group.empty()) {
//      start_group = generate_group_name(term, variables.begin()->first);
//    }
//
//    // merge each variable's groups together into start_group
//    for (auto &var : variables) {
//      if (variable_group_table_[term].find(var.first) == variable_group_table_[term].end()) {
//        variable_group_table_[term][var.first] = start_group;
//        int track = group_variables_map_[start_group].size();
//        group_variables_map_[start_group][var.first] = track;
//      } else if (variable_group_table_[term][var.first] != start_group) {
//        // merge the two groups
//        std::string var_group = variable_group_table_[term][var.first];
//        for (auto &iter : group_variables_map_[var_group]) {
//          variable_group_table_[term][iter.first] = start_group;
//          int track = group_variables_map_[start_group].size();
//          group_variables_map_[start_group][iter.first] = track;
//        }
//        group_variables_map_.erase(var_group);
//      }
//    }
//  } else {
//
    std::string start_group = "NYWAH";
    for(auto& var : variables) {
      if(variable_group_table_[term].find(var.first) == variable_group_table_[term].end()) {
        variable_group_table_[term][var.first] = start_group;
        int track = group_variables_map_[start_group].size();
        group_variables_map_[start_group][var.first] = track;
      }
    }

  //}
}

std::string ArithmeticFormulaGenerator::generate_group_name(SMT::Term_ptr term, std::string var_name) {
  std::string group_name = symbol_table_->get_var_name_for_node(term,SMT::Variable::Type::INT);
  group_name += var_name;
  return group_name;
}

VariableTrackMap ArithmeticFormulaGenerator::get_group_trackmap(std::string name) {
  if(group_variables_map_.find(name) == group_variables_map_.end()) {
    DVLOG(VLOG_LEVEL) << "no trackmap for group: " << name;
    return VariableTrackMap();
  }
  return group_variables_map_[name];
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