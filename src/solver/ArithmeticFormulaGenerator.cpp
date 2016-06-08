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
 * Generates one big coefficient vector for all int and length variables used
 *
 */
ArithmeticFormulaGenerator::ArithmeticFormulaGenerator( Script_ptr script, SymbolTable_ptr symbol_table) :
        root_ (script), symbol_table_ (symbol_table) {

}

ArithmeticFormulaGenerator::~ArithmeticFormulaGenerator() {
  for (auto& pair : formulas_) {
    delete pair.second;
    pair.second = nullptr;
  }
}

void ArithmeticFormulaGenerator::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts";
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
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;

  ArithmeticFormula_ptr and_formula = nullptr, param_formula = nullptr;

  for (auto it = and_term->term_list->rbegin(); it not_eq and_term->term_list->rend(); it++) {
    param_formula = get_term_formula(*it);
    if (param_formula not_eq nullptr) {
      if (and_formula == nullptr) {
        and_formula = param_formula->clone();
      } else if (not param_formula->isVariableOrderingSame(and_formula)) {
        param_formula->mergeCoefficients(and_formula);
      }
    }
  }

  if (and_formula not_eq nullptr) {
    and_formula->setType(ArithmeticFormula::Type::INTERSECT);
    set_term_formula(and_term, and_formula);
  }

  // clear coefficient maps for other possible and components
  reset_variable_coefficient_maps();
}

/**
 * Right most formula that contains arithmetic constraint has all variable coefficients,
 * update others based on that
 */
void ArithmeticFormulaGenerator::visitOr(Or_ptr or_term) {
  visit_children_of(or_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;

  ArithmeticFormula_ptr or_formula = nullptr, param_formula = nullptr;

  for (auto it = or_term->term_list->rbegin(); it not_eq or_term->term_list->rend(); it++) {
    param_formula = get_term_formula(*it);
    if (param_formula not_eq nullptr) {
      if (or_formula == nullptr) {
        or_formula = param_formula->clone();
      } else if (not param_formula->isVariableOrderingSame(or_formula)) {
        param_formula->mergeCoefficients(or_formula);
        if (Term::Type::AND == (*it)->type()) {
          And_ptr and_term = dynamic_cast<And_ptr>(*it);
          ArithmeticFormula_ptr child_formula = nullptr;
          for (auto& child_term : *(and_term->term_list)) {
            child_formula = get_term_formula(child_term);
            if (child_formula not_eq nullptr) {
              child_formula->mergeCoefficients(param_formula);
            }
          }
        }
      }
    }
  }

  if (or_formula not_eq nullptr) {
    or_formula->setType(ArithmeticFormula::Type::UNION);
    set_term_formula(or_term, or_formula);
  }
}

void ArithmeticFormulaGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  ArithmeticFormula_ptr formula = nullptr, child_formula = nullptr;

  child_formula = get_term_formula(not_term->term);

  if (child_formula not_eq nullptr) {
    formula = child_formula->negateOperation();
    delete_term_formula(not_term->term);
    set_term_formula(not_term, formula);
  }

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
    formula = child_formula->multiply(-1);
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
    formula = left_formula->substract(right_formula);
    formula->setType(ArithmeticFormula::Type::EQ);
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
      plus_formula = formula->add(param_formula);
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
    if (param_formula->isConstant()) {
      multiplicant = multiplicant * param_formula->getConstant();
    } else if (times_formula == nullptr) {
      times_formula = param_formula->clone();
    } else {
      LOG(FATAL)<< "Does not support non-linear multiplication";
    }
    delete_term_formula(term_ptr);
  }

  formula = times_formula->multiply(multiplicant);
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
    formula = left_formula->substract(right_formula);
    formula->setType(ArithmeticFormula::Type::EQ);
    delete_term_formula(eq_term->left_term);
    delete_term_formula(eq_term->right_term);
    set_term_formula(eq_term, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[eq_term] = string_terms_;
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
    formula = left_formula->substract(right_formula);
    formula->setType(ArithmeticFormula::Type::NOTEQ);
    delete_term_formula(not_eq_term->left_term);
    delete_term_formula(not_eq_term->right_term);
    set_term_formula(not_eq_term, formula);
    if (string_terms_.size() > 0) {
      string_terms_map_[not_eq_term] = string_terms_;
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

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::GT);
  delete_term_formula(gt_term->left_term);
  delete_term_formula(gt_term->right_term);

  set_term_formula(gt_term, formula);

  if (string_terms_.size() > 0) {
    string_terms_map_[gt_term] = string_terms_;
    string_terms_.clear();
  }
}

void ArithmeticFormulaGenerator::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(ge_term->left_term);
  right_formula = get_term_formula(ge_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::GE);
  delete_term_formula(ge_term->left_term);
  delete_term_formula(ge_term->right_term);

  set_term_formula(ge_term, formula);

  if (string_terms_.size() > 0) {
    string_terms_map_[ge_term] = string_terms_;
    string_terms_.clear();
  }
}

void ArithmeticFormulaGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(lt_term->left_term);
  right_formula = get_term_formula(lt_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::LT);
  delete_term_formula(lt_term->left_term);
  delete_term_formula(lt_term->right_term);

  set_term_formula(lt_term, formula);

  if (string_terms_.size() > 0) {
    string_terms_map_[lt_term] = string_terms_;
    string_terms_.clear();
  }
}

void ArithmeticFormulaGenerator::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = get_term_formula(le_term->left_term);
  right_formula = get_term_formula(le_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::LE);
  delete_term_formula(le_term->left_term);
  delete_term_formula(le_term->right_term);

  set_term_formula(le_term, formula);

  if (string_terms_.size() > 0) {
    string_terms_map_[le_term] = string_terms_;
    string_terms_.clear();
  }
}

void ArithmeticFormulaGenerator::visitConcat(Concat_ptr concat_term) {
}

// TODO add membership operation for integers
void ArithmeticFormulaGenerator::visitIn(In_ptr in_term) {
//  DVLOG(VLOG_LEVEL) << "visit: " << *in_term;
}

// TODO add non-membership operation for integers
void ArithmeticFormulaGenerator::visitNotIn(NotIn_ptr not_in_term) {
//  DVLOG(VLOG_LEVEL) << "visit: " << *not_in_term;
}

void ArithmeticFormulaGenerator::visitLen(Len_ptr len_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;

  ArithmeticFormula_ptr formula = nullptr;

  std::string name = symbol_table_->get_var_name_for_expression(len_term, Variable::Type::INT);

  add_int_variable(name);
  formula = new ArithmeticFormula(coeff_index_map_, coefficients_);
  formula->setVariableCoefficient(name, 1);

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

  add_int_variable(name);
  formula = new ArithmeticFormula(coeff_index_map_, coefficients_);
  formula->setVariableCoefficient(name, 1);

  set_term_formula(index_of_term, formula);

  string_terms_.push_back(index_of_term);
}

void ArithmeticFormulaGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  ArithmeticFormula_ptr formula = nullptr;

  std::string name = symbol_table_->get_var_name_for_expression(last_index_of_term, Variable::Type::INT);

  add_int_variable(name);
  formula = new ArithmeticFormula(coeff_index_map_, coefficients_);
  formula->setVariableCoefficient(name, 1);

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
    add_int_variable(variable->getName());
    formula = new ArithmeticFormula(coeff_index_map_, coefficients_);
    formula->setVariableCoefficient(variable->getName(), 1);
    if (formula->getNumberOfVariables() == 1) {
      formula->setType(ArithmeticFormula::Type::VAR);
    }
  }

  set_term_formula(qi_term, formula);
}

void ArithmeticFormulaGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  ArithmeticFormula_ptr formula = nullptr;

  switch (term_constant->getValueType()) {
    case Primitive::Type::NUMERAL: {
      int constant = std::stoi(term_constant->getValue());
      formula = new ArithmeticFormula(coeff_index_map_, coefficients_);
      formula->setConstant(constant);
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

void ArithmeticFormulaGenerator::add_int_variable(std::string name) {
  if (coeff_index_map_.find(name) == coeff_index_map_.end()) {
    coefficients_.push_back(0);
    coeff_index_map_[name] = coefficients_.size() - 1;
  }
}

void ArithmeticFormulaGenerator::reset_variable_coefficient_maps() {
  coeff_index_map_.clear();
  coefficients_.clear();
}


} /* namespace Solver */
} /* namespace Vlab */
