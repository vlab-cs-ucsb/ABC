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
        root (script), symbol_table (symbol_table) {

}

ArithmeticFormulaGenerator::~ArithmeticFormulaGenerator() {
  for (auto& pair : formulas) {
    delete pair.second;
    pair.second = nullptr;
  }
}

void ArithmeticFormulaGenerator::start() {
  DVLOG(VLOG_LEVEL) << "Arithmetic constraint extraction starts";
  visit(root);
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

  for (auto it = and_term->term_list->rbegin(); it != and_term->term_list->rend(); it++) {
    param_formula = getTermFormula(*it);
    if (param_formula != nullptr) {
      if (and_formula == nullptr) {
        and_formula = param_formula->clone();
      } else if (not param_formula->isVariableOrderingSame(and_formula)) {
        param_formula->mergeCoefficients(and_formula);
      }
    }
  }

  and_formula->setType(ArithmeticFormula::Type::INTERSECT);
  setTermFormula(and_term, and_formula);
}

/**
 * Right most formula that contains arithmetic constraint has all variable coefficients,
 * update others based on that
 */
void ArithmeticFormulaGenerator::visitOr(Or_ptr or_term) {
  visit_children_of(or_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;

  ArithmeticFormula_ptr or_formula = nullptr, param_formula = nullptr;

  for (auto it = or_term->term_list->rbegin(); it != or_term->term_list->rend(); it++) {
    param_formula = getTermFormula(*it);
    if (param_formula != nullptr) {
      if (or_formula == nullptr) {
        or_formula = param_formula->clone();
      } else if (not param_formula->isVariableOrderingSame(or_formula)) {
        param_formula->mergeCoefficients(or_formula);
        if (Term::Type::AND == (*it)->getType()) {
          And_ptr and_term = dynamic_cast<And_ptr>(*it);
          ArithmeticFormula_ptr child_formula = nullptr;
          for (auto& child_term : *(and_term->term_list)) {
            child_formula = getTermFormula(child_term);
            if (child_formula != nullptr) {
              child_formula->mergeCoefficients(param_formula);
            }
          }
        }
      }
    }
  }
  or_formula->setType(ArithmeticFormula::Type::UNION);
  setTermFormula(or_term, or_formula);
}

void ArithmeticFormulaGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  ArithmeticFormula_ptr formula = nullptr, child_formula = nullptr;

  child_formula = getTermFormula(not_term->term);

  if (child_formula != nullptr) {
    formula = child_formula->negateOperation();
    deleteTermFormula(not_term->term);
  }

  setTermFormula(not_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[not_term] = string_terms;
    string_terms.clear();
  } else {
    auto it = string_terms_map.find(not_term->term);
    if (it != string_terms_map.end()) {
      string_terms_map[not_term] = it->second;
      string_terms_map.erase(it);
    }
  }
}

void ArithmeticFormulaGenerator::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *u_minus_term;
  ArithmeticFormula_ptr formula = nullptr, child_formula = nullptr;

  child_formula = getTermFormula(u_minus_term->term);

  if (child_formula != nullptr) {
    formula = child_formula->multiply(-1);
    deleteTermFormula(u_minus_term->term);
  }

  setTermFormula(u_minus_term, formula);
}

void ArithmeticFormulaGenerator::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *minus_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(minus_term->left_term);
  right_formula = getTermFormula(minus_term->right_term);

  if (left_formula != nullptr and right_formula != nullptr) {
    formula = left_formula->substract(right_formula);
    formula->setType(ArithmeticFormula::Type::EQ);
    deleteTermFormula(minus_term->left_term);
    deleteTermFormula(minus_term->right_term);
  }

  setTermFormula(minus_term, formula);
}

void ArithmeticFormulaGenerator::visitPlus(Plus_ptr plus_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *plus_term;
  ArithmeticFormula_ptr formula = nullptr, plus_formula = nullptr, param_formula = nullptr;
  for (auto& term_ptr : *(plus_term->term_list)) {
    visit(term_ptr);
    param_formula = getTermFormula(term_ptr);
    if (formula == nullptr) {
      formula = param_formula->clone();
    } else {
      plus_formula = formula->add(param_formula);
      delete formula;
      formula = plus_formula;
    }
    deleteTermFormula(term_ptr);
  }
  setTermFormula(plus_term, formula);
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
    param_formula = getTermFormula(term_ptr);
    if (param_formula->isConstant()) {
      multiplicant = multiplicant * param_formula->getConstant();
    } else if (formula == nullptr) {
      times_formula = param_formula->clone();
    } else {
      LOG(FATAL)<< "Does not support non-linear multiplication";
    }
    deleteTermFormula(term_ptr);
  }
  formula = times_formula->multiply(multiplicant);
  delete times_formula;
  setTermFormula(times_term, formula);
}

void ArithmeticFormulaGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(eq_term->left_term);
  right_formula = getTermFormula(eq_term->right_term);

  if (left_formula != nullptr and right_formula != nullptr) {
    formula = left_formula->substract(right_formula);
    formula->setType(ArithmeticFormula::Type::EQ);
    deleteTermFormula(eq_term->left_term);
    deleteTermFormula(eq_term->right_term);
  }

  setTermFormula(eq_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[eq_term] = string_terms;
    string_terms.clear();
  }
}


void ArithmeticFormulaGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(not_eq_term->left_term);
  right_formula = getTermFormula(not_eq_term->right_term);

  if (left_formula != nullptr and right_formula != nullptr) {
    formula = left_formula->substract(right_formula);
    formula->setType(ArithmeticFormula::Type::NOTEQ);
    deleteTermFormula(not_eq_term->left_term);
    deleteTermFormula(not_eq_term->right_term);
  }

  setTermFormula(not_eq_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[not_eq_term] = string_terms;
    string_terms.clear();
  }
}

void ArithmeticFormulaGenerator::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(gt_term->left_term);
  right_formula = getTermFormula(gt_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::GT);
  deleteTermFormula(gt_term->left_term);
  deleteTermFormula(gt_term->right_term);

  setTermFormula(gt_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[gt_term] = string_terms;
    string_terms.clear();
  }
}

void ArithmeticFormulaGenerator::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(ge_term->left_term);
  right_formula = getTermFormula(ge_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::GE);
  deleteTermFormula(ge_term->left_term);
  deleteTermFormula(ge_term->right_term);

  setTermFormula(ge_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[ge_term] = string_terms;
    string_terms.clear();
  }
}

void ArithmeticFormulaGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(lt_term->left_term);
  right_formula = getTermFormula(lt_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::LT);
  deleteTermFormula(lt_term->left_term);
  deleteTermFormula(lt_term->right_term);

  setTermFormula(lt_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[lt_term] = string_terms;
    string_terms.clear();
  }
}

void ArithmeticFormulaGenerator::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;
  ArithmeticFormula_ptr formula = nullptr, left_formula = nullptr, right_formula = nullptr;

  left_formula = getTermFormula(le_term->left_term);
  right_formula = getTermFormula(le_term->right_term);

  formula = left_formula->substract(right_formula);
  formula->setType(ArithmeticFormula::Type::LE);
  deleteTermFormula(le_term->left_term);
  deleteTermFormula(le_term->right_term);

  setTermFormula(le_term, formula);

  if (string_terms.size() > 0) {
    string_terms_map[le_term] = string_terms;
    string_terms.clear();
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

  std::string name = Ast2Dot::toString(len_term);

  addArithmeticVariable(name);
  formula = new ArithmeticFormula(coeff_index_map, coefficients);
  formula->setVariableCoefficient(name, 1);

  setTermFormula(len_term, formula);

  string_terms.push_back(len_term);
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

  std::string name = Ast2Dot::toString(index_of_term);

  addArithmeticVariable(name);
  formula = new ArithmeticFormula(coeff_index_map, coefficients);
  formula->setVariableCoefficient(name, 1);

  setTermFormula(index_of_term, formula);

  string_terms.push_back(index_of_term);
}

void ArithmeticFormulaGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  ArithmeticFormula_ptr formula = nullptr;

  std::string name = Ast2Dot::toString(last_index_of_term);

  addArithmeticVariable(name);
  formula = new ArithmeticFormula(coeff_index_map, coefficients);
  formula->setVariableCoefficient(name, 1);

  setTermFormula(last_index_of_term, formula);

  string_terms.push_back(last_index_of_term);
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

  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  if (Variable::Type::INT == variable->getType()) {
    addArithmeticVariable(variable->getName());
    formula = new ArithmeticFormula(coeff_index_map, coefficients);
    formula->setVariableCoefficient(variable->getName(), 1);
  }

  setTermFormula(qi_term, formula);
}

void ArithmeticFormulaGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  ArithmeticFormula_ptr formula = nullptr;

  switch (term_constant->getValueType()) {
    case Primitive::Type::NUMERAL: {
      int constant = std::stoi(term_constant->getValue());
      formula = new ArithmeticFormula(coeff_index_map, coefficients);
      formula->setConstant(constant);
      break;
    }
    default:
      break;
  }

  setTermFormula(term_constant, formula);
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

ArithmeticFormula_ptr ArithmeticFormulaGenerator::getTermFormula(Term_ptr term) {
  auto iter = formulas.find(term);
  if (iter == formulas.end()) {
    return nullptr;
  }
  return iter->second;
}

bool ArithmeticFormulaGenerator::hasStringTerms(Term_ptr term) {
  return (string_terms_map.find(term) != string_terms_map.end());
}

std::map<SMT::Term_ptr, SMT::TermList> ArithmeticFormulaGenerator::getStringTermsMap() {
  return string_terms_map;
}

TermList& ArithmeticFormulaGenerator::getStringTermsIn(Term_ptr term) {
  return string_terms_map[term];
}

void ArithmeticFormulaGenerator::clearTermFormulas() {
  for (auto& pair : formulas) {
    delete pair.second;
  }
  formulas.clear();
}

bool ArithmeticFormulaGenerator::setTermFormula(Term_ptr term, ArithmeticFormula_ptr formula) {
  auto result = formulas.insert(std::make_pair(term, formula));
  if (result.second == false) {
    LOG(FATAL)<< "formula is already computed for term: " << *term;
  }
  return result.second;
}

void ArithmeticFormulaGenerator::deleteTermFormula(Term_ptr term) {
  auto formula = getTermFormula(term);
  if (formula != nullptr) {
    delete formula;
    formulas.erase(term);
  }
}

void ArithmeticFormulaGenerator::addArithmeticVariable(std::string name) {
  if (coeff_index_map.find(name) == coeff_index_map.end()) {
    coefficients.push_back(0);
    coeff_index_map[name] = coefficients.size() - 1;
  }
}



} /* namespace Solver */
} /* namespace Vlab */
