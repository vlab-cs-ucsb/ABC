/*
 * ArithmeticFormulaGenerator.h
 *
 *  Created on: Oct 19, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef SOLVER_ARITHMETICFORMULAGENERATOR_H_
#define SOLVER_ARITHMETICFORMULAGENERATOR_H_

#include <vector>
#include <map>
#include <sstream>

#include <glog/logging.h>
#include "smt/ast.h"
#include "SymbolTable.h"
#include "theory/ArithmeticFormula.h"
#include "Ast2Dot.h"

namespace Vlab {
namespace Solver {

class ArithmeticFormulaGenerator: public SMT::Visitor {
public:
  ArithmeticFormulaGenerator(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~ArithmeticFormulaGenerator();

  void start() override;
  void end() override;

  void visitScript(SMT::Script_ptr) override;
  void visitCommand(SMT::Command_ptr) override;
  void visitAssert(SMT::Assert_ptr) override;
  void visitTerm(SMT::Term_ptr) override;
  void visitExclamation(SMT::Exclamation_ptr) override;
  void visitExists(SMT::Exists_ptr) override;
  void visitForAll(SMT::ForAll_ptr) override;
  void visitLet(SMT::Let_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;
  void visitNot(SMT::Not_ptr) override;
  void visitUMinus(SMT::UMinus_ptr) override;
  void visitMinus(SMT::Minus_ptr) override;
  void visitPlus(SMT::Plus_ptr) override;
  void visitTimes(SMT::Times_ptr) override;
  void visitEq(SMT::Eq_ptr) override;
  void visitNotEq(SMT::NotEq_ptr) override;
  void visitGt(SMT::Gt_ptr) override;
  void visitGe(SMT::Ge_ptr) override;
  void visitLt(SMT::Lt_ptr) override;
  void visitLe(SMT::Le_ptr) override;
  void visitConcat(SMT::Concat_ptr) override;
  void visitIn(SMT::In_ptr) override;
  void visitNotIn(SMT::NotIn_ptr) override;
  void visitLen(SMT::Len_ptr) override;
  void visitContains(SMT::Contains_ptr) override;
  void visitNotContains(SMT::NotContains_ptr) override;
  void visitBegins(SMT::Begins_ptr) override;
  void visitNotBegins(SMT::NotBegins_ptr) override;
  void visitEnds(SMT::Ends_ptr) override;
  void visitNotEnds(SMT::NotEnds_ptr) override;
  void visitIndexOf(SMT::IndexOf_ptr) override;
  void visitLastIndexOf(SMT::LastIndexOf_ptr) override;
  void visitCharAt(SMT::CharAt_ptr) override;
  void visitSubString(SMT::SubString_ptr) override;
  void visitToUpper(SMT::ToUpper_ptr) override;
  void visitToLower(SMT::ToLower_ptr) override;
  void visitTrim(SMT::Trim_ptr) override;
  void visitToString(SMT::ToString_ptr) override;
  void visitToInt(SMT::ToInt_ptr) override;
  void visitReplace(SMT::Replace_ptr) override;
  void visitCount(SMT::Count_ptr) override;
  void visitIte(SMT::Ite_ptr) override;
  void visitReConcat(SMT::ReConcat_ptr) override;
  void visitToRegex(SMT::ToRegex_ptr) override;
  void visitUnknownTerm(SMT::Unknown_ptr) override;
  void visitAsQualIdentifier(SMT::AsQualIdentifier_ptr) override;
  void visitQualIdentifier(SMT::QualIdentifier_ptr) override;
  void visitTermConstant(SMT::TermConstant_ptr) override;
  void visitSort(SMT::Sort_ptr) override;
  void visitTVariable(SMT::TVariable_ptr) override;
  void visitTBool(SMT::TBool_ptr) override;
  void visitTInt(SMT::TInt_ptr) override;
  void visitTString(SMT::TString_ptr) override;
  void visitAttribute(SMT::Attribute_ptr) override;
  void visitSortedVar(SMT::SortedVar_ptr) override;
  void visitVarBinding(SMT::VarBinding_ptr) override;
  void visitIdentifier(SMT::Identifier_ptr) override;
  void visitPrimitive(SMT::Primitive_ptr) override;
  void visitVariable(SMT::Variable_ptr) override;

  Theory::ArithmeticFormula_ptr get_term_formula(SMT::Term_ptr term);
  bool has_string_terms(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::TermList> get_string_terms_map();
  SMT::TermList& get_string_terms_in(SMT::Term_ptr term);
  void clear_term_formulas();
protected:
  bool set_term_formula(SMT::Term_ptr term, Theory::ArithmeticFormula_ptr formula);
  void delete_term_formula(SMT::Term_ptr);
  void add_int_variable(std::string name);
  void reset_variable_coefficient_maps();

  SMT::Script_ptr root_;
  SymbolTable_ptr symbol_table_;
  std::map<std::string, int> coeff_index_map_;
  std::vector<int> coefficients_;
  std::map<SMT::Term_ptr, Theory::ArithmeticFormula_ptr> formulas_;
  SMT::TermList string_terms_;
  std::map<SMT::Term_ptr, SMT::TermList> string_terms_map_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_ARITHMETICFORMULAGENERATOR_H_ */
