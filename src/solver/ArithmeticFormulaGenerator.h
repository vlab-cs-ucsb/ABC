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

  void start();
  void end();

  void visitScript(SMT::Script_ptr);
  void visitCommand(SMT::Command_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitTerm(SMT::Term_ptr);
  void visitExclamation(SMT::Exclamation_ptr);
  void visitExists(SMT::Exists_ptr);
  void visitForAll(SMT::ForAll_ptr);
  void visitLet(SMT::Let_ptr);
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void visitNot(SMT::Not_ptr);
  void visitUMinus(SMT::UMinus_ptr);
  void visitMinus(SMT::Minus_ptr);
  void visitPlus(SMT::Plus_ptr);
  void visitTimes(SMT::Times_ptr);
  void visitEq(SMT::Eq_ptr);
  void visitNotEq(SMT::NotEq_ptr);
  void visitGt(SMT::Gt_ptr);
  void visitGe(SMT::Ge_ptr);
  void visitLt(SMT::Lt_ptr);
  void visitLe(SMT::Le_ptr);
  void visitConcat(SMT::Concat_ptr);
  void visitIn(SMT::In_ptr);
  void visitNotIn(SMT::NotIn_ptr);
  void visitLen(SMT::Len_ptr);
  void visitContains(SMT::Contains_ptr);
  void visitNotContains(SMT::NotContains_ptr);
  void visitBegins(SMT::Begins_ptr);
  void visitNotBegins(SMT::NotBegins_ptr);
  void visitEnds(SMT::Ends_ptr);
  void visitNotEnds(SMT::NotEnds_ptr);
  void visitIndexOf(SMT::IndexOf_ptr);
  void visitLastIndexOf(SMT::LastIndexOf_ptr);
  void visitCharAt(SMT::CharAt_ptr);
  void visitSubString(SMT::SubString_ptr);
  void visitSubStringFirstOf(SMT::SubStringFirstOf_ptr);
  void visitSubStringLastOf(SMT::SubStringLastOf_ptr);
  void visitToUpper(SMT::ToUpper_ptr);
  void visitToLower(SMT::ToLower_ptr);
  void visitTrim(SMT::Trim_ptr);
  void visitReplace(SMT::Replace_ptr);
  void visitCount(SMT::Count_ptr);
  void visitIte(SMT::Ite_ptr);
  void visitReConcat(SMT::ReConcat_ptr);
  void visitToRegex(SMT::ToRegex_ptr);
  void visitUnknownTerm(SMT::Unknown_ptr);
  void visitAsQualIdentifier(SMT::AsQualIdentifier_ptr);
  void visitQualIdentifier(SMT::QualIdentifier_ptr);
  void visitTermConstant(SMT::TermConstant_ptr);
  void visitSort(SMT::Sort_ptr);
  void visitTVariable(SMT::TVariable_ptr);
  void visitTBool(SMT::TBool_ptr);
  void visitTInt(SMT::TInt_ptr);
  void visitTString(SMT::TString_ptr);
  void visitAttribute(SMT::Attribute_ptr);
  void visitSortedVar(SMT::SortedVar_ptr);
  void visitVarBinding(SMT::VarBinding_ptr);
  void visitIdentifier(SMT::Identifier_ptr);
  void visitPrimitive(SMT::Primitive_ptr);
  void visitVariable(SMT::Variable_ptr);

  Theory::ArithmeticFormula_ptr getTermFormula(SMT::Term_ptr term);
  bool hasStringTerms(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::TermList> getStringTermsMap();
  SMT::TermList& getStringTermsIn(SMT::Term_ptr term);
  void clearTermFormulas();
protected:
  bool setTermFormula(SMT::Term_ptr term, Theory::ArithmeticFormula_ptr formula);
  void deleteTermFormula(SMT::Term_ptr);
  void addArithmeticVariable(std::string name);

  SMT::Script_ptr root;
  SymbolTable_ptr symbol_table;
  std::map<std::string, int> coeff_index_map;
  std::vector<int> coefficients;
  std::map<SMT::Term_ptr, Theory::ArithmeticFormula_ptr> formulas;
  SMT::TermList string_terms;
  std::map<SMT::Term_ptr, SMT::TermList> string_terms_map;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_ARITHMETICFORMULAGENERATOR_H_ */
