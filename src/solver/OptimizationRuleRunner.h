/*
 * OptimizationRuleRunner.h
 *
 *  Created on: May 6, 2015
 *      Author: baki
 */

#ifndef SOLVER_OPTIMIZATIONRULERUNNER_H_
#define SOLVER_OPTIMIZATIONRULERUNNER_H_

#include <glog/logging.h>
#include "smt/ast.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"
#include "SyntacticOptimizer.h"

namespace Vlab {
namespace Solver {

class OptimizationRuleRunner: public SMT::Visitor {
public:
  OptimizationRuleRunner(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~OptimizationRuleRunner();
  void start();
  void end();

  void visitScript(SMT::Script_ptr);
  void visitCommand(SMT::Command_ptr);
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
  void visitEq(SMT::Eq_ptr);
  void visitGt(SMT::Gt_ptr);
  void visitGe(SMT::Ge_ptr);
  void visitLt(SMT::Lt_ptr);
  void visitLe(SMT::Le_ptr);
  void visitConcat(SMT::Concat_ptr);
  void visitIn(SMT::In_ptr);
  void visitLen(SMT::Len_ptr);
  void visitContains(SMT::Contains_ptr);
  void visitBegins(SMT::Begins_ptr);
  void visitEnds(SMT::Ends_ptr);
  void visitIndexOf(SMT::IndexOf_ptr);
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
protected:
  bool has_optimization_rules();
  bool check_and_substitute_var(SMT::Term_ptr& term);

  SMT::Script_ptr root;
  SymbolTable_ptr symbol_table;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_OPTIMIZATIONRULERUNNER_H_ */
