/*
 * ConstraintSolver.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef SOLVER_CONSTRAINTSOLVER_H_
#define SOLVER_CONSTRAINTSOLVER_H_

#include <string>
#include <sstream>
#include <map>

#include <glog/logging.h>

#include "smt/ast.h"
#include "theory/UnaryAutomaton.h"
#include "theory/IntAutomaton.h"
#include "theory/ArithmeticFormula.h"
#include "theory/BinaryIntAutomaton.h"
#include "theory/StringAutomaton.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"
#include "Value.h"
#include "VariableValueComputer.h"
#include "ArithmeticConstraintSolver.h"

namespace Vlab {
namespace Solver {

class ConstraintSolver: public SMT::Visitor {
  typedef std::map<SMT::Term_ptr, Value_ptr> TermValueMap;
  typedef std::map<SMT::Variable_ptr, std::vector<SMT::Term_ptr>> VariablePathTable;
public:
  ConstraintSolver(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~ConstraintSolver();

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

protected:
  Value_ptr getTermValue(SMT::Term_ptr term);
  bool setTermValue(SMT::Term_ptr term, Value_ptr value);
  void clearTermValue(SMT::Term_ptr term);
  void clearTermValues();
  void setVariablePath(SMT::QualIdentifier_ptr qi_term);
  void update_variables();
  void visit_children_of(SMT::Term_ptr term);
  bool check_and_visit(SMT::Term_ptr term);

  SMT::Script_ptr root;
  SymbolTable_ptr symbol_table;

  ArithmeticConstraintSolver arithmetic_constraint_solver;

  TermValueMap term_values;

  std::vector<SMT::Term_ptr> path_trace;
  VariablePathTable variable_path_table;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_CONSTRAINTSOLVER_H_ */
