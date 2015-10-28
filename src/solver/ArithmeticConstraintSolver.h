/*
 * ArithmeticConstraintSolver.h
 *
 *  Created on: Nov 1, 2015
 *      Author: baki
 */

#ifndef SOLVER_ARITHMETICCONSTRAINTSOLVER_H_
#define SOLVER_ARITHMETICCONSTRAINTSOLVER_H_

#include <string>
#include <sstream>
#include <map>

#include <glog/logging.h>

#include "theory/ArithmeticFormula.h"
#include "theory/BinaryIntAutomaton.h"
#include "AstTraverser.h"
#include "ArithmeticFormulaGenerator.h"
#include "smt/ast.h"
#include "SymbolTable.h"
#include "Value.h"

namespace Vlab {
namespace Solver {

class ArithmeticConstraintSolver: public AstTraverser {
  typedef std::map<SMT::Term_ptr, Value_ptr> TermValueMap;
public:
  ArithmeticConstraintSolver(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~ArithmeticConstraintSolver();

  void start();
  void end();

  void setCallbacks();

  void visitScript(SMT::Script_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void processOr(SMT::Or_ptr);
  //  void visitNot(SMT::Not_ptr);
//  void visitEq(SMT::Eq_ptr);
//  void visitNotEq(SMT::NotEq_ptr);
//  void visitGt(SMT::Gt_ptr);
//  void visitGe(SMT::Ge_ptr);
//  void visitLt(SMT::Lt_ptr);
//  void visitLe(SMT::Le_ptr);

  Value_ptr getTermValue(SMT::Term_ptr term);
  bool setTermValue(SMT::Term_ptr term, Value_ptr value);
  void clearTermValues();
  bool hasStringTerms(SMT::Term_ptr term);
  SMT::TermList& getStringTermsIn(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::Term_ptr>& getTermValueIndex();
  TermValueMap& getTermValues();
  std::map<SMT::Term_ptr, SMT::TermList>& getStringTermsMap();
  void assign(std::map<SMT::Term_ptr, SMT::Term_ptr>& term_value_index,
          TermValueMap& term_values,
          std::map<SMT::Term_ptr, SMT::TermList>& string_terms_map);


protected:
  SymbolTable_ptr symbol_table;
  ArithmeticFormulaGenerator arithmetic_formula_generator;

  /**
   * To keep single automaton for each variable we use a map
   */
  std::map<SMT::Term_ptr, SMT::Term_ptr> term_value_index;
  TermValueMap term_values;
  std::map<SMT::Term_ptr, SMT::TermList> string_terms_map;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_ARITHMETICCONSTRAINTSOLVER_H_ */
