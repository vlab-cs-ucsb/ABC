/*
 * StringConstraintSolver.h
 *
 *  Created on: Jan 22, 2017
 *      Author: baki
 */

#ifndef SRC_SOLVER_STRINGCONSTRAINTSOLVER_H_
#define SRC_SOLVER_STRINGCONSTRAINTSOLVER_H_

#include <iostream>
#include <map>
#include <string>

#include <glog/logging.h>

#include "../smt/ast.h"
#include "../smt/Visitor.h"
#include "../theory/StringAutomaton.h"
#include "../theory/StringFormula.h"
#include "../theory/Formula.h"
#include "AstTraverser.h"
#include "ConstraintInformation.h"
#include "StringFormulaGenerator.h"
#include "SymbolTable.h"
#include "Value.h"

namespace Vlab {
namespace Solver {

class StringConstraintSolver: public AstTraverser {
  using TermValueMap = std::map<SMT::Term_ptr, Value_ptr>;
 public:
  StringConstraintSolver(SMT::Script_ptr, SymbolTable_ptr, ConstraintInformation_ptr);
  virtual ~StringConstraintSolver();

  void start(SMT::Visitable_ptr);
  void start();
  void end();
  void collect_string_constraint_info();

  void setCallbacks();

  void visitScript(SMT::Script_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitExists(SMT::Exists_ptr);
  void visitAnd(SMT::And_ptr);

  void postVisitAnd(SMT::And_ptr);
  void postVisitOr(SMT::Or_ptr);

  std::string get_string_variable_name(SMT::Term_ptr);
  Value_ptr get_term_value(SMT::Term_ptr term);
  bool set_term_value(SMT::Term_ptr term, Value_ptr value);
  bool set_group_value(SMT::Term_ptr term, Value_ptr value);
  void clear_term_value(SMT::Term_ptr term);
  void clear_term_values();
  bool has_integer_terms(SMT::Term_ptr term);
  SMT::TermList& get_integer_terms_in(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::TermList>& get_integer_terms_map();

  void project_variable(std::string var);

 protected:
  void visitOr(SMT::Or_ptr);

  SymbolTable_ptr symbol_table_;
  ConstraintInformation_ptr constraint_information_;
  StringFormulaGenerator string_formula_generator_;

  /**
   * To keep single automaton for each variable we use a map
   */
  std::map<SMT::Term_ptr, SMT::Term_ptr> term_value_index_;
  TermValueMap term_values_;
  std::map<SMT::Term_ptr, SMT::TermList> integer_terms_map_;

 private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_STRINGCONSTRAINTSOLVER_H_ */
