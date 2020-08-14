/*
 * ArithmeticConstraintSolver.h
 *
 *  Created on: Nov 1, 2015
 *      Author: baki
 */

#ifndef SOLVER_ARITHMETICCONSTRAINTSOLVER_H_
#define SOLVER_ARITHMETICCONSTRAINTSOLVER_H_

#include <iostream>
#include <map>
#include <string>
#include <utility>

#include <glog/logging.h>
#include <redox.hpp>
#include <unordered_map>
#include <string>

#include "../smt/ast.h"
#include "../smt/Visitor.h"
#include "../smt/typedefs.h"
#include "../theory/ArithmeticFormula.h"
#include "../theory/BinaryIntAutomaton.h"
#include "ArithmeticFormulaGenerator.h"
#include "AstTraverser.h"
#include "ConstraintInformation.h"
#include "SymbolTable.h"
#include "Value.h"

namespace Vlab {
namespace Solver {

class ArithmeticConstraintSolver : public AstTraverser {
  using TermValueMap = std::map<SMT::Term_ptr, Value_ptr>;
 public:
  ArithmeticConstraintSolver(SMT::Script_ptr, SymbolTable_ptr, ConstraintInformation_ptr, bool use_signed_integers);
  virtual ~ArithmeticConstraintSolver();

  void start(SMT::Visitable_ptr);
  void start();
  void end();
  void collect_arithmetic_constraint_info(SMT::Visitable_ptr);
  void collect_arithmetic_constraint_info();

  void setCallbacks();

  void visitScript(SMT::Script_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitAnd(SMT::And_ptr);

  void postVisitAnd(SMT::And_ptr);
  void postVisitOr(SMT::Or_ptr);

  std::string get_int_variable_name(SMT::Term_ptr);
  Value_ptr get_term_value(SMT::Term_ptr term);
  bool set_term_value(SMT::Term_ptr term, Value_ptr value);
  bool set_group_value(SMT::Term_ptr term, Value_ptr value);
  void clear_term_value(SMT::Term_ptr term);
  void clear_term_values();
  bool has_string_terms(SMT::Term_ptr term);
  SMT::TermList& get_string_terms_in(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::TermList>& get_string_terms_map();
  
  void push_generator(SMT::Term_ptr);
  void pop_generators(int, SMT::Term_ptr);


 protected:
  void visitOr(SMT::Or_ptr);

  bool use_unsigned_integers_;
  SymbolTable_ptr symbol_table_;
  ConstraintInformation_ptr constraint_information_;
  std::shared_ptr<ArithmeticFormulaGenerator> arithmetic_formula_generator_;
  std::vector<std::pair<SMT::Term_ptr,std::shared_ptr<ArithmeticFormulaGenerator>>> generator_stack_;

  /**
   * To keep single automaton for each variable we use a map
   */
  std::map<SMT::Term_ptr, SMT::Term_ptr> term_value_index_;
  TermValueMap term_values_;
  std::map<SMT::Term_ptr, SMT::TermList> string_terms_map_;

 private:
  void YieldWhileValuesLocked() {
//    while(symbol_table_->AreValuesLocked()) std::this_thread::yield();
  }
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_ARITHMETICCONSTRAINTSOLVER_H_ */
