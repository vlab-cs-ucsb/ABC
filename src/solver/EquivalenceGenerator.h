/*
 * EquivalenceGenerator.cpp
 *
  *  Created on: May 4, 2015
 *      Author: baki, tegan
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef SOLVER_EQUIVALENCEGENERATOR_H_
#define SOLVER_EQUIVALENCEGENERATOR_H_

#include <cstdbool>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <iostream>
#include <utility>

#include <glog/logging.h>
#include "smt/ast.h"
#include "solver/AstTraverser.h"
#include "solver/EquivalenceClass.h"
#include "solver/SymbolTable.h"
#include "solver/Counter.h"
#include "solver/EquivClassRuleRunner.h"
#include "solver/optimization/ConstantTermChecker.h"

namespace Vlab {
namespace Solver {

class EquivalenceGenerator : public AstTraverser {
 public:
  EquivalenceGenerator(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~EquivalenceGenerator();
  void start();
  void end();

  void setCallbacks();
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void visitEq(SMT::Eq_ptr);

 protected:
  bool is_equiv_of_variables(SMT::Term_ptr left_term, SMT::Term_ptr right_term);
  bool is_equiv_of_variable_and_constant(SMT::Term_ptr left_term, SMT::Term_ptr right_term);
  bool is_equiv_of_bool_var_and_term(SMT::Term_ptr left_term, SMT::Term_ptr right_term);

  void update_equiv_class_and_symbol_table(EquivalenceClass_ptr, EquivalenceClass_ptr);
  void update_equiv_class_and_symbol_table(EquivalenceClass_ptr, SMT::Variable_ptr);
  void update_equiv_class_and_symbol_table(EquivalenceClass_ptr, SMT::TermConstant_ptr);
  void update_equiv_class_and_symbol_table(EquivalenceClass_ptr, SMT::Term_ptr);
  void create_equiv_class_and_update_symbol_table(SMT::Variable_ptr, SMT::Variable_ptr);
  void create_equiv_class_and_update_symbol_table(SMT::Variable_ptr, SMT::TermConstant_ptr);
  void create_equiv_class_and_update_symbol_table(SMT::Variable_ptr, SMT::Term_ptr);

  SymbolTable_ptr symbol_table_;
  SMT::Variable_ptr left_variable_;
  SMT::Variable_ptr right_variable_;
  SMT::TermConstant_ptr term_constant_;
  SMT::Term_ptr unclassified_term_;
 private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_EQUIVALENCEGENERATOR_H_ */
