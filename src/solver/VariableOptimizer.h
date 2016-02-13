/*
 * VariableOptimizer.h
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#ifndef SOLVER_VARIABLEOPTIMIZER_H_
#define SOLVER_VARIABLEOPTIMIZER_H_

#include <stack>
#include <map>

#include <glog/logging.h>
#include "smt/ast.h"
#include "options/Solver.h"
#include "SymbolTable.h"
#include "AstTraverser.h"
#include "Counter.h"
#include "OptimizationRuleRunner.h"


namespace Vlab {
namespace Solver {

class VariableOptimizer: public AstTraverser {
public:
  VariableOptimizer(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~VariableOptimizer();
  void start();
  void end();

  void setCallbacks();
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void visitEq(SMT::Eq_ptr);

protected:
  void add_variable_substitution_rule(SMT::Variable_ptr, SMT::Variable_ptr, SMT::Term_ptr);
  void add_variable_substitution_rule(SMT::Variable_ptr, SMT::Term_ptr);

  SymbolTable_ptr symbol_table;

  SMT::Variable::Type target_type;
  bool existential_elimination_phase;
  std::map<SMT::Variable_ptr, int> eq_constraint_count;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_VARIABLEOPTIMIZER_H_ */
