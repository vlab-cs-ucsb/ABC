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

using SubstitutionMap = std::map<SMT::Variable_ptr, SMT::Term_ptr>;
using SubstitutionTable = std::map<SMT::Visitable_ptr, SubstitutionMap>;

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

  bool add_substitution_rule(SMT::Variable_ptr, SMT::Term_ptr);
  bool remove_substitution_rule(SMT::Variable_ptr);
  SMT::Term_ptr get_substitution_term(SMT::Variable_ptr);
  SubstitutionMap& get_substitution_map();
  SubstitutionTable& get_substitution_table();
  void reset_substitution_rules();


  SymbolTable_ptr symbol_table;

  SMT::Variable::Type target_type;
  bool existential_elimination_phase;
  std::map<SMT::Variable_ptr, int> eq_constraint_count;
  SubstitutionTable substitution_table;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_VARIABLEOPTIMIZER_H_ */
