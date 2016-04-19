/*
 * DependencySlicer.h
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#ifndef SOLVER_DEPENDENCYSLICER_H_
#define SOLVER_DEPENDENCYSLICER_H_


#include <glog/logging.h>
#include "smt/ast.h"
#include "options/Solver.h"
#include "SymbolTable.h"
#include "AstTraverser.h"
#include "VariableCollector.h"
#include "OptimizationRuleRunner.h"
#include "Component.h"


namespace Vlab {
namespace Solver {
class DependencySlicer: public AstTraverser {
public:
  DependencySlicer(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~DependencySlicer();
  void start();
  void end();
  void remap();

  void visitAnd(SMT::And_ptr);
  void setCallbacks();
  void visitOr(SMT::Or_ptr);
  void visitAssert(SMT::Assert_ptr);

private:
  static const int VLOG_LEVEL;
  std::map<SMT::Visitable_ptr, std::map<SMT::Variable_ptr, int>> ids;
  std::map<SMT::Visitable_ptr,int> n_component;
  bool term_phase;
  std::map<SMT::Visitable_ptr, std::vector<std::vector<SMT::Term_ptr>>> components;
  SMT::Visitable_ptr scope;

protected:
  SymbolTable_ptr symbol_table;
};


} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_DEPENDENCYSLICER_H_ */
