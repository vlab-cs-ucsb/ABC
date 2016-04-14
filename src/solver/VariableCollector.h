/*
 * VariableCollector.h
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#ifndef SOLVER_VARIABLECOLLECTOR_H_
#define SOLVER_VARIABLECOLLECTOR_H_


#include <glog/logging.h>
#include "smt/ast.h"
#include "options/Solver.h"
#include "SymbolTable.h"
#include "AstTraverser.h"


namespace Vlab {
namespace Solver {
class VariableCollector: public AstTraverser {
public:
  VariableCollector(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~VariableCollector();

  void start();
  void end();

  void setCallbacks();
  void visitOr(SMT::Or_ptr);
  void visitAnd(SMT::And_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitQualIdentifier(SMT::QualIdentifier_ptr);
  void visitUnknownTerm(SMT::Unknown_ptr);

private:
  static const int VLOG_LEVEL;
  SymbolTable_ptr symbol_table;
  bool internal;

};



} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_VARIABLECOLLECTOR_H_ */
