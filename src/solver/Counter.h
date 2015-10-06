/*
 * Counter.h
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#ifndef SOLVER_COUNTER_H_
#define SOLVER_COUNTER_H_

#include <glog/logging.h>
#include "smt/ast.h"
#include "SymbolTable.h"
#include "AstTraverser.h"

namespace Vlab {
namespace Solver {

class Counter: public AstTraverser {
public:
  Counter(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~Counter();

  void start();
  void end();

  void setCallbacks();
  void visitOr(SMT::Or_ptr);
  void visitQualIdentifier(SMT::QualIdentifier_ptr);
  void visitUnknownTerm(SMT::Unknown_ptr);
protected:
  SymbolTable_ptr symbol_table;

private:
  static const int VLOG_LEVEL;

};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_COUNTER_H_ */
