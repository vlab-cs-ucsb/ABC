

#ifndef SOLVER_DEPENDENCYCHECKER_H_
#define SOLVER_DEPENDENCYCHECKER_H_


#include <glog/logging.h>
#include <hiredis/hiredis.h>
#include "smt/ast.h"
#include "options/Solver.h"
#include "Component.h"
#include "SymbolTable.h"





namespace Vlab {
namespace Solver {
class DependencyChecker {
public:
  DependencyChecker(SymbolTable_ptr symbol_table); 
  virtual ~DependencyChecker();
  void start();
  

private:
  SymbolTable_ptr symbol_table;
  redisContext* db;

  static const int VLOG_LEVEL;
};


} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_DEPENDENCYCHECKER_H_ */
