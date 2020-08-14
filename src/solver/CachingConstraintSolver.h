//
// Created by will on 10/10/19.
//

#ifndef ABC_CACHINGCONSTRAINTSOLVER_H
#define ABC_CACHINGCONSTRAINTSOLVER_H

#include "ConstraintSolver.h"
#include "../theory/Automaton.h"
#include "CacheManager.h"

namespace Vlab {
namespace Solver {

class CachingConstraintSolver: public Solver::ConstraintSolver {
public:

  CachingConstraintSolver(SMT::Script_ptr, SymbolTable_ptr, ConstraintInformation_ptr, CacheManager_ptr);
  virtual ~CachingConstraintSolver();

  void start() override;
  void end() override;

  void visitScript(SMT::Script_ptr) override;
  void visitAssert(SMT::Assert_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;

protected:
  // redox client for redis cache
  CacheManager *cache_manager_;

  std::vector<std::thread> serializers_;

  std::string root_key_;
  std::string last_serialized_data_;

private:
  void YieldWhileValuesLocked() {
//    while(symbol_table_->AreValuesLocked()) std::this_thread::yield();
  }

  static const int VLOG_LEVEL;

};

using CachingConstraintSolver_ptr = CachingConstraintSolver*;

}
}


#endif //ABC_CACHINGCONSTRAINTSOLVER_H
