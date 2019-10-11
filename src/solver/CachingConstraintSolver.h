//
// Created by will on 10/10/19.
//

#ifndef ABC_CACHINGCONSTRAINTSOLVER_H
#define ABC_CACHINGCONSTRAINTSOLVER_H

#include "ConstraintSolver.h"
#include "../theory/Automaton.h"
#include <redox.hpp>

namespace Vlab {
namespace Solver {

class CachingConstraintSolver: public Solver::ConstraintSolver {
public:

  std::chrono::duration<double> diff;
  std::chrono::duration<double> diff2;

  std::chrono::duration<double> get_diff3() { return this->arithmetic_constraint_solver_.diff;}
  std::chrono::duration<double> get_diff4() { return this->arithmetic_constraint_solver_.diff2;}


  CachingConstraintSolver(SMT::Script_ptr, SymbolTable_ptr, ConstraintInformation_ptr, redox::Redox *);
  virtual ~CachingConstraintSolver();

  void start() override;
  void end() override;

  void visitScript(SMT::Script_ptr) override;
  void visitAssert(SMT::Assert_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;

  int num_hits() {return num_hits_;}
  int num_misses() {return num_misses_;}
  std::tuple<int,int> hit_statistic() {return hit_statistic_;};

protected:
  // redox client for redis cache
  redox::Redox *rdx_;
  int num_hits_;
  int num_misses_;
  std::tuple<int,int> hit_statistic_;

  std::vector<std::thread> serializers_;

  std::string root_key_;
  std::string last_serialized_data_;

private:
  static const int VLOG_LEVEL;

};

using CachingConstraintSolver_ptr = CachingConstraintSolver*;

}
}


#endif //ABC_CACHINGCONSTRAINTSOLVER_H
