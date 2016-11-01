/*
 * CountCache.h
 *
 *  Created on: Oct 31, 2016
 *      Author: baki
 */

#ifndef SRC_SOLVER_COUNTCACHE_H_
#define SRC_SOLVER_COUNTCACHE_H_

#include <functional>
#include <vector>

#include <glog/logging.h>

#include "../boost/multiprecision/cpp_int.hpp"
#include "../Eigen/SparseCore"
#include "../cereal/archives/binary.hpp"
#include "../theory/SymbolicCounter.h"
#include "../utils/Math.h"

namespace Vlab {
namespace Solver {

class CountCache {
  using Matrix = Eigen::SparseMatrix<Theory::BigInteger>;
 public:
  CountCache();
  virtual ~CountCache();
  void add_constant(int c);
  void add_symbolic_counter(const Theory::SymbolicCounter& counter);
  Theory::BigInteger CountInts(const unsigned long bound);
  Theory::BigInteger CountStrs(const unsigned long bound);
  Theory::BigInteger Count(const unsigned long int_bound, const unsigned long str_bound);

 protected:
  int unconstraint_int_vars_;
  int unconstraint_str_vars_;
  std::vector<int> constant_ints_;
  std::vector<Theory::SymbolicCounter> symbolic_counters_;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_COUNTCACHE_H_ */
