/*
 * ModelCounter.h
 *
 *  Created on: Oct 31, 2016
 *      Author: baki
 */

#ifndef SRC_SOLVER_MODELCOUNTER_H_
#define SRC_SOLVER_MODELCOUNTER_H_

#include <functional>
#include <vector>

#include <glog/logging.h>

#include "../cereal/types/vector.hpp"
#include "../theory/SymbolicCounter.h"
#include "../utils/Serialize.h"

namespace Vlab {
namespace Solver {

class ModelCounter {
 public:
  ModelCounter();
  virtual ~ModelCounter();
  void set_use_sign_integers(bool value);
  void set_num_of_unconstraint_int_vars(int n);
  void set_num_of_unconstraint_str_vars(int n);
  void add_constant(int c);
  void add_symbolic_counter(const Theory::SymbolicCounter& counter);
  Theory::BigInteger CountInts(const unsigned long bound);
  Theory::BigInteger CountStrs(const unsigned long bound);
  Theory::BigInteger Count(const unsigned long int_bound, const unsigned long str_bound);

  template <class Archive>
  void save(Archive& ar) const {
    ar(use_signed_integers_);
    ar(unconstraint_int_vars_);
    ar(unconstraint_str_vars_);
    ar(constant_ints_);
    ar(symbolic_counters_);
  }

  template <class Archive>
  void load(Archive& ar) {
    ar(use_signed_integers_);
    ar(unconstraint_int_vars_);
    ar(unconstraint_str_vars_);
    ar(constant_ints_);
    ar(symbolic_counters_);
  }

 protected:
  bool use_signed_integers_;
  int unconstraint_int_vars_;
  int unconstraint_str_vars_;
  std::vector<int> constant_ints_;
  std::vector<Theory::SymbolicCounter> symbolic_counters_;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_MODELCOUNTER_H_ */
