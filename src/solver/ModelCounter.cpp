/*
 * ModelCounter.cpp
 *
 *  Created on: Oct 31, 2016
 *      Author: baki
 */

#include "ModelCounter.h"

namespace Vlab {
namespace Solver {

ModelCounter::ModelCounter() : use_signed_integers_{true}, unconstraint_int_vars_ {0}, unconstraint_str_vars_ {0} {
}

ModelCounter::~ModelCounter() {
}

void ModelCounter::set_use_sign_integers(bool value) {
  use_signed_integers_ = value;
}

void ModelCounter::set_num_of_unconstraint_int_vars(int n) {
  unconstraint_int_vars_ = n;
}

void ModelCounter::set_num_of_unconstraint_str_vars(int n) {
  unconstraint_str_vars_ = n;
}

void ModelCounter::add_constant(int c) {
  constant_ints_.push_back(c);
}


void ModelCounter::add_symbolic_counter(const Theory::SymbolicCounter& counter) {
  symbolic_counters_.push_back(counter);
}


Theory::BigInteger ModelCounter::CountInts(const unsigned long bound) {
  Theory::BigInteger result(1);

  for (int i : constant_ints_) {
    Theory::BigInteger value(i);
    auto shift = bound;

    Theory::BigInteger base(1);
    Theory::BigInteger upper_bound = (base << shift) - 1;

    Theory::BigInteger lower_bound(0);
    if (use_signed_integers_) {
      Theory::BigInteger base2(-1);
      lower_bound = (base2 << shift) + 1;
    }

    if (not (value <= upper_bound and value >= lower_bound)) {
     return 0; // no need to compute further
    }
  }


  for (Theory::SymbolicCounter& counter : symbolic_counters_) {
    if (Theory::SymbolicCounter::Type::STRING != counter.type()) {
      result = result * counter.Count(bound);
    }
  }

  if (unconstraint_int_vars_ > 0) {
   if (use_signed_integers_) {
     result = result
            * boost::multiprecision::pow(
                (boost::multiprecision::pow(
                    boost::multiprecision::cpp_int(2),
                    (2 * bound)) - 1),
                unconstraint_int_vars_);
   } else {
     result = result
         * boost::multiprecision::pow(boost::multiprecision::cpp_int(2),
                                      (unconstraint_int_vars_ * bound));
   }
  }

  return result;
}

Theory::BigInteger ModelCounter::CountStrs(const unsigned long bound) {
  Theory::BigInteger result(1);

  for (Theory::SymbolicCounter& counter : symbolic_counters_) {
    if (Theory::SymbolicCounter::Type::STRING == counter.type()) {
      result = result * counter.Count(bound);
    }
  }

  if (unconstraint_str_vars_ > 0) {
   result = result
       * boost::multiprecision::pow(boost::multiprecision::cpp_int(256),
                                    (unconstraint_str_vars_ * bound));
  }

  return result;
}

Theory::BigInteger ModelCounter::Count(const unsigned long int_bound, const unsigned long str_bound) {
  return CountInts(int_bound) * CountStrs(str_bound);
}

} /* namespace Solver */
} /* namespace Vlab */
