/*
 * CountCache.cpp
 *
 *  Created on: Oct 31, 2016
 *      Author: baki
 */

#include "CountCache.h"

namespace Vlab {
namespace Solver {

CountCache::CountCache() : unconstraint_int_vars_ {0}, unconstraint_str_vars_ {0} {
}

CountCache::~CountCache() {
}

void CountCache::add_constant(int c) {
  constant_ints_.push_back(c);
}


void CountCache::add_symbolic_counter(const Theory::SymbolicCounter& counter) {
  symbolic_counters_.push_back(counter);
}


Theory::BigInteger CountCache::CountInts(const unsigned long bound) {
  Theory::BigInteger result(1);

  for (int i : constant_ints_) {
    Theory::BigInteger value(i);
    Theory::BigInteger base(1);
    Theory::BigInteger base2(-1);
    auto shift = bound;
    Theory::BigInteger upper_bound = (base << shift) - 1;
    Theory::BigInteger lower_bound = (base2 << shift) + 1;
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
   result = result
       * boost::multiprecision::pow(boost::multiprecision::cpp_int(2),
                                    (unconstraint_int_vars_ * bound));
  }

  return result;
}

Theory::BigInteger CountCache::CountStrs(const unsigned long bound) {
  Theory::BigInteger result(1);
  for (Theory::SymbolicCounter& counter : symbolic_counters_) {
    if (Theory::SymbolicCounter::Type::STRING != counter.type()) {
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

Theory::BigInteger CountCache::Count(const unsigned long int_bound, const unsigned long str_bound) {
  return CountInts(int_bound) * CountStrs(str_bound);
}

} /* namespace Solver */
} /* namespace Vlab */
