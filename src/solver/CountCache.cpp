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


void CountCache::add_int_matrix(const Matrix& matrix) {
  int_matrices_.push_back(matrix);
}

void CountCache::add_unsigned_int_matrix(const Matrix& matrix) {
  unsigned_int_matrices_.push_back(matrix);
}

void CountCache::add_unary_int_matrix(const Matrix& matrix) {
  unary_int_matrices_.push_back(matrix);
}

void CountCache::add_str_matrix(const Matrix& matrix) {
  str_matrices_.push_back(matrix);
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


  for (Matrix& m : int_matrices_) {
    unsigned long power = bound + 1; // sign bit
    Eigen::SparseVector<Theory::BigInteger> v (m.rows());
    v = m.innerVector(m.cols() - 1);

    while (power > 0) {
      v = m * v;
      --power;
    }

    result = result * v.coeff(m.cols() - 1);
  }

  for (Matrix& m : unsigned_int_matrices_) {
    unsigned long power = bound;
    Eigen::SparseVector<Theory::BigInteger> v (m.rows());
    v = m.innerVector(m.cols() - 1);

    while (power > 0) {
      v = m * v;
      --power;
    }

    result = result * v.coeff(m.cols() - 1);
  }

  if (unary_int_matrices_.size() > 0) {
    unsigned long base = 1;
    auto shift = bound;
    CHECK_LT(shift, std::numeric_limits<unsigned long>::digits);
    unsigned long upper_bound = (base << shift) - 1;
    for (Matrix& m : unary_int_matrices_) {
      unsigned long power = upper_bound + 1;
      Eigen::SparseVector<Theory::BigInteger> v (m.rows());
      v = m.innerVector(m.cols() - 1);

      while (power > 0) {
        v = m * v;
        --power;
      }

      result = result * v.coeff(m.cols() - 1);
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
  LOG(FATAL) << "implement me";
  return 0;
}

} /* namespace Solver */
} /* namespace Vlab */
