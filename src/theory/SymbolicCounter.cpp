/*
 * SymbolicCounter.cpp
 *
 *  Created on: Oct 31, 2016
 *      Author: baki
 */

#include "SymbolicCounter.h"

namespace Vlab {
namespace Theory {

const int SymbolicCounter::VLOG_LEVEL = 9;

SymbolicCounter::SymbolicCounter() : type_(SymbolicCounter::Type::STRING), bound_(0) {

}

SymbolicCounter::~SymbolicCounter() {
}

SymbolicCounter::Type SymbolicCounter::type() {
  return type_;
}

void SymbolicCounter::set_type(const Type t) {
  type_ = t;
}

unsigned long SymbolicCounter::get_bound() {
  return bound_;
}

void SymbolicCounter::set_bound(const unsigned long bound) {
  bound_ = bound;
}

Eigen::SparseVector<BigInteger> SymbolicCounter::get_initialization_vector() const {
  return initialization_vector_;
}

void SymbolicCounter::set_initialization_vector(const Eigen::SparseVector<BigInteger>& initialization_vector) {
  initialization_vector_ = initialization_vector;
}

Eigen::SparseMatrix<BigInteger> SymbolicCounter::get_transition_count_matrix() const {
  return transition_count_matrix_;
}

void SymbolicCounter::set_transition_count_matrix(const Eigen::SparseMatrix<BigInteger>& transition_count_matrix) {
  transition_count_matrix_ = transition_count_matrix;
}

BigInteger SymbolicCounter::Count(const unsigned long bound) {
  unsigned long power = bound;

  if (SymbolicCounter::Type::BINARYINT == type_) {
    ++power; // handle sign bit
  } else if (SymbolicCounter::Type::UNARYINT == type_) {
    unsigned long base = 1;
    power = (base << bound) - 1;
  }

  if (power >= bound_) {
    power = power - bound_;
  } else {
    initialization_vector_ = transition_count_matrix_.innerVector(transition_count_matrix_.cols()-1);
  }

  while (power > 0) {
    initialization_vector_ = transition_count_matrix_ * initialization_vector_;
    --power;
  }

  bound_ = bound;
  if (SymbolicCounter::Type::BINARYINT == type_) {
    ++bound_; // handle sign bit
  }

  DVLOG(VLOG_LEVEL) << "Count(" << bound << ") = " << initialization_vector_.coeff(0);
  return initialization_vector_.coeff(0);
}

BigInteger SymbolicCounter::CountbyMatrixMultiplication(const unsigned long bound) {
  LOG(FATAL) << "not fixed yet";
  return 0;
  //  // matrix exponentiation is off by 1 because of artificial accepting state
//  int power = bound + 1;
//
//  Eigen::SparseMatrix<BigInteger> y;
//  bool has_odds = false;
//
//  while (power > 1) {
//    if (power % 2 == 0) {
//      power = power / 2;
//    } else {
//      power = (power - 1) / 2;
//      if (has_odds) {
//        y = x * y;
//      } else {
//        y = x;
//        has_odds = true;
//      }
//    }
//    x = x * x;
//  }
//
//  if (has_odds) {
//    x = x * y;
//  }
//
//  BigInteger result = x.coeff(this->dfa_->s, this->dfa_->ns);
//  return result;
}

} /* namespace Theory */
} /* namespace Vlab */
