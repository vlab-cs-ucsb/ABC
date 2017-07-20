/*
 * SemilinearSet.cpp
 *
 *  Created on: Nov 5, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "SemilinearSet.h"

namespace Vlab {
namespace Theory {

SemilinearSet::SemilinearSet() :
      C(0), R(0) {
}

SemilinearSet::SemilinearSet(SemilinearSet& other) :
      C(other.C), R(other.R), constants(other.constants), periodic_constants(other.periodic_constants) {

}

SemilinearSet::~SemilinearSet() {
}

SemilinearSet_ptr SemilinearSet::clone() {
  return new SemilinearSet(*this);
}

std::string SemilinearSet::str() const {
  std::stringstream ss;

  ss << "C: " << C << ", ";
  ss << "R: " << R << ", ";
  ss << "constants: {";
  std::string separator = "";
  for (auto& v : constants) {
    ss << separator << v;
    separator = ", ";
  }
  ss << "}, ";
  separator = "";
  ss << "cycles: {";
  for (auto&v : periodic_constants) {
    ss << separator << "{" << C + v << " + " << R << " * k}";
    separator = ", ";
  }
  ss << "}";

  return ss.str();
}

int SemilinearSet::get_cycle_head() {
  return C;
}

void SemilinearSet::set_cycle_head(int value) {
  C = value;
}

int SemilinearSet::get_period() {
  return R;
}

void SemilinearSet::set_period(int value) {
  R = value;
}

std::vector<int>& SemilinearSet::get_constants() {
  return constants;
}

void SemilinearSet::set_constants(std::vector<int>& constants) {
  this->constants = constants;
}

std::vector<int>& SemilinearSet::get_periodic_constants() {
  return periodic_constants;
}

void SemilinearSet::set_periodic_constants(std::vector<int>& periodic_constants) {
  this->periodic_constants = periodic_constants;
}

void SemilinearSet::add_constant(int value) {
  constants.push_back(value);
}

void SemilinearSet::add_periodic_constant(int value) {
  periodic_constants.push_back(value);
}
int SemilinearSet::get_number_of_constants() {
  return constants.size();
}

int SemilinearSet::get_number_of_periodic_constants() {
  return periodic_constants.size();
}

// TODO test and fix me
SemilinearSet_ptr SemilinearSet::Merge(SemilinearSet_ptr other) {
  SemilinearSet_ptr result = nullptr;
  if (this->is_empty_set()) {
    return other->clone();
  } else if (other->is_empty_set()) {
    return this->clone();
  }

  result = new SemilinearSet();

  result->constants = constants;
  result->constants.insert(result->constants.end(), other->constants.begin(), other->constants.end());
  Util::List::sort_and_remove_duplicate(result->constants);
  int cycle_head = 0;
  int p1 = this->R;
  int p2 = other->R;
  int lcm_value = Util::Math::lcm(p1, p2);

  if (not result->constants.empty()) {
    cycle_head = result->constants.back() + 1;
    int max_head = std::max(this->get_cycle_head(), other->get_cycle_head());
    if (max_head > lcm_value) {
      cycle_head = std::max(cycle_head, max_head);
    }
  } else {
    cycle_head = std::max(this->get_cycle_head(), other->get_cycle_head());
    if (cycle_head < lcm_value) {
      cycle_head = 0;
    }
  }

  result->set_cycle_head(cycle_head);

  int period;
  if (p1 == 0) {
    result->periodic_constants = other->periodic_constants;
    result->R = p2;
  } else if (p2 == 0) {
    result->periodic_constants = this->periodic_constants;
    result->R = this->R;
  } else {
    result->R = lcm_value;

    auto compute_periods = [result](SemilinearSet_ptr other) {
      int period = result->get_period();
      int cycle_head = result->get_cycle_head();
      int other_cycle_head = other->get_cycle_head();
      int other_period = other->get_period();
      for (auto p : other->get_periodic_constants()) {
        int sum = 0;
        while (sum < period) {
          int value = (other_cycle_head + p + sum);
          if (value >= cycle_head) {
            result->add_periodic_constant(value - cycle_head);
          } else {
            result->add_constant(value);
            result->add_periodic_constant(value - cycle_head + period);
          }
          sum += other_period;
        }
      }
    };

    compute_periods(this);
    compute_periods(other);
  }

  Util::List::sort_and_remove_duplicate(result->periodic_constants);

  return result;
}

bool SemilinearSet::is_empty_set() {
  return (C == 0 and R == 0 and constants.empty());
}

bool SemilinearSet::has_only_constants() {
  return (C == 0 and R == 0 and (not constants.empty()));
}

bool SemilinearSet::has_constants() {
  return (not constants.empty());
}

void SemilinearSet::clear() {
  C = 0;
  R = 0;
  constants.clear();
  periodic_constants.clear();
}

std::ostream& operator<<(std::ostream& os, const SemilinearSet& semilinear_set) {
  return os << semilinear_set.str();
}

} /* namespace Theory */
} /* namespace Vlab */
