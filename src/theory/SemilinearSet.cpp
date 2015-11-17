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

SemilinearSet::~SemilinearSet() {
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

int SemilinearSet::getCycleHead() {
  return C;
}

void SemilinearSet::setCycleHead(int value) {
  C = value;
}

int SemilinearSet::getPeriod() {
  return R;
}

void SemilinearSet::setPeriod(int value) {
  R = value;
}

std::vector<int>& SemilinearSet::getConstants() {
  return constants;
}

void SemilinearSet::setConstants(std::vector<int>& constants) {
  this->constants = constants;
}

std::vector<int>& SemilinearSet::getPeriodicConstants() {
  return periodic_constants;
}

void SemilinearSet::setPeriodicConstants(std::vector<int>& periodic_constants) {
  this->periodic_constants = periodic_constants;
}

void SemilinearSet::addConstant(int value) {
  constants.push_back(value);
}

void SemilinearSet::addPeriodicConstant(int value) {
  periodic_constants.push_back(value);
}
int SemilinearSet::getNumberOfConstants() {
  return constants.size();
}

int SemilinearSet::getNumberOfPeriodicConstants() {
  return periodic_constants.size();
}

// TODO fix me
SemilinearSet_ptr SemilinearSet::merge(SemilinearSet_ptr other) {
  SemilinearSet_ptr result = new SemilinearSet();
  result->constants = constants;
  result->constants.insert(result->constants.end(), other->constants.begin(), other->constants.end());
  Util::List::sort_and_remove_duplicate(result->constants);
  int cycle_head = 0;
  if (not result->constants.empty()) {
    cycle_head = result->constants.back();
    if (cycle_head > 0) { // if the constants is not zero we need one more state
      cycle_head = cycle_head + 1;
    }
  }
  cycle_head = std::max({cycle_head, this->getCycleHead(), other->getCycleHead()});
  result->setCycleHead(cycle_head);

  int p1 = this->R;
  int p2 = other->R;

  int period;
  if (p1 == 0) {
    result->periodic_constants = other->periodic_constants;
    result->R = p2;
  } else if (p2 == 0) {
    result->periodic_constants = this->periodic_constants;
    result->R = this->R;
  } else {
    result->R = Util::Math::lcm(p1, p2);

    auto compute_periods = [result](SemilinearSet_ptr other) {
      int period = result->getPeriod();
      int cycle_head = result->getCycleHead();
      int other_cycle_head = other->getCycleHead();
      int other_period = other->getPeriod();
      for (auto p : other->getPeriodicConstants()) {
        int sum = 0;
        while (sum < period) {
          int value = (other_cycle_head + p + sum);
          if (value >= cycle_head) {
            result->addPeriodicConstant(value - cycle_head);
          } else {
            result->addConstant(value);
            result->addPeriodicConstant(value - cycle_head + period);
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

bool SemilinearSet::isEmptySet() {
  return (C == 0 and R == 0 and constants.empty());
}

bool SemilinearSet::hasOnlyConstants() {
  return (C == 0 and R == 0 and (not constants.empty()));
}

bool SemilinearSet::hasConstants() {
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
