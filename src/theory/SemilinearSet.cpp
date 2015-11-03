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

std::vector<int>& SemilinearSet::getPeriodicConstants() {
  return periodic_constants;
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

std::ostream& operator<<(std::ostream& os, const SemilinearSet& semilinear_set) {
  return os << semilinear_set.str();
}

} /* namespace Theory */
} /* namespace Vlab */
