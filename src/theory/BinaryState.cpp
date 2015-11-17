/*
 * BinaryState.cpp
 *
 *  Created on: Nov 7, 2015
 *      Author: baki
 */

#include "BinaryState.h"

namespace Vlab {
namespace Theory {

BinaryState::BinaryState() :
      type(Type::VAL), V(0), B(0), d0(-1), d1(-1) {
}


BinaryState::BinaryState(Type t, int v, int b) :
      type(t), V(v), B(b), d0(-1), d1(-1) {
}

BinaryState::BinaryState(int v, int b) :
      type(Type::VAL), V(v), B(b), d0(-1), d1(-1) {

}

BinaryState::~BinaryState() {

}

std::string BinaryState::str() const {
  std::stringstream ss;

  switch (type) {
    case Type::VAL:
      ss << "VAL: ";
      break;
    case Type::REMT:
      ss << "REMT: ";
      break;
    case Type::REMF:
      ss << "REMF: ";
      break;
    default:
      ss << "NONE: ";
      break;
  }

  ss << "V(" << V << "), B(" << B << "), 0 -> " << d0 << " 1 -> " << d1;

  return ss.str();
}

BinaryState::Type BinaryState::getType() {
  return type;
}

void BinaryState::setType(Type t) {
  this->type = t;
}

int BinaryState::getV() {
  return V;
}

int BinaryState::getB() {
  return B;
}


int BinaryState::getd0() {
  return d0;
}

int BinaryState::getd1() {
  return d1;
}

void BinaryState::setTypeValueBit(Type t, int v, int b) {
  this->type = t;
  this->V = v;
  this->B = b;
}

void BinaryState::setd0(int d0) {
  this->d0 = d0;
}
void BinaryState::setd1(int d1) {
  this->d1 = d1;
}

void BinaryState::setd0d1(int d0, int d1) {
  this->d0 = d0;
  this->d1 = d1;
}


bool BinaryState::isEqualTo(Type t, int v, int b) {
  return (this->V == v and this->B == b and this->type == t);
}

bool BinaryState::isEqualTo(int v, int b) {
  return (this->V == v and this->B == b);
}

std::ostream& operator<<(std::ostream& os, const BinaryState& binary_state) {
  return os << binary_state.str();
}

} /* namespace Theory */
} /* namespace Vlab */
