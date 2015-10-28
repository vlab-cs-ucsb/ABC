/*
 * MockBinaryIntAutomaton.h
 *
 *  Created on: Oct 30, 2015
 *      Author: baki
 */

#ifndef TEST_MOCK_THEORY_MOCKBINARYINTAUTOMATON_H_
#define TEST_MOCK_THEORY_MOCKBINARYINTAUTOMATON_H_

#include "gtest/gtest.h"
#include "gmock/gmock.h"
#include "theory/ArithmeticFormula.h"
#include "theory/BinaryIntAutomaton.h"

namespace Vlab {
namespace Test {
namespace Mock {

using namespace Vlab::Theory;

class BinaryIntAutomatonInterface {
public:
  virtual ~BinaryIntAutomatonInterface() { }
  virtual BinaryIntAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr formula) = 0;
  virtual BinaryIntAutomaton_ptr makeEquality(ArithmeticFormula_ptr formula) = 0;
};

class TestableBinaryIntAutomaton : public BinaryIntAutomaton, public BinaryIntAutomatonInterface {

 public:
  using BinaryIntAutomaton::makeEquality; // changes access rights
  using BinaryIntAutomaton::makeNotEquality; // changes access rights
  using BinaryIntAutomaton::makeLessThan;
  using BinaryIntAutomaton::makeLessThanOrEqual;
  using BinaryIntAutomaton::makeGreaterThan;
  using BinaryIntAutomaton::makeGreaterThanOrEqual;

  virtual BinaryIntAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr formula) {
    return BinaryIntAutomaton::makeAutomaton(formula);
  }

  virtual BinaryIntAutomaton_ptr makeEquality(ArithmeticFormula_ptr formula) {
    return BinaryIntAutomaton::makeEquality(formula);
  }


};

class MockBinaryIntAutomaton : public TestableBinaryIntAutomaton {
public:
  MOCK_METHOD1(makeAutomaton, BinaryIntAutomaton_ptr(ArithmeticFormula_ptr formula));
  MOCK_METHOD1(makeEquality, BinaryIntAutomaton_ptr(ArithmeticFormula_ptr formula));
};

} /* namespace Mock */
} /* namespace Test */
} /* namespace Vlab */

#endif /* TEST_MOCK_THEORY_MOCKBINARYINTAUTOMATON_H_ */
