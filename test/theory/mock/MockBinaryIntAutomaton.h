/*
 * MockIntegerAutomaton.h
 *
 *  Created on: Oct 30, 2015
 *      Author: baki
 */

#ifndef TEST_MOCK_THEORY_MOCKBINARYINTAUTOMATON_H_
#define TEST_MOCK_THEORY_MOCKBINARYINTAUTOMATON_H_

#include "../../../src/theory/IntegerAutomaton.h"
#include "gtest/gtest.h"
#include "gmock/gmock.h"
#include "theory/ArithmeticFormula.h"

namespace Vlab {
namespace Test {
namespace Mock {

using namespace Vlab::Theory;

class IntegerAutomatonInterface {
public:
  virtual ~IntegerAutomatonInterface() { }
  virtual IntegerAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr formula) = 0;
  virtual IntegerAutomaton_ptr makeEquality(ArithmeticFormula_ptr formula) = 0;
};

class TestableIntegerAutomaton : public IntegerAutomaton, public IntegerAutomatonInterface {

 public:
  using IntegerAutomaton::MakeIntEquality; // changes access rights
  using IntegerAutomaton::makeNotEquality; // changes access rights
  using IntegerAutomaton::makeLessThan;
  using IntegerAutomaton::makeLessThanOrEqual;
  using IntegerAutomaton::makeGreaterThan;
  using IntegerAutomaton::makeGreaterThanOrEqual;

  virtual IntegerAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr formula) {
    return IntegerAutomaton::makeAutomaton(formula);
  }

  virtual IntegerAutomaton_ptr makeEquality(ArithmeticFormula_ptr formula) {
    return IntegerAutomaton::MakeIntEquality(formula);
  }


};

class MockIntegerAutomaton : public TestableIntegerAutomaton {
public:
  MOCK_METHOD1(makeAutomaton, IntegerAutomaton_ptr(ArithmeticFormula_ptr formula));
  MOCK_METHOD1(makeEquality, IntegerAutomaton_ptr(ArithmeticFormula_ptr formula));
};

} /* namespace Mock */
} /* namespace Test */
} /* namespace Vlab */

#endif /* TEST_MOCK_THEORY_MOCKBINARYINTAUTOMATON_H_ */
