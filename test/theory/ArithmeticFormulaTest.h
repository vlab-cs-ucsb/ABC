/*
 * ArithmeticFormulaTest.h
 *
 *  Created on: Oct 21, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_ARITHMETICFORMULATEST_H_
#define THEORY_ARITHMETICFORMULATEST_H_

#include <vector>

#include "gtest/gtest.h"
#include "gmock/gmock.h"
#include "theory/ArithmeticFormula.h"

namespace Vlab {
namespace Theory {
namespace Test {

class ArithmeticFormulaTest : public ::testing::Test {
protected:
  virtual void SetUp();
  virtual void TearDown();

  std::map<std::string, int> variable_coefficient_map_;
};

} /* namespace Test */
} /* namespace Theory */
} /* namespace Vlab */


#endif /* THEORY_ARITHMETICFORMULATEST_H_ */
