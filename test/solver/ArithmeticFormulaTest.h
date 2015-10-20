/*
 * ArithmeticFormulaTest.h
 *
 *  Created on: Oct 21, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef SOLVER_ARITHMETICFORMULATEST_H_
#define SOLVER_ARITHMETICFORMULATEST_H_

#include <vector>

#include "gtest/gtest.h"
#include "theory/ArithmeticFormula.h"

namespace Vlab {
namespace Test {
namespace Solver {

class ArithmeticFormulaTest : public ::testing::Test {
protected:
  virtual void SetUp();
  virtual void TearDown();

  std::map<std::string, int> coeff_index_map;
  std::vector<int> coefficients;
};

} /* namespace Solver */
} /* namespace Test */
} /* namespace Vlab */

#endif /* SOLVER_ARITHMETICFORMULATEST_H_ */
