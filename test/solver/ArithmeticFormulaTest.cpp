/*
 * ArithmeticFormulaTest.cpp
 *
 *  Created on: Oct 21, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "ArithmeticFormulaTest.h"

namespace Vlab {
namespace Test {
namespace Solver {

namespace Theory = Vlab::Theory;

void ArithmeticFormulaTest::SetUp() {
  coefficients = {1,2,3};
  coeff_index_map = {{"x", 0}, {"y", 1}, {"z", 2}};
}

void ArithmeticFormulaTest::TearDown() {
}

TEST_F(ArithmeticFormulaTest, ConstructorNoArgs) {
  Theory::ArithmeticFormula formula;
  EXPECT_EQ(0, formula.getConstant());
  EXPECT_TRUE(Theory::ArithmeticFormula::Type::NONE == formula.getType());
}

TEST_F(ArithmeticFormulaTest, ConstructorWithArgs) {
  EXPECT_EQ(0,1);
}



} /* namespace Solver */
} /* namespace Test */
} /* namespace Vlab */
