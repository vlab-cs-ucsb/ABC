/*
 * IntegerAutomatonTest.h
 *
 *  Created on: Oct 29, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_BINARYINTAUTOMATONTEST_H_
#define THEORY_BINARYINTAUTOMATONTEST_H_


#include "../../src/theory/IntegerAutomaton.h"

#include "gtest/gtest.h"
#include "gmock/gmock.h"
#include "helper/FileHelper.h"
//#include "theory/mock/MockIntegerAutomaton.h"

namespace Vlab {
namespace Theory {
namespace Test {

class IntegerAutomatonTest : public ::testing::Test {
protected:
  virtual void SetUp();
  virtual void TearDown();

};

} /* namespace Test */
} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYINTAUTOMATONTEST_H_ */
