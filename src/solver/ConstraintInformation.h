/*
 * ConstraintInformation.h
 *
 *  Created on: Jun 7, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef SRC_SOLVER_CONSTRAINTINFORMATION_H_
#define SRC_SOLVER_CONSTRAINTINFORMATION_H_

namespace Vlab {
namespace Solver {

class ConstraintInformation {
 public:
  ConstraintInformation();
  virtual ~ConstraintInformation();
};

using ConstraintInformation_ptr = ConstraintInformation*;

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_CONSTRAINTINFORMATION_H_ */
