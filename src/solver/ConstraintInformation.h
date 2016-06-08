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

#include <cstdbool>
#include <set>

#include "smt/typedefs.h"

namespace Vlab {
namespace Solver {

class ConstraintInformation {
 public:
  ConstraintInformation();
  virtual ~ConstraintInformation();

  bool is_component(SMT::Visitable_ptr);
  void add_component(SMT::Visitable_ptr);
  void remove_component(SMT::Visitable_ptr);
 private:
  std::set<SMT::Visitable_ptr> components_;
};

using ConstraintInformation_ptr = ConstraintInformation*;

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_CONSTRAINTINFORMATION_H_ */
