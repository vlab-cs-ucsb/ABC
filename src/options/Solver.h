/*
 * Solver.h
 *
 *  Created on: Dec 14, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef SRC_OPTIONS_SOLVER_H_
#define SRC_OPTIONS_SOLVER_H_

#include <string>

namespace Vlab {
namespace Option {

enum class Name : int {
  OUTPUT_PATH = 0,
  MODEL_COUNTER_ENABLED,
  LIA_ENGINE_ENABLED
};

class Solver {
public:
  static bool MODEL_COUNTER_ENABLED;
  static bool LIA_ENGINE_ENABLED;
  static std::string OUTPUT_PATH;
};

} /* namespace Option */
} /* namespace Vlab */

#endif /* SRC_OPTIONS_SOLVER_H_ */
