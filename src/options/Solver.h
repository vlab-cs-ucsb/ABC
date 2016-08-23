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
  LIA_ENGINE_ENABLED,
  SCRIPT_PATH,
  LIA_ONLY_CONSTRAINT,
  LIA_NATURAL_NUMBERS_ONLY,
  ENABLE_RELATIONAL_STRING_AUTOMATA,
  FORCE_DNF_FORMULA,
  ENABLE_IMPLICATIONS,
  ENABLE_DEPENDENCY,
  ENABLE_SORTING,
  ENABLE_EQUIVALENCE
};

class Solver {
public:
  static bool MODEL_COUNTER_ENABLED;
  static bool LIA_ENGINE_ENABLED;
  static std::string OUTPUT_PATH;
  static std::string SCRIPT_PATH;
  static bool LIA_ONLY_CONSTRAINT;
  static bool LIA_NATURAL_NUMBERS_ONLY;
  static bool ENABLE_RELATIONAL_STRING_AUTOMATA;
  static bool FORCE_DNF_FORMULA;
  static bool ENABLE_IMPLICATIONS;
  static bool ENABLE_DEPENDENCY;
  static bool ENABLE_SORTING;
  static bool ENABLE_EQUIVALENCE;
};

} /* namespace Option */
} /* namespace Vlab */

#endif /* SRC_OPTIONS_SOLVER_H_ */