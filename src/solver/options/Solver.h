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

enum class Name: int {
  USE_SIGNED_INTEGERS = 0,
  USE_UNSIGNED_INTEGERS,
  USE_MULTITRACK_AUTO,
  USE_SINGLETRACK_AUTO,
  ENABLE_EQUIVALENCE_CLASSES,
  DISABLE_EQUIVALENCE_CLASSES,
  ENABLE_DEPENDENCY_ANALYSIS,
  DISABLE_DEPENDENCY_ANALYSIS,
  ENABLE_IMPLICATIONS,
  DISABLE_IMPLICATIONS,
  LIMIT_LEN_IMPLICATIONS,
  ENABLE_SORTING_HEURISTICS,
  DISABLE_SORTING_HEURISTICS,
	FORCE_DNF_FORMULA,
	COUNT_BOUND_EXACT,
  USE_SINGLE_AUTO,
  USE_REGEX_SPLITTER,
  USE_PREFIX_SHORTENER,
  REGEX_FLAG,
  OUTPUT_PATH,
  SCRIPT_PATH,
  CONCAT_COLLAPSE_HEURISTIC,
  DFA_TO_RE,
  GET_NUM_RANDOM_MODELS,
  COMPARE_REGEX_VARIABLE
};

class Solver {
public:
  static bool USE_SIGNED_INTEGERS;
  static bool USE_MULTITRACK_AUTO;
  static bool ENABLE_EQUIVALENCE_CLASSES;
  static bool ENABLE_DEPENDENCY_ANALYSIS;
  static bool ENABLE_IMPLICATIONS;
  static bool ENABLE_LEN_IMPLICATIONS;
  static bool ENABLE_SORTING_HEURISTICS;
  static bool FORCE_DNF_FORMULA;
  static bool COUNT_BOUND_EXACT;
  static bool USE_SINGLE_AUTO;
  static bool USE_REGEX_SPLITTER;
  static bool USE_PREFIX_SHORTENER;
  static bool CONCAT_COLLAPSE_HEURISTIC;
  static bool DFA_TO_RE;
  static bool GET_NUM_RANDOM_MODELS;
  static bool COMPARE_REGEX_VARIABLE;
  static std::string OUTPUT_PATH;
  static std::string SCRIPT_PATH;
};

} /* namespace Option */
} /* namespace Vlab */

#endif /* SRC_OPTIONS_SOLVER_H_ */
