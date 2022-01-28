/*
 * Solver.cpp
 *
 *  Created on: Dec 14, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "Solver.h"

namespace Vlab {
namespace Option {

bool Solver::USE_SIGNED_INTEGERS = true;
bool Solver::USE_MULTITRACK_AUTO = true;
bool Solver::ENABLE_EQUIVALENCE_CLASSES = true;
bool Solver::ENABLE_DEPENDENCY_ANALYSIS = true;
bool Solver::ENABLE_IMPLICATIONS = true;
bool Solver::ENABLE_LEN_IMPLICATIONS = true;
bool Solver::ENABLE_SORTING_HEURISTICS = true;
bool Solver::FORCE_DNF_FORMULA = false;
bool Solver::COUNT_BOUND_EXACT = false;
bool Solver::USE_SINGLE_AUTO = false;
bool Solver::USE_REGEX_SPLITTER = false;
bool Solver::USE_PREFIX_SHORTENER = false;
bool Solver::CONCAT_COLLAPSE_HEURISTIC = false;


std::string Solver::OUTPUT_PATH         = ".";
std::string Solver::SCRIPT_PATH         = ".";
} /* namespace Option */
} /* namespace Vlab */
