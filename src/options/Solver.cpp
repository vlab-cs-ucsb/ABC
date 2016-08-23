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

std::string Solver::OUTPUT_PATH         = ".";
std::string Solver::SCRIPT_PATH         = ".";
bool Solver::MODEL_COUNTER_ENABLED      = false;
bool Solver::LIA_ENGINE_ENABLED         = true;
bool Solver::LIA_ONLY_CONSTRAINT        = true;
bool Solver::LIA_NATURAL_NUMBERS_ONLY   = false;
bool Solver::ENABLE_RELATIONAL_STRING_AUTOMATA = true;
bool Solver::FORCE_DNF_FORMULA = false;
bool Solver::ENABLE_IMPLICATIONS = false;
bool Solver::ENABLE_DEPENDENCY = true;
bool Solver::ENABLE_SORTING = true;
bool Solver::ENABLE_EQUIVALENCE = true;

} /* namespace Option */
} /* namespace Vlab */