/*
 * BoolAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "BoolAutomaton.h"

namespace Vlab {
namespace Theory {

const int BoolAutomaton::VLOG_LEVEL = 9;

BoolAutomaton::BoolAutomaton()
        : Automaton(Automaton::Type::STRING) {
}

BoolAutomaton::BoolAutomaton(const BoolAutomaton& other)
        : Automaton(Automaton::Type::STRING) {
}

BoolAutomaton_ptr BoolAutomaton::clone() const {
  return new BoolAutomaton(*this);
}

BoolAutomaton::~BoolAutomaton() {
}

} /* namespace Theory */
} /* namespace Vlab */
