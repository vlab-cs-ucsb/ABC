/*
 * IntBoolAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "IntBoolAutomaton.h"

namespace Vlab {
namespace Theory {

const int IntBoolAutomaton::VLOG_LEVEL = 9;

IntBoolAutomaton::IntBoolAutomaton()
        : Automaton(Automaton::Type::STRING) {
}

IntBoolAutomaton::IntBoolAutomaton(const IntBoolAutomaton& other)
        : Automaton(Automaton::Type::STRING) {
}

IntBoolAutomaton_ptr IntBoolAutomaton::clone() const {
  return new IntBoolAutomaton(*this);
}

IntBoolAutomaton::~IntBoolAutomaton() {
}

} /* namespace Theory */
} /* namespace Vlab */
