/*
 * IntAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "IntAutomaton.h"

namespace Vlab {
namespace Theory {

const int IntAutomaton::VLOG_LEVEL = 9;

IntAutomaton::IntAutomaton()
	: Automaton (Automaton::Type::STRING) { }

IntAutomaton::IntAutomaton(const IntAutomaton& other)
	: Automaton (Automaton::Type::STRING) { }

IntAutomaton_ptr IntAutomaton::clone() const { return new IntAutomaton(*this); }

IntAutomaton::~IntAutomaton() { }

} /* namespace Theory */
} /* namespace Vlab */
