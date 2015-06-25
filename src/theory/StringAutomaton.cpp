/*
 * StringAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "StringAutomaton.h"

namespace Vlab {
namespace Theory {

const int StringAutomaton::VLOG_LEVEL = 9;

StringAutomaton::StringAutomaton()
	: Automaton (Automaton::Type::STRING) { }

StringAutomaton::StringAutomaton(const StringAutomaton& other)
	: Automaton (Automaton::Type::STRING) { }

StringAutomaton_ptr StringAutomaton::clone() const { return new StringAutomaton(*this); }

StringAutomaton::~StringAutomaton() { }

} /* namespace Theory */
} /* namespace Vlab */
