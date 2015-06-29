/*
 * StringAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "StringAutomaton.h"

namespace Vlab {
namespace Theory {

const int StringAutomaton::VLOG_LEVEL = 8;

const int StringAutomaton::num_ascii_track = 8;

int* StringAutomaton::indices_main = allocateAscIIIndexWithExtraBit(StringAutomaton::num_ascii_track);
unsigned* StringAutomaton::unsigned_indices_main = StringAutomaton::get_unsigned_indices_main(StringAutomaton::num_ascii_track);

StringAutomaton::StringAutomaton(DFA_ptr dfa)
	: Automaton (Automaton::Type::STRING), dfa (dfa) { }

StringAutomaton::StringAutomaton(const StringAutomaton& other)
	: Automaton (Automaton::Type::STRING), dfa (other.dfa) { }

StringAutomaton::~StringAutomaton() {
	dfaFree(dfa);
	dfa = nullptr;
}

StringAutomaton_ptr StringAutomaton::clone() const { return new StringAutomaton(*this); }

StringAutomaton_ptr StringAutomaton::makeAnyString() {
	DVLOG(VLOG_LEVEL) << id << " = makeAnyString()";

	DFA_ptr any_string_dfa = dfaAllStringASCIIExceptReserveWords(StringAutomaton::num_ascii_track, StringAutomaton::indices_main);
	StringAutomaton_ptr any_string = new StringAutomaton(any_string_dfa);
	return any_string;
}

void StringAutomaton::toDotAscii(bool print_sink, std::ostream& out) {
	int sink_status = (print_sink) ? 1 : 0;
	sink_status = (dfa->ns == 1 and dfa->f[0] == -1) ? 2 : sink_status;
	dfaPrintGraphvizAsciiRange(dfa, StringAutomaton::num_ascii_track, StringAutomaton::indices_main, sink_status);
}

} /* namespace Theory */
} /* namespace Vlab */
