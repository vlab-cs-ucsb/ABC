/*
 * StringAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_STRINGAUTOMATON_H_
#define THEORY_STRINGAUTOMATON_H_

#include <glog/logging.h>
#include <stranger_lib_internal.h>
#include <stranger.h>
#include "../utils/RegularExpression.h"
#include "Automaton.h"

namespace Vlab {
namespace Theory {

class StringAutomaton;
typedef StringAutomaton* StringAutomaton_ptr;
typedef DFA* DFA_ptr;

class StringAutomaton: public Automaton {
public:
	StringAutomaton(DFA_ptr);
	StringAutomaton(const StringAutomaton&);
	virtual ~StringAutomaton();

	virtual StringAutomaton_ptr clone() const;

	static StringAutomaton_ptr makeAnyString();

	void toDotAscii(bool print_sink = true, std::ostream& out = std::cout);
protected:
	DFA_ptr dfa;
	static const int num_ascii_track;
	static int* indices_main;
	static unsigned* unsigned_indices_main;
private:

	static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_STRINGAUTOMATON_H_ */
