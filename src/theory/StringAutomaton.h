/*
 * StringAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_STRINGAUTOMATON_H_
#define THEORY_STRINGAUTOMATON_H_

#include <glog/logging.h>
#include "stranger/stranger_lib_internal.h"
#include "stranger/stranger.h"
#include "../utils/RegularExpression.h"
#include "Automaton.h"

namespace Vlab {
namespace Theory {

class StringAutomaton;
typedef StringAutomaton* StringAutomaton_ptr;

class StringAutomaton: public Automaton {
public:
	StringAutomaton();
	StringAutomaton(const StringAutomaton&);
	virtual ~StringAutomaton();

	virtual StringAutomaton_ptr clone() const;

private:
	static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_STRINGAUTOMATON_H_ */
