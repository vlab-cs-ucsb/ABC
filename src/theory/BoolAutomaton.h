/*
 * BoolAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_BOOLAUTOMATON_H_
#define THEORY_BOOLAUTOMATON_H_

#include "Automaton.h"

namespace Vlab {
namespace Theory {

class BoolAutomaton;
typedef BoolAutomaton* BoolAutomaton_ptr;

class BoolAutomaton: public Automaton {
public:
	BoolAutomaton();
	BoolAutomaton(const BoolAutomaton&);
	virtual ~BoolAutomaton();

	virtual BoolAutomaton_ptr clone() const;

private:
	static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BOOLAUTOMATON_H_ */
