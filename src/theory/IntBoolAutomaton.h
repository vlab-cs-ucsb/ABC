/*
 * IntBoolAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_INTBOOLAUTOMATON_H_
#define THEORY_INTBOOLAUTOMATON_H_

#include "Automaton.h"

namespace Vlab {
namespace Theory {

class IntBoolAutomaton;
typedef IntBoolAutomaton* IntBoolAutomaton_ptr;

class IntBoolAutomaton: public Automaton {
public:
  IntBoolAutomaton();
  IntBoolAutomaton(const IntBoolAutomaton&);
  virtual ~IntBoolAutomaton();

  virtual IntBoolAutomaton_ptr clone() const;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_INTBOOLAUTOMATON_H_ */
