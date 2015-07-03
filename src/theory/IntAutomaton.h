/*
 * IntAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_INTAUTOMATON_H_
#define THEORY_INTAUTOMATON_H_

#include "Automaton.h"

namespace Vlab {
namespace Theory {

class IntAutomaton;
typedef IntAutomaton* IntAutomaton_ptr;

class IntAutomaton: public Automaton {
public:
  IntAutomaton();
  IntAutomaton(const IntAutomaton&);
  virtual ~IntAutomaton();

  virtual IntAutomaton_ptr clone() const;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_INTAUTOMATON_H_ */
