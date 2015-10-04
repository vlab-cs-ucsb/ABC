/*
 * BoolAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_BOOLAUTOMATON_H_
#define THEORY_BOOLAUTOMATON_H_

#include <array>

#include <glog/logging.h>
#include <stranger.h>
#include <stranger_lib_internal.h>
#include "Automaton.h"

namespace Vlab {
namespace Theory {

class BoolAutomaton;
typedef BoolAutomaton* BoolAutomaton_ptr;
typedef DFA* DFA_ptr;

class BoolAutomaton: public Automaton {
public:
  BoolAutomaton(DFA_ptr dfa);
  BoolAutomaton(DFA_ptr dfa, int num_of_variables);
  BoolAutomaton(const BoolAutomaton&);
  virtual ~BoolAutomaton();

  virtual BoolAutomaton_ptr clone() const;

  static BoolAutomaton_ptr makeTrue(int num_of_variables = BoolAutomaton::DEFAULT_NUM_OF_VARIABLES,
      int* variable_indices = BoolAutomaton::DEFAULT_VARIABLE_INDICES);
  static BoolAutomaton_ptr makeFalse(int num_of_variables = BoolAutomaton::DEFAULT_NUM_OF_VARIABLES,
      int* variable_indices = BoolAutomaton::DEFAULT_VARIABLE_INDICES);

  void toDot();
protected:
  DFA_ptr dfa;
  int num_of_variables;
  static int DEFAULT_NUM_OF_VARIABLES;
  static int* DEFAULT_VARIABLE_INDICES;
  static unsigned* DEFAULT_UNSIGNED_VARIABLE_INDICES;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BOOLAUTOMATON_H_ */
