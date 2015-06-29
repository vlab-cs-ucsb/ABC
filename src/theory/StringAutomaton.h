/*
 * StringAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_STRINGAUTOMATON_H_
#define THEORY_STRINGAUTOMATON_H_

#include <array>

#include <glog/logging.h>
#include <stranger.h>
#include <stranger_lib_internal.h>
#include "../utils/RegularExpression.h"
#include "Automaton.h"

namespace Vlab {
namespace Theory {

class StringAutomaton;
typedef StringAutomaton* StringAutomaton_ptr;
typedef DFA* DFA_ptr;
/**
 * TODO Try to refactor libstranger functions here
 */
class StringAutomaton: public Automaton {
public:
  StringAutomaton(DFA_ptr);
  StringAutomaton(const StringAutomaton&);
  virtual ~StringAutomaton();

  virtual StringAutomaton_ptr clone() const;

  static StringAutomaton_ptr makePhi();
  static StringAutomaton_ptr makeEmptyString();
  static StringAutomaton_ptr makeString(char c);
  static StringAutomaton_ptr makeString(std::string str);
  static StringAutomaton_ptr makeAnyString();

  void toDotAscii(bool print_sink = true, std::ostream& out = std::cout);
protected:
  static StringAutomaton_ptr makeString(std::string str, int num_of_variables, int variable_indices[]);

  static int* allocateAscIIIndexWithExtraBit(int length);

  DFA_ptr dfa;
  static int DEFAULT_NUM_OF_VARIABLES;
  static int* DEFAULT_VARIABLE_INDICES;
  static unsigned* DEFAULT_UNSIGNED_VARIABLE_INDICES;
private:

  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_STRINGAUTOMATON_H_ */
