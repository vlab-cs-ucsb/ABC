/*
 * StringAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_STRINGAUTOMATON_H_
#define THEORY_STRINGAUTOMATON_H_

#include <array>
#include <vector>
#include <sstream>

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
 * TODO Try to refactor libstranger functions here.
 * Method specific todos are listed in .cpp file
 * Number of variables in String automaton kept as a static member
 * An object member version can be introduced later on.
 */
class StringAutomaton: public Automaton {
public:
  StringAutomaton(DFA_ptr);
  StringAutomaton(DFA_ptr, int num_of_variables);
  StringAutomaton(const StringAutomaton&);
  virtual ~StringAutomaton();

  virtual StringAutomaton_ptr clone() const;

  static StringAutomaton_ptr makePhi(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeEmptyString(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeString(std::string str, int num_of_variables =
          StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeAnyString(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeChar(char c, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeCharRange(char from, char to, int num_of_variables =
          StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeAnyChar(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeRegexAuto(std::string regex, int num_of_variables =
          StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);

  StringAutomaton_ptr complement();
  StringAutomaton_ptr union_(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr intersect(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr difference(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr concatenate(StringAutomaton_ptr other_auto);

  StringAutomaton_ptr optional();
  StringAutomaton_ptr closure();
  StringAutomaton_ptr kleeneClosure();
  StringAutomaton_ptr repeat(unsigned min);
  StringAutomaton_ptr repeat(unsigned min, unsigned max);

  bool checkEquivalence(StringAutomaton_ptr other_auto);
  bool isEmptyLanguage();
  bool hasEmptyString();
  bool isEmptyString();

  void toDotAscii(bool print_sink = false, std::ostream& out = std::cout);
protected:

  static StringAutomaton_ptr makeRegexAuto(Util::RegularExpression_ptr regular_expression);
  static int* allocateAscIIIndexWithExtraBit(int length);
  static std::vector<char> getReservedWord(char last_char, int length);
  static char* binaryFormat(unsigned long n, int bit_length);

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

#endif /* THEORY_STRINGAUTOMATON_H_ */
