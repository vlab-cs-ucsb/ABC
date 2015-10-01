/*
 * StringAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_STRINGAUTOMATON_H_
#define THEORY_STRINGAUTOMATON_H_

#include <sstream>
#include <iostream>
#include <fstream>
#include <array>
#include <vector>
#include <map>
#include <set>
#include <stack>
#include <queue>

#include <glog/logging.h>
#include <stranger.h>
#include <stranger_lib_internal.h>
#include "../utils/RegularExpression.h"
#include "Graph.h"
#include "DAGraph.h"
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
  static StringAutomaton_ptr makeLengthRange(int start, int end, int num_of_variables =
          StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeLengthEqual(int length, int num_of_variables =
            StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeLengthLessThan(int length, int num_of_variables =
              StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeLengthLessThanEqual(int length, int num_of_variables =
                StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeLengthGreaterThan(int length, int num_of_variables =
                  StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  static StringAutomaton_ptr makeLengthGreaterThanEqual(int length, int num_of_variables =
                    StringAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);

  StringAutomaton_ptr complement();
  StringAutomaton_ptr union_(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr intersect(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr difference(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr concatenate(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr concat(StringAutomaton_ptr other_auto);

  StringAutomaton_ptr optional();
  StringAutomaton_ptr closure();
  StringAutomaton_ptr kleeneClosure();
  StringAutomaton_ptr repeat(unsigned min);
  StringAutomaton_ptr repeat(unsigned min, unsigned max);

  StringAutomaton_ptr suffixes();
  StringAutomaton_ptr prefixes();
  StringAutomaton_ptr suffixesFromIndex(int start);
  StringAutomaton_ptr prefixesUntilIndex(int end);
  StringAutomaton_ptr prefixesAtIndex(int index);

  StringAutomaton_ptr charAt(int index);
  StringAutomaton_ptr substring(int start);
  StringAutomaton_ptr substring(int start, int end);
  StringAutomaton_ptr indexOf(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr lastIndexOf(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr contains(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr begins(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr ends(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr toUpperCase();
  StringAutomaton_ptr toLowerCase();
  StringAutomaton_ptr trim();

  StringAutomaton_ptr replace(StringAutomaton_ptr search_auto, StringAutomaton_ptr replace_auto);

  DFA_ptr length();
  /**
   * TODO Pre image computations can be gudied by a range auto
   * which is the set that a pre image computation can takes values from,
   * it corresponds to post image value of the operation
   */

  StringAutomaton_ptr preCharAt(int index, StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preSubstring(int start, StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preSubstring(int start, int end, StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preContains();
  StringAutomaton_ptr preBegins();
  StringAutomaton_ptr preEnds();
  StringAutomaton_ptr preToUpperCase(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preToLowerCase(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preTrim(StringAutomaton_ptr rangeAuto = nullptr);

  StringAutomaton_ptr preReplace(StringAutomaton_ptr searchAuto, std::string replaceString, StringAutomaton_ptr rangeAuto = nullptr);

  bool checkEquivalence(StringAutomaton_ptr other_auto);
  bool isEmptyLanguage();
  bool hasEmptyString();
  bool isEmptyString();
  bool isAcceptingSingleString();
  std::string getString();

  void toDotAscii(bool print_sink = false, std::ostream& out = std::cout);
  // TODO merge toDot methods into one with options
  void toDot();
  void printBDD(std::ostream& out = std::cout);
  int inspectAuto(bool print_sink = false);

protected:

  static StringAutomaton_ptr makeRegexAuto(Util::RegularExpression_ptr regular_expression);
  static std::vector<char> getReservedWord(char last_char, int length, bool extra_bit = false);
  static char* binaryFormat(unsigned long n, int bit_length);
  // TODO figure out better name
  static StringAutomaton_ptr dfaSharpStringWithExtraBit(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
      int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);
  inline bool isSinkState(int state_id);
  inline bool isAcceptingState(int state_id);
  int getSinkState();
  bool isStartStateReachable();

  bool hasExceptionToValidStateFrom(int state, std::vector<char>& exception);
  int getNextStateFrom(int state, std::vector<char>& exception);
  std::vector<int> getAcceptingStates();

  std::set<int>* getNextStates(int state);

  void minimize();
  void project(unsigned num_of_variables);

  GraphOld* getGraph();
  Graph_ptr toGraph();

  static int DEFAULT_NUM_OF_VARIABLES;
  static int* DEFAULT_VARIABLE_INDICES;
  static unsigned* DEFAULT_UNSIGNED_VARIABLE_INDICES;

private:
  static int name_counter;
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_STRINGAUTOMATON_H_ */
