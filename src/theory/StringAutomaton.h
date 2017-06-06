/*
 * StringAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_STRINGAUTOMATON_H_
#define THEORY_STRINGAUTOMATON_H_

#include <cmath>
#include <cstring>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <utility>
#include <vector>

#include <glog/logging.h>

#include "../utils/RegularExpression.h"
#include "Automaton.h"
#include "UnaryAutomaton.h"
#include "Graph.h"
#include "GraphNode.h"
#include "IntAutomaton.h"
#include "StringFormula.h"
#include "RelationalStringAutomaton.h"

namespace Vlab {
namespace Theory {

class StringAutomaton;
typedef StringAutomaton* StringAutomaton_ptr;
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

  static StringAutomaton_ptr makePhi(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeEmptyString(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeString(std::string str, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeAnyString(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeAnyStringOtherThan(std::string str, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeChar(char c, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeCharRange(char from, char to, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeAnyChar(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeRegexAuto(std::string regex, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeLengthEqual(int length, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeLengthLessThan(int length, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeLengthLessThanEqual(int length, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeLengthGreaterThan(int length, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeLengthGreaterThanEqual(int length, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  static StringAutomaton_ptr makeLengthRange(int start, int end, int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  StringAutomaton_ptr complement();
  StringAutomaton_ptr union_(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr intersect(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr difference(StringAutomaton_ptr other_auto);
  StringAutomaton_ptr concat(StringAutomaton_ptr other_auto);

  StringAutomaton_ptr optional();
  StringAutomaton_ptr closure();
  StringAutomaton_ptr kleeneClosure();
  StringAutomaton_ptr repeat(unsigned min);
  StringAutomaton_ptr repeat(unsigned min, unsigned max);

  StringAutomaton_ptr suffixes();
  StringAutomaton_ptr suffixesAtIndex(int index);
  StringAutomaton_ptr suffixesFromIndex(int start);
  StringAutomaton_ptr suffixesFromTo(int start, int end);
  StringAutomaton_ptr prefixes();
  StringAutomaton_ptr prefixesUntilIndex(int end);
  StringAutomaton_ptr prefixesAtIndex(int index);
  StringAutomaton_ptr subStrings();

  StringAutomaton_ptr CharAt(const int index);
  StringAutomaton_ptr CharAt(IntAutomaton_ptr index_auto);
  StringAutomaton_ptr SubString(const int start);
  /**
   * TODO decide on substring second param; which one is better:
   * end index, or length of substring
   */
  StringAutomaton_ptr SubString(const int start, const int end);
  StringAutomaton_ptr SubString(IntAutomaton_ptr length_auto, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr subString(int start, IntAutomaton_ptr end_auto);
  StringAutomaton_ptr subStringLastOf(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr subStringFirstOf(StringAutomaton_ptr search_auto);

  IntAutomaton_ptr indexOf(StringAutomaton_ptr search_auto);
  IntAutomaton_ptr lastIndexOf(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr contains(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr begins(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr ends(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr toUpperCase();
  StringAutomaton_ptr toLowerCase();
  StringAutomaton_ptr trim();

  StringAutomaton_ptr replace(StringAutomaton_ptr search_auto, StringAutomaton_ptr replace_auto);

  StringAutomaton_ptr getAnyStringNotContainsMe();

  DFA_ptr unaryLength();
  UnaryAutomaton_ptr toUnaryAutomaton();
  IntAutomaton_ptr parseToIntAutomaton();
  IntAutomaton_ptr length();
  StringAutomaton_ptr restrictLengthTo(int length);
  StringAutomaton_ptr restrictLengthTo(IntAutomaton_ptr length_auto);
  StringAutomaton_ptr restrictIndexOfTo(int index, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr restrictIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr restrictLastIndexOfTo(int index, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr restrictLastIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr restrictLastOccuranceOf(StringAutomaton_ptr search_auto);

  StringAutomaton_ptr restrictFromIndexToEndTo(int index, StringAutomaton_ptr sub_string_auto);
  StringAutomaton_ptr restrictFromIndexToEndTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto);
  StringAutomaton_ptr restrictAtIndexTo(int index, StringAutomaton_ptr sub_string_auto);
  StringAutomaton_ptr restrictAtIndexTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto);

  /**
   * TODO Pre image computations can be gudied by a range auto
   * which is the set that a pre image computation can takes values from,
   * it corresponds to post image value of the operation
   */

  StringAutomaton_ptr preToUpperCase(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preToLowerCase(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preTrim(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr preConcatLeft(StringAutomaton_ptr right_auto);
  StringAutomaton_ptr preConcatRight(StringAutomaton_ptr left_auto);

  StringAutomaton_ptr preReplace(StringAutomaton_ptr searchAuto, std::string replaceString, StringAutomaton_ptr rangeAuto = nullptr);

  bool hasEmptyString();
  bool isEmptyString();
  bool isAcceptingSingleString();
  std::string getAnAcceptingString();

  StringFormula_ptr get_formula();
  void set_formula(StringFormula_ptr formula);

protected:

  static StringAutomaton_ptr makeRegexAuto(Util::RegularExpression_ptr regular_expression);

  // TODO figure out better name
//  static StringAutomaton_ptr dfaSharpStringWithExtraBit(int num_of_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
//      int* variable_indices = StringAutomaton::DEFAULT_VARIABLE_INDICES);

  bool hasExceptionToValidStateFrom(int state, std::vector<char>& exception);
  std::vector<int> getAcceptingStates();

  StringAutomaton_ptr indexOfHelper(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr lastIndexOfHelper(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr getDuplicateStateAutomaton();
  StringAutomaton_ptr toQueryAutomaton();
  StringAutomaton_ptr search(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr removeReservedWords();
  void add_print_label(std::ostream& out) override;

  StringFormula_ptr formula_;
  static int DEFAULT_NUM_OF_VARIABLES;

private:
  static int name_counter;
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_STRINGAUTOMATON_H_ */
