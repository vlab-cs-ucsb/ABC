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
using StringAutomaton_ptr = StringAutomaton*;

class StringAutomaton: public Automaton {
public:
  StringAutomaton(const DFA_ptr);
  StringAutomaton(const DFA_ptr, const int number_of_bdd_variables);
  StringAutomaton(const StringAutomaton&);
  virtual ~StringAutomaton();

  virtual StringAutomaton_ptr clone() const;

  /**
   * Generates a string automaton that does not recognize any string
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakePhi(const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that recognizes only empty string
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeEmptyString(const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that recognizes given string
   * @param str
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeString(const std::string str, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that recognizes any string
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyString(const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that recognizes any string except the given string
   * @param str
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyOtherString(const std::string str, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that recognizes characters inclusive from a given character to a given character
   * @param from
   * @param to
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeCharRange(const char from, const char to, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any character. It is equivalent to the string automaton that accepts any strings with length 1
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyChar(const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts the strings defined by the given regular expression
   * @param regex_string
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeRegexAuto(const std::string regex_string, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts the strign defined by the given regular expression
   * @param regular_expression
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeRegexAuto(Util::RegularExpression_ptr regular_expression, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any string with the given length
   * @param length
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyStringLengthEqualTo(const int length, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any string with length less than the given length
   * @param length
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyStringLengthLessThan(const int length, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any string with length less than or equal the given length
   * @param length
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyStringLengthLessThanOrEqualTo(const int length, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any string with length greater than the given length
   * @param length
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyStringLengthGreaterThan(const int length, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any string with length greater than or equal to the given length
   * @param length
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyStringLengthGreaterThanOrEqualTo(const int length, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that accepts any string with length in the range of given start and end lengths
   * @param start
   * @param end
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakeAnyStringWithLengthInRange(const int start, const int end, const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  /**
   * Generates a string automaton that wraps the dfa
   * @param dfa
   * @param number_of_variables
   * @return
   */
  virtual StringAutomaton_ptr MakeAutomaton(DFA_ptr dfa, const int number_of_variables) override;


  // TODO baki left here: move common functions to base class, should be implemented similar to visitor pattern
  //StringAutomaton_ptr concat(StringAutomaton_ptr other_auto);

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