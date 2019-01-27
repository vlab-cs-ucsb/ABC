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
#include "../utils/Serialize.h"

namespace Vlab {
namespace Theory {

class StringAutomaton;
using StringAutomaton_ptr = StringAutomaton*;

class StringAutomaton: public Automaton {
	using TransitionVector = std::vector<std::pair<std::string,std::string>>;
	using TransitionTable = std::map<std::pair<int,StringFormula::Type>,TransitionVector>;
public:
	StringAutomaton(const DFA_ptr, const int number_of_bdd_variables);
	StringAutomaton(const DFA_ptr, const int number_of_tracks, const int number_of_bdd_variables);
	StringAutomaton(const DFA_ptr, const int i_track, const int number_of_tracks, const int in_num_vars);
	StringAutomaton(const DFA_ptr, StringFormula_ptr formula, const int number_of_bdd_variables);
  StringAutomaton(const StringAutomaton&);
  virtual ~StringAutomaton();

  virtual StringAutomaton_ptr clone() const;

  template <class Archive>
  void save(Archive& ar) const {
    ar(num_tracks_);
    formula_->save(ar);
    Util::Serialize::save(ar,dfa_);
  }

  template <class Archive>
  void load(Archive& ar) {
    ar(num_tracks_);
    formula_->load(ar);
    Util::Serialize::load(ar,dfa_);
    if(dfa_ == nullptr) {
      LOG(INFO) << "Null!?";
    }
  }

  /**
   * Generates a string automaton that does not recognize any string
   * @param number_of_bdd_variables
   * @return
   */
  static StringAutomaton_ptr MakePhi(const int number_of_bdd_variables = StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

  static StringAutomaton_ptr MakePhi(StringFormula_ptr group_formula);
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
  virtual StringAutomaton_ptr MakeAutomaton(DFA_ptr dfa, Formula_ptr formula, const int number_of_variables) override;

  static StringAutomaton_ptr MakeAutomaton(StringFormula_ptr formula);
  static StringAutomaton_ptr MakeBegins(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeNotBegins(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeConcatExtraTrack(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeEquality(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeNotEquality(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeLessThan(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeLessThanOrEqual(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeGreaterThan(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeGreaterThanOrEqual(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeAnyStringUnaligned(StringFormula_ptr formula);
	static StringAutomaton_ptr MakeAnyStringAligned(StringFormula_ptr formula);

  StringAutomaton_ptr Complement();
  StringAutomaton_ptr Intersect(StringAutomaton_ptr);
  StringAutomaton_ptr Union(StringAutomaton_ptr);
  StringAutomaton_ptr Difference(StringAutomaton_ptr);
  StringAutomaton_ptr Concat(StringAutomaton_ptr);

  StringAutomaton_ptr Optional();
  StringAutomaton_ptr Closure();
  StringAutomaton_ptr KleeneClosure();
  StringAutomaton_ptr Repeat(unsigned min);
  StringAutomaton_ptr Repeat(unsigned min, unsigned max);

  StringAutomaton_ptr Suffixes();
  StringAutomaton_ptr SuffixesAtIndex(int index);
  StringAutomaton_ptr SuffixesFromIndex(int start);
  StringAutomaton_ptr SuffixesFromTo(int start, int end);
  StringAutomaton_ptr Prefixes();
  StringAutomaton_ptr PrefixesUntilIndex(int end);
  StringAutomaton_ptr PrefixesAtIndex(int index);
  StringAutomaton_ptr SubStrings();

  StringAutomaton_ptr CharAt(const int index);
  StringAutomaton_ptr CharAt(IntAutomaton_ptr index_auto);
  StringAutomaton_ptr SubString(const int start);
  /**
   * TODO decide on substring second param; which one is better:
   * end index, or length of substring
   */
  StringAutomaton_ptr SubString(const int start, const int end);
  StringAutomaton_ptr SubString(IntAutomaton_ptr length_auto, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr SubString(int start, IntAutomaton_ptr end_auto);
  StringAutomaton_ptr SubStringLastOf(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr SubStringFirstOf(StringAutomaton_ptr search_auto);

  IntAutomaton_ptr IndexOf(StringAutomaton_ptr search_auto);
  IntAutomaton_ptr LastIndexOf(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr Contains(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr Begins(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr Ends(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr ToUpperCase();
  StringAutomaton_ptr ToLowerCase();
  StringAutomaton_ptr Trim();

  StringAutomaton_ptr Replace(StringAutomaton_ptr search_auto, StringAutomaton_ptr replace_auto);

  StringAutomaton_ptr GetAnyStringNotContainsMe();

  UnaryAutomaton_ptr ToUnaryAutomaton();
  IntAutomaton_ptr ParseToIntAutomaton();
  IntAutomaton_ptr Length();
  StringAutomaton_ptr RestrictLengthTo(int length);
  StringAutomaton_ptr RestrictLengthTo(IntAutomaton_ptr length_auto);
  StringAutomaton_ptr RestrictIndexOfTo(int index, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr RestrictIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr RestrictLastIndexOfTo(int index, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr RestrictLastIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto);
  StringAutomaton_ptr RestrictLastOccuranceOf(StringAutomaton_ptr search_auto);

  StringAutomaton_ptr RestrictFromIndexToEndTo(int index, StringAutomaton_ptr sub_string_auto);
  StringAutomaton_ptr RestrictFromIndexToEndTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto);
  StringAutomaton_ptr RestrictAtIndexTo(int index, StringAutomaton_ptr sub_string_auto);
  StringAutomaton_ptr RestrictAtIndexTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto);

  /**
   * TODO Pre image computations can be guided by a range auto
   * which is the set that a pre image computation can takes values from,
   * it corresponds to post image value of the operation
   */

  StringAutomaton_ptr PreToUpperCase(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr PreToLowerCase(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr PreTrim(StringAutomaton_ptr rangeAuto = nullptr);
  StringAutomaton_ptr PreConcatLeft(StringAutomaton_ptr right_auto);
  StringAutomaton_ptr PreConcatRight(StringAutomaton_ptr left_auto);
  StringAutomaton_ptr PreReplace(StringAutomaton_ptr searchAuto, std::string replaceString, StringAutomaton_ptr rangeAuto = nullptr);

  StringAutomaton_ptr GetAutomatonForVariable(std::string var_name);
  StringAutomaton_ptr GetKTrack(int track);
  StringAutomaton_ptr ProjectAwayVariable(std::string var_name);
  StringAutomaton_ptr ProjectKTrack(int track);
  StringAutomaton_ptr ChangeIndicesMap(StringFormula_ptr new_formula);

  void SetSymbolicCounter() override;
  void SetSymbolicCounter(SymbolicCounter&);
  std::vector<std::string> GetAnAcceptingStringForEachTrack();
  std::map<std::string,std::vector<std::string>> GetModelsWithinBound(int num_models, int bound) override;
	int GetNumTracks() const;

  bool HasEmptyString();
  bool IsEmptyString();
  bool IsAcceptingSingleString();
  std::string GetAnAcceptingString();
  std::string GetAnAcceptingStringRandom();
  std::string GetMutatedAcceptingString(std::string model);

  StringFormula_ptr GetFormula();
  void SetFormula(StringFormula_ptr formula);


  static const TransitionVector& GenerateTransitionsForRelation(StringFormula::Type type, int bits_per_var);
	static DFA_ptr MakeBinaryRelationDfa(StringFormula::Type type, int bits_per_var, int num_tracks, int left_track, int right_track);
	static DFA_ptr MakeBinaryAlignedDfa(int left_track, int right_track, int total_tracks);
	static DFA_ptr MakeRelationalCharAtDfa(StringFormula_ptr formula, int bits_per_var, int num_tracks, int left_track, int right_track);
	static StringAutomaton_ptr MakePrefixSuffix(int left_track, int prefix_track, int suffix_track, int num_tracks);
  static StringAutomaton_ptr MakeConcatExtraTrack(int left_track, int right_track, int num_tracks, std::string str_constant);


	static bool IsExepEqualChar(std::vector<char> exep, std::vector<char> cvec, int var);
	static bool IsExepIncludeChar(std::vector<char> exep, std::vector<char> cvec, int var);

	static DFA_ptr PrependLambda(DFA_ptr dfa, int var);
	static DFA_ptr TrimLambdaPrefix(DFA_ptr dfa, int var, bool project_bit = true);
	static DFA_ptr TrimLambdaSuffix(DFA_ptr dfa, int var, bool project_bit = true);
	static DFA_ptr TrimPrefix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var);
	static DFA_ptr TrimSuffix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var);
	static DFA_ptr concat(DFA_ptr prefix_dfa, DFA_ptr suffix_dfa, int var);

	static DFA_ptr PreConcatPrefix(DFA_ptr concat_dfa, DFA_ptr suffix_dfa, int var);
	static DFA_ptr PreConcatSuffix(DFA_ptr concat_dfa, DFA_ptr prefix_dfa, int var);

protected:
  bool HasExceptionToValidStateFrom(int state, std::vector<char>& exception);
  std::vector<int> GetAcceptingStates();

  StringAutomaton_ptr IndexOfHelper(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr LastIndexOfHelper(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr GetDuplicateStateAutomaton();
  StringAutomaton_ptr ToQueryAutomaton();
  StringAutomaton_ptr Search(StringAutomaton_ptr search_auto);
  StringAutomaton_ptr RemoveReservedWords();
  virtual void AddPrintLabel(std::ostream& out);


  int num_tracks_;
  StringFormula_ptr formula_;
  static TransitionTable TRANSITION_TABLE;
  static const int VAR_PER_TRACK = 9;
  static const int DEFAULT_NUM_OF_VARIABLES = 8;
  static bool debug;

private:
  StringAutomaton();

  static int name_counter;
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_STRINGAUTOMATON_H_ */
