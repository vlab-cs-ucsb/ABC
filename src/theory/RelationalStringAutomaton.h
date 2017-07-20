/*
 * RelationalStringAutomaton.h
 *
 *  Created on: Jan 23, 2017
 *      Author: baki
 */

#ifndef SRC_THEORY_RELATIONALSTRINGAUTOMATON_H_
#define SRC_THEORY_RELATIONALSTRINGAUTOMATON_H_

#include <glog/logging.h>

#include "StringAutomaton.h"
#include "StringFormula.h"

namespace Vlab {
namespace Theory {

class RelationalStringAutomaton;
using RelationalStringAutomaton_ptr = RelationalStringAutomaton*;

class RelationalStringAutomaton: public Automaton {
  using TransitionVector = std::vector<std::pair<std::string,std::string>>;
  using TransitionTable = std::map<std::pair<int,StringFormula::Type>,TransitionVector>;

 public:
//  RelationalStringAutomaton(DFA_ptr dfa, int num_tracks);
  RelationalStringAutomaton(DFA_ptr dfa, StringFormula_ptr formula);
  RelationalStringAutomaton(DFA_ptr dfa, int i_track, int num_tracks, int in_num_vars = DEFAULT_NUM_VAR);
  RelationalStringAutomaton(const RelationalStringAutomaton&);
  virtual ~RelationalStringAutomaton();
  virtual RelationalStringAutomaton_ptr clone() const;

  static RelationalStringAutomaton_ptr makePrefixSuffix(int left_track, int prefix_track, int suffix_track, int num_tracks);

  static RelationalStringAutomaton_ptr MakePhi(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeAutomaton(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeBegins(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeNotBegins(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeConcatExtraTrack(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeEquality(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeNotEquality(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeLessThan(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeLessThanOrEqual(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeGreaterThan(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeGreaterThanOrEqual(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeAnyStringUnaligned(StringFormula_ptr formula);
  static RelationalStringAutomaton_ptr MakeAnyStringAligned(StringFormula_ptr formula);

  RelationalStringAutomaton_ptr Complement();
  RelationalStringAutomaton_ptr Union(RelationalStringAutomaton_ptr other_auto);
  RelationalStringAutomaton_ptr Intersect(RelationalStringAutomaton_ptr other_auto);
  RelationalStringAutomaton_ptr Intersect(StringAutomaton_ptr other_auto);
  RelationalStringAutomaton_ptr Difference(RelationalStringAutomaton_ptr other_auto);

  RelationalStringAutomaton_ptr ProjecAwayVariable(std::string var_name);
  RelationalStringAutomaton_ptr ProjectKTrack(int track);
  StringAutomaton_ptr GetAutomatonForVariable(std::string var_name);
  StringAutomaton_ptr GetKTrack(int k);
  void SetSymbolicCounter() override;
  std::vector<std::string> getAnAcceptingStringForEachTrack();
  int getNumTracks() const;

  StringFormula_ptr get_formula();
  void set_formula(StringFormula_ptr formula);



  static const TransitionVector& generate_transitions_for_relation(StringFormula::Type type, int bits_per_var);
  static DFA_ptr make_binary_relation_dfa(StringFormula::Type type, int bits_per_var, int num_tracks, int left_track, int right_track);
  static DFA_ptr make_binary_aligned_dfa(int left_track, int right_track, int total_tracks);

  static bool is_exep_equal_char(std::vector<char> exep, std::vector<char> cvec, int var);
  static bool is_exep_include_char(std::vector<char> exep, std::vector<char> cvec, int var);

  static DFA_ptr prepend_lambda(DFA_ptr dfa, int var);
  static DFA_ptr append_lambda(DFA_ptr dfa, int var);
  static DFA_ptr trim_lambda_prefix(DFA_ptr dfa, int var, bool project_bit = true);
  static DFA_ptr trim_lambda_suffix(DFA_ptr dfa, int var, bool project_bit = true);
  static DFA_ptr trim_prefix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var);
  static DFA_ptr trim_suffix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var);
  static DFA_ptr concat(DFA_ptr prefix_dfa, DFA_ptr suffix_dfa, int var);

  static DFA_ptr pre_concat_prefix(DFA_ptr concat_dfa, DFA_ptr suffix_dfa, int var);
  static DFA_ptr pre_concat_suffix(DFA_ptr concat_dfa, DFA_ptr prefix_dfa, int var);

  static const int DEFAULT_NUM_VAR = 8;
  static const int VAR_PER_TRACK = 9;
  int num_of_tracks_;
protected:
  void add_print_label(std::ostream& out) override;

  StringFormula_ptr formula_;
  static TransitionTable TRANSITION_TABLE;

 private:
  static const int VLOG_LEVEL;

};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_RELATIONALSTRINGAUTOMATON_H_ */
