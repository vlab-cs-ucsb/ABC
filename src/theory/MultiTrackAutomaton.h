/*
 * MultiTrackAutomaton.h
 *
 * Created on: Jan 29, 2015
 * Author: Will
 */

#ifndef THEORY_MULTITRACKAUTOMATON_H_
#define THEORY_MULTITRACKAUTOMATON_H_

#include <glog/logging.h>

#include "StringAutomaton.h"
#include "StringRelation.h"

namespace Vlab {
namespace Theory {

class MultiTrackAutomaton;
typedef MultiTrackAutomaton* MultiTrackAutomaton_ptr;

class MultiTrackAutomaton: public Automaton {
  using TransitionVector = std::vector<std::pair<std::string,std::string>>;
  using TransitionTable = std::map<std::pair<int,StringRelation::Type>,TransitionVector>;

 public:
	MultiTrackAutomaton(DFA_ptr dfa, int num_tracks);
	MultiTrackAutomaton(DFA_ptr dfa, int i_track, int num_tracks, int in_num_vars = DEFAULT_NUM_VAR);
	MultiTrackAutomaton(const MultiTrackAutomaton&);
virtual ~MultiTrackAutomaton();
	virtual MultiTrackAutomaton_ptr clone() const;

	static MultiTrackAutomaton_ptr makePrefixSuffix(int left_track, int prefix_track, int suffix_track, int num_tracks);

	static MultiTrackAutomaton_ptr makePhi(int ntracks);
	static MultiTrackAutomaton_ptr makeAuto(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeBegins(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeNotBegins(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeConcatExtraTrack(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeEquality(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeNotEquality(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeLessThan(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeLessThanOrEqual(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeGreaterThan(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeGreaterThanOrEqual(StringRelation_ptr relation);
	static MultiTrackAutomaton_ptr makeAnyAutoUnaligned(int num_tracks);
	static MultiTrackAutomaton_ptr makeAnyAutoAligned(int num_tracks);

	MultiTrackAutomaton_ptr complement();
	MultiTrackAutomaton_ptr union_(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr intersect(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr difference(MultiTrackAutomaton_ptr other_auto);

	MultiTrackAutomaton_ptr projectKTrack(int track);
	StringAutomaton_ptr getKTrack(int k);
	boost::multiprecision::cpp_int Count(int bound, bool count_less_than_or_equal_to_bound, bool count_reserved_words);
	std::vector<std::string> getAnAcceptingStringForEachTrack();
	int getNumTracks() const;

	StringRelation_ptr getRelation();
	bool setRelation(StringRelation_ptr relation);



	static const TransitionVector& generate_transitions_for_relation(StringRelation::Type type, int bits_per_var);
	static DFA_ptr make_binary_relation_dfa(StringRelation::Type type, int bits_per_var, int num_tracks, int left_track, int right_track);
	static DFA_ptr make_binary_aligned_dfa(int left_track, int right_track, int total_tracks);

	static bool is_exep_equal_char(std::vector<char> exep, std::vector<char> cvec, int var);
	static bool is_exep_include_char(std::vector<char> exep, std::vector<char> cvec, int var);

	static DFA_ptr prepend_lambda(DFA_ptr dfa, int var);
	static DFA_ptr append_lambda(DFA_ptr dfa, int var);
	static DFA_ptr trim_lambda_prefix(DFA_ptr dfa, int var);
	static DFA_ptr trim_lambda_suffix(DFA_ptr dfa, int var);
	static DFA_ptr trim_prefix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var);
	static DFA_ptr trim_suffix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var);
	static DFA_ptr concat(DFA_ptr prefix_dfa, DFA_ptr suffix_dfa, int var);

	static DFA_ptr pre_concat_prefix(DFA_ptr concat_dfa, DFA_ptr suffix_dfa, int var);
	static DFA_ptr pre_concat_suffix(DFA_ptr concat_dfa, DFA_ptr prefix_dfa, int var);

	static const int DEFAULT_NUM_VAR = 8;
	static const int VAR_PER_TRACK = 9;
	int num_of_tracks;

 private:

 	StringRelation_ptr relation;
 	static TransitionTable transition_table;
	static const int VLOG_LEVEL;

};

} /* namespace Theory */
} /* namespace VLAB */

#endif /* THEORY_MULTITRACKAUTOMATON_H_ */
