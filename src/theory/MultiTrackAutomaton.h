/*
 * MultiTrackAutomaton.h
 *
 * Created on: Jan 29, 2015
 * Author: Will
 */

#ifndef THEORY_MULTITRACKAUTOMATON_H_
#define THEORY_MULTITRACKAUTOMATON_H_

#include "StringAutomaton.h"
#include <glog/logging.h>
#include "StringRelation.h"

namespace Vlab {
namespace Theory {

class MultiTrackAutomaton;
typedef MultiTrackAutomaton* MultiTrackAutomaton_ptr;

class MultiTrackAutomaton: public Automaton {
 public:
	MultiTrackAutomaton(DFA_ptr dfa, int num_tracks);
	MultiTrackAutomaton(DFA_ptr dfa, int i_track, int num_tracks);
	MultiTrackAutomaton(const MultiTrackAutomaton&);
virtual ~MultiTrackAutomaton();
	virtual MultiTrackAutomaton_ptr clone() const;

	static MultiTrackAutomaton_ptr makePhi(int ntracks);
	static MultiTrackAutomaton_ptr makeAuto(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeEquality(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeNotEquality(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeLessThan(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeLessThanOrEqual(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeGreaterThan(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeGreaterThanOrEqual(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks);
	static MultiTrackAutomaton_ptr makeAnyAutoUnaligned(int num_tracks);
	static MultiTrackAutomaton_ptr makeAnyAutoAligned(int num_tracks);

	MultiTrackAutomaton_ptr complement();
	MultiTrackAutomaton_ptr union_(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr intersect(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr difference(MultiTrackAutomaton_ptr other_auto);

	MultiTrackAutomaton_ptr projectKTrack(int track);
	StringAutomaton_ptr getKTrack(int k);
	std::vector<std::string> getAnAcceptingStringForEachTrack();
	int getNumTracks() const;

	StringRelation_ptr getRelation();
	StringRelation_ptr getRelationClone() const;
	bool setRelation(StringRelation_ptr relation);

 protected:

	static char* getLambda(int);
	static DFA_ptr getLambdaStar(int, int*);
	static bool checkLambda(std::string,int track_num,int num_tracks,int var);
	static DFA_ptr removeLambdaSuffix(DFA_ptr dfa, int num_vars);
	DFA_ptr makeConcreteDFA();

	static const int VAR_PER_TRACK = 8;
	int num_of_tracks;

 private:
 	StringRelation_ptr relation;
	static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace VLAB */

#endif /* THEORY_MULTITRACKAUTOMATON_H_ */
