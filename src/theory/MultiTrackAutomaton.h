/*
 * MultiTrackAutomaton.h
 *
 * Created on: Jan 29, 2015
 * Author: Will & Miroslav
 */

#ifndef THEORY_MULTITRACKAUTOMATON_H_
#define THEORY_MULTITRACKAUTOMATON_H_

#include "StringAutomaton.h"
#include <unordered_map>
#include <list>
#include <chrono>
#include "StringRelation.h"
#include <glog/logging.h>
#include <unordered_set>
#include <queue>
#include <bitset>

namespace Vlab {
namespace Theory {

class MultiTrackAutomaton;
typedef MultiTrackAutomaton* MultiTrackAutomaton_ptr;

class MultiTrackAutomaton: public Automaton {
 public:
	MultiTrackAutomaton(DFA_ptr dfa, size_t num_tracks);
	MultiTrackAutomaton(DFA_ptr dfa, unsigned i_track, size_t num_tracks);
	MultiTrackAutomaton(const MultiTrackAutomaton&);
	virtual ~MultiTrackAutomaton();
	virtual MultiTrackAutomaton_ptr clone() const;

	static MultiTrackAutomaton_ptr makePhi(StringRelation_ptr str_rel);
	static MultiTrackAutomaton_ptr makeAutomaton(StringRelation_ptr str_rel);
	static MultiTrackAutomaton_ptr makeAnyAutoUnaligned(size_t num_tracks);
	static MultiTrackAutomaton_ptr makeAnyAutoAligned(size_t num_tracks);

	size_t getNumTracks() const;
	StringRelation_ptr getRelation();
	void setRelation(StringRelation_ptr str_rel);

	MultiTrackAutomaton_ptr complement();
	MultiTrackAutomaton_ptr union_(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr intersect(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr difference(MultiTrackAutomaton_ptr other_auto);

	MultiTrackAutomaton_ptr projectKTrack(unsigned track);
	StringAutomaton_ptr getKTrack(unsigned k) const;


 protected:
  MultiTrackAutomaton(StringRelation_ptr str_rel);

	static MultiTrackAutomaton_ptr makeEquality(StringRelation_ptr str_rel);
	static MultiTrackAutomaton_ptr makeNotEquality(StringRelation_ptr str_rel);

	static char* getLambda(int);
	static DFA_ptr getLambdaStar(int, int*);
	static bool checkLambda(std::string,int track_num,int num_tracks,int var);
	static int* allocateMultipleAscIIIndex(int m, int length, int extra = 0);

	MultiTrackAutomaton_ptr removeLambdaSuffix(unsigned track_num);
	DFA_ptr makeConcreteDFA();

	static const size_t VAR_PER_TRACK = 8;
	size_t num_of_tracks;
	StringRelation_ptr string_relation;

 private:
	static const int VLOG_LEVEL;
};

class Exception {
 public:
	std::string ex;
	unsigned to;
	std::pair<unsigned,unsigned> pto;
	std::pair<unsigned,unsigned> pex;
	std::pair<std::string,std::string> string_pair_exep;

	Exception() {}
	Exception(std::string, unsigned);
	Exception(std::pair<unsigned,unsigned>, std::pair<unsigned,unsigned>);
	Exception(std::pair<std::string,std::string>, std::pair<unsigned,unsigned>);
	~Exception();
};

} /* namespace Theory */
} /* namespace VLAB */

#endif /* THEORY_MULTITRACKAUTOMATON_H_ */
