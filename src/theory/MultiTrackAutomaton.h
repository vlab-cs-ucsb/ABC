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

	static MultiTrackAutomaton_ptr makePhi(size_t ntracks);
	static MultiTrackAutomaton_ptr makeEquality(std::vector<std::pair<std::string, int>> tracks, size_t ntracks);
	static MultiTrackAutomaton_ptr makeNotEquality(std::vector<std::pair<std::string, int>> tracks, size_t ntracks);
	static MultiTrackAutomaton_ptr makeAnyAutoUnaligned(size_t num_tracks);
	static MultiTrackAutomaton_ptr makeAnyAutoAligned(size_t num_tracks);

	size_t getNumTracks() const;

	MultiTrackAutomaton_ptr complement();
	MultiTrackAutomaton_ptr union_(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr intersect(MultiTrackAutomaton_ptr other_auto);
	MultiTrackAutomaton_ptr difference(MultiTrackAutomaton_ptr other_auto);

	MultiTrackAutomaton_ptr projectKTrack(unsigned track);
	StringAutomaton_ptr getKTrack(unsigned k);
	std::vector<std::string> getAnAcceptingStringForEachTrack();

 protected:

	static char* getLambda(int);
	static DFA_ptr getLambdaStar(int, int*);
	static bool checkLambda(std::string,int track_num,int num_tracks,int var);
	static int* allocateMultipleAscIIIndex(int m, int length, int extra = 0);
	static DFA_ptr removeLambdaSuffix(DFA_ptr dfa);
	DFA_ptr makeConcreteDFA();

	static const size_t VAR_PER_TRACK = 8;
	size_t num_of_tracks;

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
