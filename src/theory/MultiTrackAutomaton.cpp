/*
* MultiTrackAutomaton.cpp
*
* Created on Jan 29, 2016
* Author: Will & Miroslav
*
*/

// TODO: Use Automaton::getIndices rather than
// TODO: getLambdaStar does not accept empty string, so it now functions like getLambdaPlus
// 			this is due to issue in string concat from libstranger


#include "MultiTrackAutomaton.h"
namespace Vlab {
namespace Theory {

const int MultiTrackAutomaton::VLOG_LEVEL = 20;

MultiTrackAutomaton::MultiTrackAutomaton(DFA_ptr dfa, size_t num_tracks)
			: Automaton(Automaton::Type::MULTITRACK, dfa, num_tracks * VAR_PER_TRACK),
				num_of_tracks(num_tracks) {
}

MultiTrackAutomaton::MultiTrackAutomaton(DFA_ptr dfa, unsigned i_track, size_t num_tracks)
			: Automaton(Automaton::Type::MULTITRACK, nullptr, num_tracks * VAR_PER_TRACK),
			  num_of_tracks(num_tracks) {
	int *indices = allocateMultipleAscIIIndex(1,VAR_PER_TRACK);
	DFA_ptr result,temp,M;
	M = getLambdaStar(VAR_PER_TRACK,indices);
	StringAutomaton_ptr t1,t2,t3;
	t1 = new StringAutomaton(dfaCopy(dfa));
	t2 = new StringAutomaton(M);

	t3 = t1->concat(t2);
	delete t1;
	delete t2;
	M = t3->getDFA();
	trace_descr tp;
	paths state_paths, pp;
	Exception curr_exep;
	std::vector<Exception> state_exeps;
	int sink;
	char* statuses;
	int* mindices;
	unsigned len;

	len = num_tracks * VAR_PER_TRACK;
	mindices = allocateMultipleAscIIIndex(num_tracks,VAR_PER_TRACK);
	statuses = new char[len+1];
	sink = find_sink(M);
	// begin dfa building process
	dfaSetup(M->ns, len, mindices);
	for(unsigned i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);

		while(pp) {
			if(pp->to != sink) {
				std::string curr = std::string(len,'X');
				for(unsigned j = 0; j < VAR_PER_TRACK; j++) {
					for(tp = pp->trace; tp && (tp->index != mindices[j]); tp = tp->next);
					if(tp) {
						if(tp->value) curr[i_track+num_tracks*j] = '1';
						else curr[i_track+num_tracks*j] = '0';
					}
					else
						curr[i_track+num_tracks*j] = 'X';
				}
				curr.push_back('\0');
				state_exeps.push_back(Exception(curr,pp->to));
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		dfaAllocExceptions(state_exeps.size());
		for(unsigned k = 0; k < state_exeps.size(); ++k) {
			std::vector<char> v = std::vector<char>(state_exeps[k].ex.begin(), state_exeps[k].ex.end());
			v.push_back('\0');
			dfaStoreException(state_exeps[k].to,&v[0]);
		}
		dfaStoreState(sink);
		state_exeps.clear();

		if(M->f[i] == -1)
			statuses[i] = '-';
		else if(M->f[i] == 1)
			statuses[i] = '+';
		else
			statuses[i] = '0';
	}
	statuses[len] = '\0';

	temp = dfaBuild(statuses);
	result = dfaMinimize(temp);
	dfaFree(temp);
	delete[] statuses;
	delete t3;
	this->dfa = result;
}

MultiTrackAutomaton::MultiTrackAutomaton(const MultiTrackAutomaton& other)
			: Automaton(other),
				num_of_tracks(other.num_of_tracks) {
}

MultiTrackAutomaton::~MultiTrackAutomaton() {
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::clone() const {
	MultiTrackAutomaton_ptr cloned_auto = new MultiTrackAutomaton(*this);
	return cloned_auto;
}

int* MultiTrackAutomaton::allocateMultipleAscIIIndex(int m, int length, int extra) {
	int* indices;
	indices = new int[length*m+extra];
	for(int i=0; i<m*length+extra; i++) {
		indices[i] = i;
	}
	return indices;
}

char* MultiTrackAutomaton::getLambda(int var) {
	return getSharp1(var); //11111111
}

// LAMBDAPLUS
DFA_ptr MultiTrackAutomaton::getLambdaStar(int var, int* indices) {
	char *lambda;
	lambda = getLambda(var);
	dfaSetup(3, var, indices);
	dfaAllocExceptions(1);
	dfaStoreException(1, lambda);
	dfaStoreState(2);
	dfaAllocExceptions(1);
	dfaStoreException(1, lambda);
	dfaStoreState(2);
	dfaAllocExceptions(0);
	dfaStoreState(2);
	delete[] lambda;

	//return dfaBuild("++-");
	return dfaBuild("-+-");
}

bool MultiTrackAutomaton::checkLambda(std::string exeps, int track_num, int num_tracks, int var) {
	for(int i = 0; i < var; i++) {
		if(exeps[track_num+num_tracks*i] != '1')
			return false;
	}
	return true;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makePhi(size_t ntracks) {
	DFA_ptr non_accepting_dfa = nullptr;
	MultiTrackAutomaton_ptr non_accepting_auto = nullptr;
	int *indices = allocateMultipleAscIIIndex(ntracks,VAR_PER_TRACK);

	non_accepting_dfa = Automaton::makePhi(ntracks*VAR_PER_TRACK, indices);
	delete[] indices; indices = nullptr;
	non_accepting_auto = new MultiTrackAutomaton(non_accepting_dfa, ntracks);

	return non_accepting_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeEquality(std::vector<std::pair<std::string,int>> tracks, size_t ntracks) {
	MultiTrackAutomaton_ptr result_auto;
	DFA_ptr temp_dfa, result_dfa;
	size_t num_tracks = ntracks;
	if(tracks.size() < 2) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::makeEquality: insufficient variables";
	}

	int left_track = tracks[0].second;
	int right_track = tracks[1].second;

	if(left_track == -1) {
		StringAutomaton_ptr string_auto = StringAutomaton::makeString(tracks[0].first);
		result_auto = new MultiTrackAutomaton(string_auto->getDFA(),right_track,ntracks);
		delete string_auto;
		return result_auto;
	} else if(right_track == -1) {
		StringAutomaton_ptr string_auto = StringAutomaton::makeString(tracks[1].first);
		result_auto = new MultiTrackAutomaton(string_auto->getDFA(),left_track,ntracks);
		delete string_auto;
		return result_auto;
	}

	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = allocateMultipleAscIIIndex(num_tracks,var);
	int nump = 1 << var;
	dfaSetup(3,len,mindices);
	dfaAllocExceptions(nump);
	for(int i = 0; i < nump-1; i++) {
		std::vector<char> exep = getBinaryFormat(i,var);
		std::vector<char> str(len,'X');
		for(int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep[k];
			str[right_track+num_tracks*k] = exep[k];
		}
		str.push_back('\0');
		dfaStoreException(0,&str[0]);
	}

	// append lambda
	std::vector<char> exep = getBinaryFormat(nump-1,var);
	std::vector<char> str(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep[k];
		str[right_track+num_tracks*k] = exep[k];
	}

	str.push_back('\0');
	dfaStoreException(1,&str[0]);
	dfaStoreState(2);
	dfaAllocExceptions(1);
	dfaStoreException(1,&str[0]);
	dfaStoreState(2);
	dfaAllocExceptions(0);
	dfaStoreState(2);
	temp_dfa = dfaBuild("++-");
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	result_auto = new MultiTrackAutomaton(result_dfa,num_tracks);
	return result_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeNotEquality(std::vector<std::pair<std::string,int>> tracks, size_t ntracks) {
	MultiTrackAutomaton_ptr eq_auto = nullptr, not_eq_auto = nullptr;
	eq_auto = makeEquality(tracks, ntracks);
	not_eq_auto = eq_auto->complement();
	delete eq_auto;
	return not_eq_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAnyAutoUnaligned(size_t num_tracks) {
	size_t len = VAR_PER_TRACK * num_tracks;
	int *mindices = MultiTrackAutomaton::allocateMultipleAscIIIndex(num_tracks,VAR_PER_TRACK);
	std::vector<char> str(len, 'X');
	str.push_back('\0');

	dfaSetup(1, len, mindices);
	dfaAllocExceptions(1);
	dfaStoreException(0,&str[0]);
	dfaStoreState(0);

	DFA_ptr ptr = dfaMinimize(dfaBuild("+"));
	//dfaFree(ptr);
	return new MultiTrackAutomaton(ptr,num_tracks);
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAnyAutoAligned(size_t num_tracks) {
	MultiTrackAutomaton_ptr aligned_auto = nullptr, any_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr any_string_auto = nullptr;

	aligned_auto = makeAnyAutoUnaligned(num_tracks);
	any_string_auto = StringAutomaton::makeAnyString();

	for(unsigned i = 0; i < num_tracks; i++) {
		any_auto = new MultiTrackAutomaton(any_string_auto->getDFA(),i,num_tracks);
		temp_auto = aligned_auto->intersect(any_auto);
		delete aligned_auto;
		delete any_auto;
		aligned_auto = temp_auto;
	}
	return aligned_auto;
}

size_t MultiTrackAutomaton::getNumTracks() const {
	return this->num_of_tracks;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::complement() {
  DFA_ptr complement_dfa = nullptr;
	MultiTrackAutomaton_ptr temp_auto = nullptr, complement_auto = nullptr, aligned_universe_auto = nullptr;
	complement_dfa = dfaCopy(this->dfa);
	dfaNegation(complement_dfa);
	temp_auto = new MultiTrackAutomaton(complement_dfa,this->num_of_tracks);
	aligned_universe_auto = makeAnyAutoAligned(this->num_of_tracks);
	complement_auto = temp_auto->intersect(aligned_universe_auto);
	delete temp_auto;
	delete aligned_universe_auto;

	return complement_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::union_(MultiTrackAutomaton_ptr other_auto) {
	if (this->num_of_tracks != other_auto->num_of_tracks) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::union_, unequal track numbers";
		return this->clone();
	}
  DFA_ptr intersect_dfa, minimized_dfa;
	MultiTrackAutomaton_ptr union_auto;
	intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaOR);
	minimized_dfa = dfaMinimize(intersect_dfa);
	dfaFree(intersect_dfa);
	union_auto = new MultiTrackAutomaton(minimized_dfa, this->num_of_tracks);
	return union_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::difference(MultiTrackAutomaton_ptr other_auto) {
	if (this->num_of_tracks != other_auto->num_of_tracks) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::difference, unequal track numbers";
		return this->clone();
	}
	MultiTrackAutomaton_ptr complement_auto, difference_auto;
	complement_auto = other_auto->complement();
	difference_auto = this->intersect(complement_auto);
	delete complement_auto; complement_auto = nullptr;
	return difference_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::intersect(MultiTrackAutomaton_ptr other_auto) {
	if (this->num_of_tracks != other_auto->num_of_tracks) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::intersect, unequal track numbers";
		return this->clone();
	}
	DFA_ptr intersect_dfa, minimized_dfa;
	MultiTrackAutomaton_ptr intersect_auto;
	intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaAND);
	minimized_dfa = dfaMinimize(intersect_dfa);
	dfaFree(intersect_dfa);
	intersect_auto = new MultiTrackAutomaton(minimized_dfa, this->num_of_tracks);
	return intersect_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::projectKTrack(unsigned k_track) {
	const size_t var_per_track = this->num_of_variables / this->num_of_tracks;
	MultiTrackAutomaton_ptr result_auto;
	DFA_ptr temp,result_dfa = this->dfa;
	int flag = 0;

	int *map = allocateMultipleAscIIIndex(this->num_of_tracks, VAR_PER_TRACK);

	for(int i = 0,k=0,l=0; i < this->num_of_variables; i++) {
	    if(i == k_track+l*this->num_of_tracks) {
	        map[i] = (this->num_of_tracks-1)*VAR_PER_TRACK+l;
	        l++;
	        continue;
	    }
	    map[i] = k++;
	}

	for(unsigned j = 0; j < var_per_track; j++) {
		temp = dfaProject(result_dfa,k_track+this->num_of_tracks*j);
		if(flag)
			dfaFree(result_dfa);
		result_dfa = dfaMinimize(temp);
		flag = 1;
		dfaFree(temp);
	}
	dfaReplaceIndices(result_dfa,map);
	result_auto = new MultiTrackAutomaton(result_dfa,this->num_of_tracks-1);
	return result_auto;
}

//TODO: Why doesn't k=0 work?
StringAutomaton_ptr MultiTrackAutomaton::getKTrack(unsigned k_track) {
	DFA_ptr result = this->dfa, temp;
	StringAutomaton_ptr result_auto = nullptr;
	int flag = 0;

	if(k_track >= this->num_of_tracks) {
		std::cerr << "error in MultiTrackAutomaton::getKTrack" << std::endl;
		exit(1);
	} else if(this->num_of_tracks == 1) {
	    result= removeLambdaSuffix(this->dfa);
	    result_auto = new StringAutomaton(result);
		return result_auto;
	} else if(k_track == 0) {
		MultiTrackAutomaton_ptr m1, m2;
		m1 = this->clone();
		for (int i = this->num_of_tracks - 1; i > 0; i--) {
			m2 = m1->projectKTrack(i);
			delete m1;
			m1 = m2;
			m2 = nullptr;
		}
		result = removeLambdaSuffix(m1->dfa);
		delete m1; m1 = nullptr;
		result_auto = new StringAutomaton(result);
		return result_auto;
	}

    // k_track needs to be mapped to indices 0-VAR_PER_TRACK
    // while all others need to be pushed back by VAR_PER_TRACK, then
    // interleaved with 1 less than current number of tracks
	int* map = allocateMultipleAscIIIndex(this->num_of_tracks,VAR_PER_TRACK);
    for(int i = 0; i < this->num_of_tracks; i++) {
        if(i == k_track) {
            for(int k = 0; k < VAR_PER_TRACK; k++) {
                map[i+this->num_of_tracks*k] = k;
            }
        } else {
            for(int k = 0; k < VAR_PER_TRACK; k++) {
                map[i+this->num_of_tracks*k] = VAR_PER_TRACK + i+(this->num_of_tracks-1)*k;
            }
        }
    }

	// project away all but the kth track
	for(int i = this->num_of_tracks-1; i >= 0; --i) {
		if(i != k_track) {
			for(int j = VAR_PER_TRACK-1; j>=0; --j) {
				temp = dfaProject(result,i+this->num_of_tracks*j);
				if(flag)
					dfaFree(result);
				result = dfaMinimize(temp);
				flag = 1;
				dfaFree(temp);
			}
		}
	}
	dfaReplaceIndices(result,map);
	temp = removeLambdaSuffix(result);
	dfaFree(result);
	result = temp;
	return new StringAutomaton(result);
}

DFA_ptr MultiTrackAutomaton::removeLambdaSuffix(DFA_ptr dfa) {
	DFA_ptr result_dfa, temp;
	paths state_paths, pp;
	trace_descr tp;
	char* statuses;
	int *indices;
	int sink;
	std::string symbol;
	std::vector<Exception> state_exeps;
	indices = MultiTrackAutomaton::allocateMultipleAscIIIndex(1,VAR_PER_TRACK);
	sink = find_sink(dfa);

	dfaSetup(dfa->ns, VAR_PER_TRACK, indices);
	statuses = new char[dfa->ns+1];
	for(int i = 0; i < dfa->ns; i++) {
		if(dfa->f[i] == 1)
		  statuses[i] = '+';
		else
		  statuses[i] = '-';
		state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);

		// essentially, basic idea is to keep all transitions except for lambda transitions
		// if there is a lambda transition on some state, that means that state must be
		// an accepting state. get rid of the lambda transition and make that state accepting.
		while (pp) {
			if (pp->to != sink) {
				for (unsigned j = 0; j < VAR_PER_TRACK; j++) {
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);

					if (tp) {
						if (tp->value) symbol += '1';
						else symbol += '0';
					}
					else
						symbol += 'X';
				}
				if (MultiTrackAutomaton::checkLambda(symbol, 0, 1, VAR_PER_TRACK)) {
					statuses[i] = '+';
				}
				else {
					state_exeps.push_back(Exception(symbol, pp->to));
				}
				symbol = "";
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		dfaAllocExceptions(state_exeps.size());
		for (unsigned k = 0; k < state_exeps.size(); k++) {
			std::vector<char> v = std::vector<char>(state_exeps[k].ex.begin(), state_exeps[k].ex.end());
			v.push_back('\0');
			dfaStoreException(state_exeps[k].to,&v[0]);
		}
		dfaStoreState(sink);
		state_exeps.clear();
	}
	statuses[dfa->ns] = '\0';
	temp = dfaBuild(statuses);
	result_dfa = dfaMinimize(temp);
	dfaFree(temp);

	delete[] statuses;
	return result_dfa;
}

DFA_ptr MultiTrackAutomaton::makeConcreteDFA() {
	DFA_ptr result_dfa;
	int var = VAR_PER_TRACK;
	int *indices = allocateMultipleAscIIIndex(1,var);
	int nump = 1 << var;

	dfaSetup(2,var,indices);
	dfaAllocExceptions(nump-1);
	for(int i = 0; i < nump-1; i++) {
		std::vector<char> exep = getBinaryFormat(i,var);
		exep.push_back('\0');
		dfaStoreException(0,&exep[0]);
	}
	dfaStoreState(1);

	dfaAllocExceptions(0);
	dfaStoreState(1);

	result_dfa = dfaBuild("+-");
	return result_dfa;

}

Exception::Exception(std::string e, unsigned t) {
	ex = e;
	to = t;
}

Exception::Exception(std::pair<unsigned,unsigned> e, std::pair<unsigned,unsigned> p) {
	pex = e;
	to = 0;
	pto = p;
}

Exception::Exception(std::pair<std::string,std::string> e, std::pair<unsigned,unsigned> p) {
	string_pair_exep = e;
	to = 0;
	pto = p;
}

Exception::~Exception() {
}

/*
MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAutoWordConcat(StringRelation_ptr str_rel,unsigned num_tracks) {
	MultiTrackAutomaton_ptr temp1_auto,temp2_auto,temp3_auto,temp4_auto, result_auto,
							stage1_auto,stage2_auto;
	StringAutomaton_ptr left_string_auto   = nullptr,
						right1_string_auto = nullptr,
						right2_string_auto = nullptr,
						concat_string_auto = nullptr,temp_string_auto;
	Letter_ptr left_letter,right1_letter,right2_letter;
	StringRelation_ptr temp_str_rel;
	int left_track, right1_track, right2_track, next_track;
	int new_track_size;

	left_letter = str_rel->getLeftLetter();
	right1_letter = str_rel->getRightFirstLetter();
	right2_letter = str_rel->getRightSecondLetter();

	left_track = left_letter->track_num;
	right1_track = right1_letter->track_num;
	right2_track = right2_letter->track_num;
	next_track = num_tracks;

	// if any are -1, then that track is constant
	if(left_track == -1) {
		left_track = next_track++;
		left_string_auto = StringAutomaton::makeString(left_letter->const_value);
	}

	if(right1_track == -1) {
		right1_track = next_track++;
		right1_string_auto = StringAutomaton::makeString(right1_letter->const_value);
	} else {
		right1_string_auto = this->getKTrack(right1_track);
	}
	if(right2_track == -1) {
		right2_track = next_track++;
		right2_string_auto = StringAutomaton::makeString(right2_letter->const_value);
	}
	else {
		right2_string_auto = this->getKTrack(right2_track);
	}
	new_track_size = next_track;

	// change track numbers, if we have to, for prefix
	left_letter->track_num = left_track;
	right1_letter->track_num = right1_track;
	right2_letter->track_num = right2_track;
	temp_str_rel = new StringRelation(StringRelation::Type::CONCAT,left_letter,right1_letter,right2_letter);

	// check if either right1,right2 sigma*
	int right1_sink = find_sink(right1_string_auto->getDFA());
	int right2_sink = find_sink(right2_string_auto->getDFA());

	// if either has no sink, make them instead any string but lambda
	// (easier this way for prefix/suffix)
	if(right1_sink == -1) {
		delete right1_string_auto;
		right1_string_auto = new StringAutomaton(MultiTrackAutomaton::makeConcreteDFA());
	}
	if(right2_sink == -1) {
		delete right2_string_auto;
		right2_string_auto = new StringAutomaton(MultiTrackAutomaton::makeConcreteDFA());
	}

	// put prefix concat suffix on left_track
	concat_string_auto = right1_string_auto->concat(right2_string_auto);
	// Y concat Z
	temp1_auto = new MultiTrackAutomaton(concat_string_auto->getDFA(),left_track,new_track_size);
	delete concat_string_auto;
	// put prefix on right1_track
	temp2_auto = new MultiTrackAutomaton(right1_string_auto->getDFA(),right1_track,new_track_size);
	temp3_auto = temp1_auto->intersect(temp2_auto);
	delete temp1_auto;
	delete temp2_auto;
	// match up prefix/suffix stuff
	temp1_auto = makeAutoWordPrefix(temp_str_rel,new_track_size);
	stage1_auto = temp3_auto->intersect(temp1_auto);
	delete temp1_auto;
	delete temp3_auto;
	// put suffix on right2_track
	temp2_auto = new MultiTrackAutomaton(right2_string_auto->getDFA(),right2_track,new_track_size);
	temp3_auto = stage1_auto->intersect(temp2_auto);
	delete stage1_auto;
	delete temp2_auto;
	// if left side is constant, intersect it with stage2_auto, which
	// will have prefix->concat(suffix) on left_track, prefix on right1_track,
	// suffix on right2_track, and have constraint that lefttrack = righttrack till lambda
	if(left_string_auto != nullptr) {
		temp1_auto = new MultiTrackAutomaton(left_string_auto->getDFA(),left_track,new_track_size);
		temp2_auto = stage2_auto->intersect(temp1_auto);
		delete temp1_auto;
		delete stage2_auto;
		delete left_string_auto;
		stage2_auto = temp2_auto;
	}
	result_auto = stage2_auto;
	// project away extra tracks
	for(int k = new_track_size-1; k >= num_tracks; k--){
		temp1_auto = result_auto->projectKTrack(k);
		delete result_auto;
		result_auto = temp1_auto;
	}
	temp1_auto = this->intersect(result_auto);
	delete temp_str_rel;
	delete right1_string_auto;
	delete right2_string_auto;
	delete result_auto;
	result_auto = temp1_auto;
	return result_auto;

}
*/
/*
MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAutoWordPrefix(StringRelation_ptr str_rel,unsigned num_tracks) {
	MultiTrackAutomaton_ptr result_auto;
	DFA_ptr temp_dfa, result_dfa;
	int left_track = str_rel->getLeftLetter()->track_num;
	int right_track = str_rel->getRightFirstLetter()->track_num;

	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = allocateMultipleAscIIIndex(num_tracks,var);
	int nump = 1 << var;
	dfaSetup(3,len,mindices);
	dfaAllocExceptions(2 * nump - 1); // 1 extra for lambda stuff below
	for(int i = 0; i < nump-1; i++) {
		std::vector<char> exep = getBinaryFormat(i,var);
		std::vector<char> str(len,'X');
		for(int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep[k];
			str[right_track+num_tracks*k] = exep[k];
		}
		str.push_back('\0');
		dfaStoreException(0,&str[0]);
	}

	// append lambda to right_track, left_track gets anything.
	// then append lambda to left_track
	std::vector<char> exep_lambda = getBinaryFormat(nump-1,var);

	// if right is lambda, left can be anything, but go to next state
	for(int i = 0; i < nump-1; i++) {
		std::vector<char> exep = getBinaryFormat(i,var);
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		str.push_back('\0');
		dfaStoreException(0,&str[0]);
	}

	// if both are lambda, go to next state
	std::vector<char> str(len,'X');
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(1,&str[0]);
	dfaStoreState(2);

	dfaAllocExceptions(1);
	dfaStoreException(1,&str[0]);
	dfaStoreState(2);

	dfaAllocExceptions(0);
	dfaStoreState(2);
	temp_dfa = dfaBuild("++-");
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	result_auto = new MultiTrackAutomaton(result_dfa,num_tracks);

	return result_auto;
}
*/

} /* namespace Vlab */
} /* namespace Theory */
