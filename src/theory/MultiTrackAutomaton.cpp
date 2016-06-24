/*
* MultiTrackAutomaton.cpp
*
* Created on Jan 29, 2016
* Author: Will
*
*/

// TODO: getLambdaStar does not accept empty string, so it now functions like getLambdaPlus
// 			this is due to issue in string concat from libstranger


#include "MultiTrackAutomaton.h"
namespace Vlab {
namespace Theory {

const int MultiTrackAutomaton::VLOG_LEVEL = 20;

MultiTrackAutomaton::MultiTrackAutomaton(DFA_ptr dfa, int num_tracks)
			: Automaton(Automaton::Type::MULTITRACK, dfa, num_tracks * VAR_PER_TRACK),
				num_of_tracks(num_tracks), relation(nullptr) {
}

MultiTrackAutomaton::MultiTrackAutomaton(DFA_ptr dfa, int i_track, int num_tracks)
			: Automaton(Automaton::Type::MULTITRACK, nullptr, num_tracks * VAR_PER_TRACK),
			  num_of_tracks(num_tracks), relation(nullptr) {
	int *indices = getIndices(VAR_PER_TRACK);
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
	std::vector<std::pair<std::string,int>> state_exeps;
	int sink;
	char* statuses;
	int* mindices;
	int len;
	len = num_tracks * VAR_PER_TRACK;
	mindices = getIndices(num_tracks*VAR_PER_TRACK);
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
				state_exeps.push_back(std::make_pair(curr,pp->to));
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		dfaAllocExceptions(state_exeps.size());
		for(unsigned k = 0; k < state_exeps.size(); ++k) {
			std::vector<char> v = std::vector<char>(state_exeps[k].first.begin(), state_exeps[k].first.end());
			v.push_back('\0');
			dfaStoreException(state_exeps[k].second,&v[0]);
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
	delete[] indices;
	delete[] mindices;
	delete t3;
	this->dfa = result;
}

MultiTrackAutomaton::MultiTrackAutomaton(const MultiTrackAutomaton& other)
			: Automaton(other),
				num_of_tracks(other.num_of_tracks), relation(other.getRelationClone()) {
}

MultiTrackAutomaton::~MultiTrackAutomaton() {
  delete relation;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::clone() const {
	MultiTrackAutomaton_ptr cloned_auto = new MultiTrackAutomaton(*this);
	return cloned_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makePhi(int ntracks) {
	DFA_ptr non_accepting_dfa = nullptr;
	MultiTrackAutomaton_ptr non_accepting_auto = nullptr;
	int *indices = getIndices(ntracks*VAR_PER_TRACK);

	non_accepting_dfa = Automaton::makePhi(ntracks*VAR_PER_TRACK, indices);
	delete[] indices; indices = nullptr;
	non_accepting_auto = new MultiTrackAutomaton(non_accepting_dfa, ntracks);
	non_accepting_auto->setRelation(nullptr);
	return non_accepting_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAuto(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
	MultiTrackAutomaton_ptr result_auto = nullptr;
	switch(relation->get_type()) {
    case StringRelation::Type::EQ:
      result_auto = MultiTrackAutomaton::makeEquality(relation, tracks);
      break;
    case StringRelation::Type::NOTEQ:
      result_auto = MultiTrackAutomaton::makeNotEquality(relation, tracks);
      break;
    case StringRelation::Type::GT:
      result_auto = MultiTrackAutomaton::makeGreaterThan(relation, tracks);
      break;
    case StringRelation::Type::GE:
      result_auto = MultiTrackAutomaton::makeGreaterThanOrEqual(relation, tracks);
      break;
    case StringRelation::Type::LT:
      result_auto = MultiTrackAutomaton::makeLessThan(relation, tracks);
      break;
    case StringRelation::Type::LE:
      result_auto = MultiTrackAutomaton::makeLessThanOrEqual(relation, tracks);
      break;
    default:
      DVLOG(VLOG_LEVEL) << "StringRelation type not supported";
      result_auto = nullptr;
      break;
	}
	return result_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeEquality(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
	MultiTrackAutomaton_ptr result_auto;
	DFA_ptr temp_dfa, result_dfa;
	int num_tracks = relation->get_num_tracks();
	if(tracks.size() < 2) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::makeEquality: insufficient variables";
	}

	int left_track = tracks[0].second;
	int right_track = tracks[1].second;

	if(left_track == -1) {
		StringAutomaton_ptr string_auto = StringAutomaton::makeString(tracks[0].first);
		result_auto = new MultiTrackAutomaton(string_auto->getDFA(),right_track,num_tracks);
		delete string_auto;
		return result_auto;
	} else if(right_track == -1) {
		StringAutomaton_ptr string_auto = StringAutomaton::makeString(tracks[1].first);
		result_auto = new MultiTrackAutomaton(string_auto->getDFA(),left_track,num_tracks);
		delete string_auto;
		return result_auto;
	}

	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = getIndices(num_tracks*var);
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
	result_auto->setRelation(relation);
	delete[] mindices;
	return result_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeNotEquality(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
	MultiTrackAutomaton_ptr eq_auto = nullptr, not_eq_auto = nullptr;
	eq_auto = MultiTrackAutomaton::makeEquality(relation, tracks);
	not_eq_auto = eq_auto->complement();
	delete eq_auto;
	return not_eq_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeLessThan(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
	MultiTrackAutomaton_ptr result_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr constant_string_auto = nullptr;
	DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
	int num_tracks = relation->get_num_tracks();
	if(tracks.size() < 2) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::makeLessThan: insufficient variables";
	}
	int left_track = tracks[0].second;
	int right_track = tracks[1].second;
	// if one side is constant, replace with temp variable on last track,
	// proceeed normally, then intersect it
	// i.e., construct x < y
	// then intersect ^ with multitrack where constant is on y track
	// then project y track away
	if(left_track == -1) {
		// make room for temp variable
		left_track = num_tracks;
		num_tracks++;
		constant_string_auto = StringAutomaton::makeString(tracks[0].first);
	} else if(right_track == -1) {
		// make room for temp variable
		right_track = num_tracks;
		num_tracks++;
		constant_string_auto = StringAutomaton::makeString(tracks[1].first);
	}

	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = getIndices(num_tracks*var);
	int init = 0,
		  lambda_star = 1,
		  lambda_lambda = 2,
		  sink = 3;

	dfaSetup(4,len,mindices);
  std::vector<std::pair<std::vector<char>,int>> exeps;

  /************ initial state *******************/

	// if i < j and j != lambda, still valid, loop to init
	// if i == lambda, j != lambda, still good, but goto lambda_star
	// if i == lambda, j == lambda, still good, but goto lambda_lambda
	// otherwise, goto sink


  // take advantage of symbolic transtions
  // all the transitions where left < right follow the pattern:
  // 0 / 1
  // 0X / 1X
  // 0XX / 1XX
  // ...
  // 0XXXXXXX / 1XXXXXXX
  // BUT we need to account for if left is lambda, and right isn't, we
  // need to go to a separate state
  // and if left and right are both lambda, then we need to go to even
  // another state! so, to account for this, we do another pass, like so:
  // 1111110X / 11111110
  // 111110XX / 1111110X
  // ...
  // 0XXXXXXX / 10XXXXXX
  // both passes combined represent all transitions where left < right, excluing lambda

  // ----- first pass -----
  std::vector<char> exep_left(var,'0');
  std::vector<char> exep_right(var,'0');
  for(int pos = var-1; pos > 0; --pos) {
    exep_right[pos] = '1';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,init));
    exep_left[pos] = 'X';
    exep_right[pos] = 'X';
  }
  // ----- second pass (reversed) ------
  // exep_left / exep_right should be
  // 0XXXXXXX / 0XXXXXXX
  for(int pos = 0; pos < var-1; pos++) {
    exep_right[pos] = '1';
    exep_right[pos+1] = '0';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,init));
    exep_left[pos] = '1';
    exep_left[pos+1] = '0';
  }

  // now transitions where left = lambda, right = lambda
  // exep_left / exep_right should be
  // 11111110 / 11111110
  exep_left[var-1] = '1';
  exep_right[var-1] = '1';
  std::vector<char> str2(len, 'X');
  for (int k = 0; k < var; k++) {
    str2[left_track + num_tracks * k] = exep_left[k];
    str2[right_track + num_tracks * k] = exep_right[k];
  }
  str2.push_back('\0');
  exeps.push_back(std::make_pair(str2,lambda_lambda));

  // now transitions where left == lambda, right == star-lambda
  // exep_left / exep_right should be
  // 11111111 / 11111111
  for(int pos = var-1; pos >= 0; --pos) {
    exep_right[pos] = '0';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,lambda_star));
    exep_right[pos] = 'X';
  }

	dfaAllocExceptions(exeps.size());
	for(int i = 0; i < exeps.size(); i++) {
	  dfaStoreException(exeps[i].second, &(exeps[i].first)[0]);
	}
	dfaStoreState(sink);
  exeps.clear();
  /****************************************************************/

	/************* lambda_star state (i must be lambda) *****************/
	exep_left = std::vector<char>(var,'1');
	exep_right = std::vector<char>(var,'1');
	// lambda / lambda, good but goes to lambda_lambda state
  str2 = std::vector<char>(len, 'X');
  for (int k = 0; k < var; k++) {
    str2[left_track + num_tracks * k] = exep_left[k];
    str2[right_track + num_tracks * k] = exep_right[k];
  }
  str2.push_back('\0');
  exeps.push_back(std::make_pair(str2,lambda_lambda));

  // now transitions where left == lambda, right == star-lambda
  // exep_left, exep_right both lambda / lambda currently
  for(int pos = var-1; pos >= 0; --pos) {
    exep_right[pos] = '0';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,lambda_star));
    exep_right[pos] = 'X';
  }

	dfaAllocExceptions(exeps.size());
	for(int i = 0; i < exeps.size(); i++) {
	  dfaStoreException(exeps[i].second, &(exeps[i].first)[0]);
	}
	dfaStoreState(sink);
  exeps.clear();
  /*************************************************************8/


	/************ lambda_lambda state (i,j must both be lambda) ***********/
	exep_left = std::vector<char>(var,'1');
	exep_right = std::vector<char>(var,'1');
	// if i == lambda, j == lambda, still valid, loop to lambda_lambda
	// otherwise, goto sink
	dfaAllocExceptions(1);
	str2 = std::vector<char>(len, 'X');
	for (int k = 0; k < var; k++) {
		str2[left_track + num_tracks * k] = exep_left[k];
		str2[right_track + num_tracks * k] = exep_right[k];
	}
	str2.push_back('\0');
	dfaStoreException(lambda_lambda, &str2[0]);
	dfaStoreState(sink);
	/******************************************************************/

	/****************** sink state ************************/
	dfaAllocExceptions(0);
	dfaStoreState(sink);
  /**************************************************************/

	// build it!
	temp_dfa = dfaBuild("+++-");
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	result_auto = new MultiTrackAutomaton(result_dfa,num_tracks);
	// if constant_string_auto != nullptr, then either the left or right
	// side of the inequality is constant; we need to intersect it with
	// the multitrack where the constant is on the extra track, then
	// project away the extra track before we return
	if(constant_string_auto != nullptr) {
		MultiTrackAutomaton_ptr constant_multi_auto = new MultiTrackAutomaton(constant_string_auto->getDFA(),num_tracks-1,num_tracks);
		temp_auto = result_auto->intersect(constant_multi_auto);
		delete result_auto;
		delete constant_multi_auto;
		delete constant_string_auto;
		result_auto = temp_auto->projectKTrack(num_tracks-1);
		delete temp_auto;
	}

	result_auto->setRelation(relation);
	delete[] mindices;
	return result_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeLessThanOrEqual(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
  MultiTrackAutomaton_ptr greater_than_auto = nullptr, less_than_or_equal_auto = nullptr;
	greater_than_auto = MultiTrackAutomaton::makeLessThan(relation, tracks);
	less_than_or_equal_auto = greater_than_auto->complement();
	delete greater_than_auto;
	return less_than_or_equal_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeGreaterThan(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
  MultiTrackAutomaton_ptr result_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr constant_string_auto = nullptr;
	DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
	int num_tracks = relation->get_num_tracks();
	if(tracks.size() < 2) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::makeGreaterThan: insufficient variables";
	}
	int left_track = tracks[0].second;
	int right_track = tracks[1].second;
	// if one side is constant, replace with temp variable on last track,
	// proceeed normally, then intersect it
	// i.e., construct x > y
	// then intersect ^ with multitrack where constant is on y track
	// then project y track away
	if(left_track == -1) {
		// make room for temp variable
		left_track = num_tracks;
		num_tracks++;
		constant_string_auto = StringAutomaton::makeString(tracks[0].first);
	} else if(right_track == -1) {
		// make room for temp variable
		right_track = num_tracks;
		num_tracks++;
		constant_string_auto = StringAutomaton::makeString(tracks[1].first);
	}

	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = getIndices(num_tracks*var);
	int init = 0,
		  star_lambda = 1,
		  lambda_lambda = 2,
		  sink = 3;

	dfaSetup(4,len,mindices);
  std::vector<std::pair<std::vector<char>,int>> exeps;

  /************ initial state *******************/

	// if i > j and j != lambda, still valid, loop to init
	// if i != lambda, j == lambda, still good, but goto star_lambda
	// if i == lambda, j == lambda, still good, but goto lambda_lambda
	// otherwise, goto sink
  // SAME LOGIC AS LESS THAN, but flipped

  std::vector<char> exep_left(var,'0');
  std::vector<char> exep_right(var,'0');
  for(int pos = var-1; pos > 0; --pos) {
    exep_left[pos] = '1';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,init));
    exep_right[pos] = 'X';
    exep_left[pos] = 'X';
  }
  // ----- second pass (reversed) ------
  // exep_left / exep_right should be
  // 0XXXXXXX / 0XXXXXXX
  for(int pos = 0; pos < var-1; pos++) {
    exep_left[pos] = '1';
    exep_left[pos+1] = '0';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,init));
    exep_right[pos] = '1';
    exep_right[pos+1] = '0';
  }

  // now transitions where left = lambda, right = lambda
  // exep_left / exep_right should be
  // 11111110 / 11111110
  exep_left[var-1] = '1';
  exep_right[var-1] = '1';
  std::vector<char> str2(len, 'X');
  for (int k = 0; k < var; k++) {
    str2[left_track + num_tracks * k] = exep_left[k];
    str2[right_track + num_tracks * k] = exep_right[k];
  }
  str2.push_back('\0');
  exeps.push_back(std::make_pair(str2,lambda_lambda));

  // now transitions where left == star-lambda, right == lambda
  // exep_left / exep_right should be
  // 11111111 / 11111111
  for(int pos = var-1; pos >= 0; --pos) {
    exep_left[pos] = '0';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,star_lambda));
    exep_left[pos] = 'X';
  }

	dfaAllocExceptions(exeps.size());
	for(int i = 0; i < exeps.size(); i++) {
	  dfaStoreException(exeps[i].second, &(exeps[i].first)[0]);
	}
	dfaStoreState(sink);
  exeps.clear();
  /****************************************************************/

	/************* lambda_star state (i must be lambda) *****************/
	exep_left = std::vector<char>(var,'1');
	exep_right = std::vector<char>(var,'1');
	// lambda / lambda, good but goes to lambda_lambda state
  str2 = std::vector<char>(len, 'X');
  for (int k = 0; k < var; k++) {
    str2[left_track + num_tracks * k] = exep_left[k];
    str2[right_track + num_tracks * k] = exep_right[k];
  }
  str2.push_back('\0');
  exeps.push_back(std::make_pair(str2,lambda_lambda));

  // now transitions where left == lambda, right == star-lambda
  // exep_left, exep_right both lambda / lambda currently
  for(int pos = var-1; pos >= 0; --pos) {
    exep_left[pos] = '0';
    std::vector<char> str(len, 'X');
    for (int k = 0; k < var; k++) {
      str[left_track + num_tracks * k] = exep_left[k];
      str[right_track + num_tracks * k] = exep_right[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,star_lambda));
    exep_left[pos] = 'X';
  }

	dfaAllocExceptions(exeps.size());
	for(int i = 0; i < exeps.size(); i++) {
	  dfaStoreException(exeps[i].second, &(exeps[i].first)[0]);
	}
	dfaStoreState(sink);
  exeps.clear();
  /*************************************************************8/


	/************ lambda_lambda state (i,j must both be lambda) ***********/
	exep_left = std::vector<char>(var,'1');
	exep_right = std::vector<char>(var,'1');
	// if i == lambda, j == lambda, still valid, loop to lambda_lambda
	// otherwise, goto sink
	dfaAllocExceptions(1);
	str2 = std::vector<char>(len, 'X');
	for (int k = 0; k < var; k++) {
		str2[left_track + num_tracks * k] = exep_left[k];
		str2[right_track + num_tracks * k] = exep_right[k];
	}
	str2.push_back('\0');
	dfaStoreException(lambda_lambda, &str2[0]);
	dfaStoreState(sink);
	/******************************************************************/

	/****************** sink state ************************/
	dfaAllocExceptions(0);
	dfaStoreState(sink);
  /**************************************************************/

	// build it!
	temp_dfa = dfaBuild("+++-");
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	result_auto = new MultiTrackAutomaton(result_dfa,num_tracks);
	// if constant_string_auto != nullptr, then either the left or right
	// side of the inequality is constant; we need to intersect it with
	// the multitrack where the constant is on the extra track, then
	// project away the extra track before we return
	if(constant_string_auto != nullptr) {
		MultiTrackAutomaton_ptr constant_multi_auto = new MultiTrackAutomaton(constant_string_auto->getDFA(),num_tracks-1,num_tracks);
		temp_auto = result_auto->intersect(constant_multi_auto);
		delete result_auto;
		delete constant_multi_auto;
		delete constant_string_auto;
		result_auto = temp_auto->projectKTrack(num_tracks-1);
		delete temp_auto;
	}

	result_auto->setRelation(relation);
	delete[] mindices;
	return result_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeGreaterThanOrEqual(StringRelation_ptr relation, std::vector<std::pair<std::string,int>> tracks) {
  MultiTrackAutomaton_ptr less_than_auto = nullptr, greater_than_or_equal_auto = nullptr;
	less_than_auto = MultiTrackAutomaton::makeLessThan(relation, tracks);
	greater_than_or_equal_auto = less_than_auto->complement();
	delete less_than_auto;
	return greater_than_or_equal_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAnyAutoUnaligned(int num_tracks) {
	DFA_ptr result, temp;
	int len = VAR_PER_TRACK * num_tracks;
	int *mindices = Automaton::getIndices(num_tracks*VAR_PER_TRACK);
	std::vector<char> str(len, 'X');
	str.push_back('\0');

	dfaSetup(1, len, mindices);
	dfaAllocExceptions(1);
	dfaStoreException(0,&str[0]);
	dfaStoreState(0);

	temp = dfaBuild("+");
	result = dfaMinimize(temp);
	dfaFree(temp);
	delete[] mindices;
	return new MultiTrackAutomaton(result,num_tracks);
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::makeAnyAutoAligned(int num_tracks) {
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

MultiTrackAutomaton_ptr MultiTrackAutomaton::complement() {
  DFA_ptr complement_dfa = nullptr;
  MultiTrackAutomaton_ptr temp_auto = nullptr, complement_auto = nullptr, aligned_universe_auto = nullptr;
	complement_dfa = dfaCopy(this->dfa);
	dfaNegation(complement_dfa);
	temp_auto = new MultiTrackAutomaton(complement_dfa,this->num_of_tracks);
	aligned_universe_auto = makeAnyAutoAligned(this->num_of_tracks);
	complement_auto = temp_auto->intersect(aligned_universe_auto);
	complement_auto->setRelation(getRelationClone());
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
	union_auto->setRelation(getRelationClone());
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
	difference_auto->setRelation(getRelationClone());
	delete complement_auto; complement_auto = nullptr;
	return difference_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::intersect(MultiTrackAutomaton_ptr other_auto) {
	DFA_ptr intersect_dfa, minimized_dfa = nullptr;
	MultiTrackAutomaton_ptr intersect_auto = nullptr;
	StringRelation_ptr intersect_relation = nullptr;
	if (this->num_of_tracks != other_auto->num_of_tracks) {
		LOG(ERROR) << "Error in MultiTrackAutomaton::intersect, unequal track numbers";
		return this->clone();
	}
	intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaAND);
	minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
	intersect_auto = new MultiTrackAutomaton(minimized_dfa, this->num_of_tracks);

	if(this->relation == nullptr && other_auto->relation == nullptr) {
		LOG(FATAL) << "No relation set for either multitrack during intersection";
	} else if(other_auto->relation == nullptr) {
		intersect_relation = this->relation->clone();
	} else if(this->relation == nullptr) {
		intersect_relation = other_auto->relation->clone();
	} else {
		intersect_relation = this->relation->combine(other_auto->relation);
	}
	intersect_auto->setRelation(intersect_relation);
	return intersect_auto;
}

MultiTrackAutomaton_ptr MultiTrackAutomaton::projectKTrack(int k_track) {
	MultiTrackAutomaton_ptr result_auto;
	DFA_ptr temp,result_dfa = this->dfa;
	int flag = 0;

	int *map = getIndices(this->num_of_tracks*VAR_PER_TRACK);

	for(int i = 0,k=0,l=0; i < this->num_of_variables; i++) {
	    if(i == k_track+l*this->num_of_tracks) {
	        map[i] = (this->num_of_tracks-1)*VAR_PER_TRACK+l;
	        l++;
	        continue;
	    }
	    map[i] = k++;
	}

		for(unsigned j = 0; j < VAR_PER_TRACK; j++) {
		temp = dfaProject(result_dfa,k_track+this->num_of_tracks*j);
		if(flag)
			dfaFree(result_dfa);
		result_dfa = dfaMinimize(temp);
		flag = 1;
		dfaFree(temp);
	}
	dfaReplaceIndices(result_dfa,map);
	delete[] map;
	result_auto = new MultiTrackAutomaton(result_dfa,this->num_of_tracks-1);
	result_auto->setRelation(getRelationClone());
	return result_auto;
}

//TODO: Why doesn't k=0 work?
StringAutomaton_ptr MultiTrackAutomaton::getKTrack(int k_track) {
	DFA_ptr result = this->dfa, temp;
	StringAutomaton_ptr result_auto = nullptr;
	int flag = 0;

	if(k_track >= this->num_of_tracks) {
		std::cerr << "error in MultiTrackAutomaton::getKTrack" << std::endl;
		exit(1);
	} else if(this->num_of_tracks == 1) {
	    result= removeLambdaSuffix(this->dfa,VAR_PER_TRACK);
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
		result = removeLambdaSuffix(m1->dfa,VAR_PER_TRACK);
		delete m1; m1 = nullptr;
		result_auto = new StringAutomaton(result);
		return result_auto;
	}

    // k_track needs to be mapped to indices 0-VAR_PER_TRACK
    // while all others need to be pushed back by VAR_PER_TRACK, then
    // interleaved with 1 less than current number of tracks
	int* map = getIndices(this->num_of_tracks*VAR_PER_TRACK);
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
	temp = removeLambdaSuffix(result, VAR_PER_TRACK);
	dfaFree(result);
	result = temp;
	delete[] map;
	return new StringAutomaton(result);
}

std::vector<std::string> MultiTrackAutomaton::getAnAcceptingStringForEachTrack() {
  std::vector<std::string> strings(num_of_tracks, "");
  std::vector<bool>* example = getAnAcceptingWord();
  unsigned char c = 0;
  unsigned num_transitions = example->size() / num_of_variables;
  bool bit;
  unsigned sharp1 = 254, sharp2 = 255;

  DVLOG(VLOG_LEVEL) << "We got: " << num_transitions << " transitions";

  for(int t = 0; t < num_transitions; t++) {
    unsigned offset = t*num_of_variables;
    for (int i = 0; i < num_of_tracks; i++) {
      for (int j = 0; j < VAR_PER_TRACK; j++) {
        bit = (*example)[offset+i+num_of_tracks*j];
        if(bit) {
          c |= 1;
        } else {
          c |= 0;
        }
        if(j != VAR_PER_TRACK-1) {
          c <<= 1;
        }
      }
      if(c != sharp1 && c != sharp2) strings[i] += c;
      c = 0;
    }
  }
  delete example;
  return strings;
}

int MultiTrackAutomaton::getNumTracks() const {
	return this->num_of_tracks;
}

StringRelation_ptr MultiTrackAutomaton::getRelation() {
  return this->relation;
}

StringRelation_ptr MultiTrackAutomaton::getRelationClone() const {
  return this->relation->clone();
}

bool MultiTrackAutomaton::setRelation(StringRelation_ptr relation) {
  if(this->relation == nullptr) {
    delete this->relation;
  }
  this->relation = relation;
  return true;
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

DFA_ptr MultiTrackAutomaton::removeLambdaSuffix(DFA_ptr dfa, int num_vars) {
	DFA_ptr result_dfa, temp;
	paths state_paths, pp;
	trace_descr tp;
	char* statuses;
	int *indices;
	int sink;
	std::string symbol;
	std::vector<std::pair<std::string,int>> state_exeps;
	indices = Automaton::getIndices(num_vars);
	sink = find_sink(dfa);

	dfaSetup(dfa->ns, num_vars, indices);
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
				for (unsigned j = 0; j < num_vars; j++) {
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);

					if (tp) {
						if (tp->value) symbol += '1';
						else symbol += '0';
					}
					else
						symbol += 'X';
				}
				if (MultiTrackAutomaton::checkLambda(symbol, 0, 1, num_vars)) {
					statuses[i] = '+';
				}
				else {
					state_exeps.push_back(std::make_pair(symbol, pp->to));
				}
				symbol = "";
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		dfaAllocExceptions(state_exeps.size());
		for (unsigned k = 0; k < state_exeps.size(); k++) {
			std::vector<char> v = std::vector<char>(state_exeps[k].first.begin(), state_exeps[k].first.end());
			v.push_back('\0');
			dfaStoreException(state_exeps[k].second,&v[0]);
		}
		dfaStoreState(sink);
		state_exeps.clear();
	}
	statuses[dfa->ns] = '\0';
	temp = dfaBuild(statuses);
	result_dfa = dfaMinimize(temp);
	dfaFree(temp);

	delete[] statuses;
	delete[] indices;
	return result_dfa;
}

DFA_ptr MultiTrackAutomaton::makeConcreteDFA() {
	DFA_ptr result_dfa;
	int *indices = getIndices(VAR_PER_TRACK);
	int nump = 1 << VAR_PER_TRACK;

	dfaSetup(2,VAR_PER_TRACK,indices);
	dfaAllocExceptions(nump-1);
	for(int i = 0; i < nump-1; i++) {
		std::vector<char> exep = getBinaryFormat(i,VAR_PER_TRACK);
		exep.push_back('\0');
		dfaStoreException(0,&exep[0]);
	}
	dfaStoreState(1);

	dfaAllocExceptions(0);
	dfaStoreState(1);

	result_dfa = dfaBuild("+-");
	delete[] indices;
	return result_dfa;

}

} /* namespace Vlab */
} /* namespace Theory */
