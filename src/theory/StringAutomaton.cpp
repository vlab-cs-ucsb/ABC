/*
 * StringAutomaton.cpp
 *
 *  Created on: Aug 14, 2017
 *      Author: will
 */

#include "StringAutomaton.h"

namespace Vlab {
namespace Theory {

StringAutomaton::TransitionTable StringAutomaton::TRANSITION_TABLE;

StringAutomaton::StringAutomaton(const DFA_ptr dfa, const int number_of_tracks, const int number_of_bdd_variables)
		:	Automaton(Automaton::Type::MULTITRACK, dfa, number_of_bdd_variables),
			num_tracks_(number_of_tracks),
			formula_(nullptr) {

}

StringAutomaton::StringAutomaton(const DFA_ptr dfa, const int i_track, const int number_of_tracks, const int in_num_vars)
		:	Automaton(Automaton::Type::MULTITRACK, nullptr, number_of_tracks * VAR_PER_TRACK),
			num_tracks_(number_of_tracks),
			formula_(nullptr) {
	DFA_ptr M = dfa, temp = nullptr, result = nullptr;
	trace_descr tp;
	paths state_paths, pp;
	std::vector<std::pair<std::vector<char>,int>> state_exeps;
	int sink;
	char* statuses;
	int* mindices;
	bool has_sink = true;
	int num_states = M->ns+1; // lambda state
	int lambda_state = num_states-1;
	int var = VAR_PER_TRACK;
	int len = (num_tracks_ * var)+1; // extrabit for nondeterminism
	mindices = GetBddVariableIndices(len);

	sink = find_sink(M);
	if(sink < 0) {
		has_sink = false;
		sink = num_states;
		num_states++;
	}

	statuses = new char[num_states+1];
	// begin dfa building process
	// old transitions end in '0'
	// new transitions end in '1' (lambda transitions)

	dfaSetup(num_states, len, mindices);
	for(unsigned i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);

		// if state is final, add lambda transition to lambda state
		if(M->f[i] == 1) {
			std::vector<char> curr(len,'X');
			for(int k = 0; k < var; k++) {
				curr[i_track+num_tracks_*k] = '1';
			}
			curr[len-1] = '1'; // new transition, end with '1'
			curr.push_back('\0');
			state_exeps.push_back(std::make_pair(curr,lambda_state));
		}

		while(pp) {
			if(pp->to != sink) {
				std::vector<char> curr(len,'X');
				for(unsigned j = 0; j < in_num_vars; j++) {
					for(tp = pp->trace; tp && (tp->index != mindices[j]); tp = tp->next);
					if(tp) {
						if(tp->value) curr[i_track+num_tracks_*j] = '1';
						else curr[i_track+num_tracks_*j] = '0';
					}
					else
						curr[i_track+num_tracks_*j] = 'X';
				}
				// if default_num_Var, make default_num_var+1 index '0' for non-lambda
				if(in_num_vars == DEFAULT_NUM_OF_VARIABLES) {
					curr[i_track+num_tracks_*(DEFAULT_NUM_OF_VARIABLES)] = '0';
				}
				curr[len-1] = '0'; // old transition, end with '0'
				curr.push_back('\0');
				state_exeps.push_back(std::make_pair(curr,pp->to));
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		dfaAllocExceptions(state_exeps.size());
		for(unsigned k = 0; k < state_exeps.size(); ++k) {
			dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
		}
		dfaStoreState(sink);
		state_exeps.clear();

		statuses[i] = '-';
	}

	// lambda state, loop de loop
	dfaAllocExceptions(1);
	std::vector<char> str(len,'X');
	for(int i = 0; i < var; i++) {
		str[i_track+num_tracks_*i] = '1';
	}
	str[len-1] = '1';
	str.push_back('\0');
	dfaStoreException(lambda_state,&str[0]);
	dfaStoreState(sink);
	statuses[lambda_state] = '+';

	// extra sink state, if needed
	if(!has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuses[sink] = '-';
	}

	statuses[num_states] = '\0';
	result = dfaBuild(statuses);
	temp = dfaMinimize(result);
	dfaFree(result);
	// project away the extra bit
	result = dfaProject(temp,len-1);
	dfaFree(temp);
	temp = dfaMinimize(result);
	dfaFree(result);
	result = temp;

	delete[] statuses;
	this->dfa_ = result;
}

StringAutomaton::StringAutomaton(const DFA_ptr dfa, StringFormula_ptr formula, const int number_of_bdd_variables)
		:	Automaton(Automaton::Type::MULTITRACK, dfa, number_of_bdd_variables) {
	if(formula == nullptr) {
		LOG(FATAL) << "formula is nullptr!";
	}

	this->num_tracks_ = formula->GetNumberOfVariables();
	formula_ = formula;
}

StringAutomaton::StringAutomaton(const StringAutomaton& other)
		:	Automaton(other) {
	this->num_tracks_ = other.num_tracks_;
	if(other.formula_ != nullptr) {
		this->formula_ = other.formula_->clone();
	}
}

StringAutomaton::~StringAutomaton() {
	delete formula_;
}

StringAutomaton_ptr StringAutomaton::clone() const {
	return new StringAutomaton(*this);
}

const StringAutomaton::TransitionVector& StringAutomaton::GenerateTransitionsForRelation(StringFormula::Type type, int bits_per_var) {
  bits_per_var--;
  // check table for precomputed value first
  std::pair<int,StringFormula::Type> key(bits_per_var,type);
  if(TRANSITION_TABLE.find(key) != TRANSITION_TABLE.end()) {
    return TRANSITION_TABLE[key];
  }

  // not previously computed; compute now and cache for later.
  bool final_states[3] = {false,false,false};
  switch(type) {
    case StringFormula::Type::EQ:
      final_states[0] = true;
      break;
    case StringFormula::Type::NOTEQ:
      final_states[1] = true;
      final_states[2] = true;
      break;
    case StringFormula::Type::LT:
      final_states[1] = true;
      break;
    case StringFormula::Type::LE:
      final_states[0] = true;
      final_states[1] = true;
      break;
    case StringFormula::Type::GT:
      final_states[2] = true;
      break;
    case StringFormula::Type::GE:
      final_states[0] = true;
      final_states[2] = true;
      break;
    default:
      LOG(FATAL) << "Invalid relation ordering type";
      break;
  }

  std::vector<std::map<std::string,int>> states(3, std::map<std::string, int>());
  states[0]["00"] = 0;
  states[0]["01"] = 1;
  states[0]["10"] = 2;
  states[0]["11"] = 0;

  states[1]["XX"] = 1;
  states[2]["XX"] = 2;

  TransitionVector good_trans;
  std::queue<std::pair<int,std::pair<std::string,std::string>>> next;
  next.push(std::make_pair(0,std::make_pair("","")));

  while(!next.empty()) {
    std::pair<int,std::pair<std::string,std::string>> curr = next.front();
    if(curr.second.first.size() >= bits_per_var) {
      if(final_states[curr.first]) {
        // append lambda bit for multitrack lambda
        curr.second.first += '0';
        curr.second.second += '0';
        good_trans.push_back(curr.second);
      }
    } else {
      for(auto& t : states[curr.first]) {
        next.push(std::make_pair(
            t.second,
            std::make_pair(
                curr.second.first + std::string(1,t.first[0]),
                curr.second.second + std::string(1,t.first[1]))));
      }
    }
    next.pop();
  }

  // cache the transitions for later
  TRANSITION_TABLE[key] = good_trans;

  return TRANSITION_TABLE[key];
}

DFA_ptr StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type type, int bits_per_var, int num_tracks, int left_track, int right_track) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr, aligned_dfa = nullptr;
  int var = bits_per_var;
  int len = num_tracks * var;
  int *mindices = GetBddVariableIndices(num_tracks*var);
  int eq = 0,
      left = 1,
      right = 2,
      sink = 3;
  char statuses[5] = {"----"};
  std::vector<std::pair<std::vector<char>,int>> exeps;
  TransitionVector tv_eq, tv_left, tv_right;
  tv_eq = GenerateTransitionsForRelation(StringFormula::Type::EQ,bits_per_var);
  tv_left = GenerateTransitionsForRelation(StringFormula::Type::LT,bits_per_var);
  tv_right = GenerateTransitionsForRelation(StringFormula::Type::GT,bits_per_var);

  switch(type) {
    case StringFormula::Type::EQ:
      statuses[eq] = '+';
      break;
    case StringFormula::Type::NOTEQ:
      statuses[left] = '+';
      statuses[right] = '+';
      break;
    case StringFormula::Type::LT:
      statuses[left] = '+';
      break;
    case StringFormula::Type::LE:
      statuses[eq] = '+';
      statuses[left] = '+';
      break;
    case StringFormula::Type::GT:
      statuses[right] = '+';
      break;
    case StringFormula::Type::GE:
      statuses[eq] = '+';
      statuses[right] = '+';
      break;
    default:
      DVLOG(VLOG_LEVEL) << "Invalid stringrelation type! can't make dfa...";
      delete mindices;
      return nullptr;
  }

  for(auto& t : tv_eq) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = t.first[k];
      str[right_track+num_tracks*k] = t.second[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,eq));
  }

  for(auto& t : tv_left) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = t.first[k];
      str[right_track+num_tracks*k] = t.second[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,left));
  }

  for(auto& t : tv_right) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = t.first[k];
      str[right_track+num_tracks*k] = t.second[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,right));
  }

  std::vector<char> str(len,'X');
  for(int k = 0; k < var; k++) {
    str[left_track+num_tracks*k] = '1';
    str[right_track+num_tracks*k] = '1';
  }
  str.push_back('\0');
  exeps.push_back(std::make_pair(str,eq));

  for(int k = 0; k < var-1; k++) {
    str[left_track + num_tracks * k] = 'X';
    str[right_track+ num_tracks * k] = '1';
  }
  str[left_track+num_tracks*(var-1)] = '0';
  str[right_track+num_tracks*(var-1)] = '1';
  exeps.push_back(std::make_pair(str,right));

  for(int k = 0; k < var-1; k++) {
    str[left_track + num_tracks * k] = '1';
    str[right_track+ num_tracks * k] = 'X';
  }
  str[left_track+num_tracks*(var-1)] = '1';
  str[right_track+num_tracks*(var-1)] = '0';
  exeps.push_back(std::make_pair(str,left));


  dfaSetup(4,len,mindices);
  dfaAllocExceptions(exeps.size());
  for(int i = 0; i < exeps.size(); i++) {
    dfaStoreException(exeps[i].second, &(exeps[i].first)[0]);
  }
  dfaStoreState(sink);
  exeps.clear();

  dfaAllocExceptions(0);
  dfaStoreState(left);

  dfaAllocExceptions(0);
  dfaStoreState(right);

  // sink
  dfaAllocExceptions(0);
  dfaStoreState(sink);

  // build it!
  temp_dfa = dfaBuild(statuses);
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);

  aligned_dfa = MakeBinaryAlignedDfa(left_track,right_track,num_tracks);
  temp_dfa = dfaProduct(result_dfa,aligned_dfa,dfaAND);

  dfaFree(result_dfa);
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  dfaFree(aligned_dfa);

  return result_dfa;
}

DFA_ptr StringAutomaton::MakeBinaryAlignedDfa(int left_track, int right_track, int num_tracks) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  TransitionVector tv;
  int init = 0,lambda_star = 1, lambda_lambda = 2,
      star_lambda = 3, sink = 4;
  int var = VAR_PER_TRACK;
  int len = num_tracks * var;
  int *mindices = GetBddVariableIndices(num_tracks*var);
  std::vector<char> exep_lambda(var,'1');
  std::vector<char> exep_dont_care(var,'X');
  exep_dont_care[var-1] = '0';
  tv = GenerateTransitionsForRelation(StringFormula::Type::EQ,var);

  dfaSetup(5,len,mindices);

  // ---- init state
  // if lambda/star goto lambda_star,
  // if star/lambda goto star_lambda,
  // if lambda_lambda goto lambda_lambda,
  // if star/star, loop
  // else, sink

  std::vector<char> str(len,'X');
  str.push_back('\0');

  dfaAllocExceptions(4);
  // x,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_dont_care[i];
    str[right_track+num_tracks*i] = exep_dont_care[i];
  }
  dfaStoreException(init, &str[0]);

  // x,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_dont_care[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(star_lambda, &str[0]);

  // lambda,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_dont_care[i];
  }
  dfaStoreException(lambda_star, &str[0]);

  //lambda,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- lambda_star state ----

  dfaAllocExceptions(2);
  // lambda,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_dont_care[i];
  }
  dfaStoreException(lambda_star, &str[0]);
  //lambda,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- lambda_lambda state ----

  dfaAllocExceptions(1);
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- star_lambda state ----

  dfaAllocExceptions(2);
  // lambda,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_dont_care[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(star_lambda, &str[0]);
  //lambda,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- sink state -----

  dfaAllocExceptions(0);
  dfaStoreState(sink);

  temp_dfa = dfaBuild("--+--");
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);

  return result_dfa;
}

StringAutomaton_ptr StringAutomaton::MakePrefixSuffix(int left_track, int prefix_track, int suffix_track, int num_tracks) {
	StringAutomaton_ptr result_auto = nullptr;
  DFA_ptr temp_dfa, result_dfa;
  TransitionVector tv;

  int var = VAR_PER_TRACK;
  int len = num_tracks * var;
  static int *mindices = GetBddVariableIndices(num_tracks*var);
  std::vector<char> exep_lambda(var,'1');
  tv = GenerateTransitionsForRelation(StringFormula::Type::EQ, var);

  dfaSetup(4,len,mindices);
  dfaAllocExceptions(2*tv.size() + 1); // 1 extra for lambda stuff below
  for(int i = 0; i < tv.size(); i++) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = tv[i].first[k];
      str[prefix_track+num_tracks*k] = tv[i].first[k];
      str[suffix_track+num_tracks*k] = exep_lambda[k];
    }
    str.push_back('\0');
    dfaStoreException(0,&str[0]);
  }

  // if prefix is lambda, left  and suffix same
  for(int i = 0; i < tv.size(); i++) {
    std::vector<char> str(len,'X');
    for (int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = tv[i].first[k];
      str[prefix_track+num_tracks*k] = exep_lambda[k];
      str[suffix_track+num_tracks*k] = tv[i].first[k];
    }
    str.push_back('\0');
    dfaStoreException(1,&str[0]);
  }

  // if all 3 are lambda, go to next state
  std::vector<char> str(len,'X');
  str = std::vector<char>(len,'X');
  for(int k = 0; k < var; k++) {
    str[left_track+num_tracks*k] = exep_lambda[k];
    str[prefix_track+num_tracks*k] = exep_lambda[k];
    str[suffix_track+num_tracks*k] = exep_lambda[k];
  }
  str.push_back('\0');
  dfaStoreException(2,&str[0]);
  dfaStoreState(3);

  // left = suffix, prefix lambda, loop back here
  dfaAllocExceptions(tv.size() + 1);
  for(int i = 0; i < tv.size(); i++) {
    std::vector<char> str(len,'X');
    for (int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = tv[i].first[k];
      str[prefix_track+num_tracks*k] = exep_lambda[k];
      str[suffix_track+num_tracks*k] = tv[i].first[k];
    }
    str.push_back('\0');
    dfaStoreException(1,&str[0]);
  }
  // if all 3 lambda, goto 2
  str = std::vector<char>(len,'X');
  for(int k = 0; k < var; k++) {
    str[left_track+num_tracks*k] = exep_lambda[k];
    str[prefix_track+num_tracks*k] = exep_lambda[k];
    str[suffix_track+num_tracks*k] = exep_lambda[k];
  }
  str.push_back('\0');
  dfaStoreException(2,&str[0]);
  dfaStoreState(3);

  // lambda/lambda state, loop back on lambda
  dfaAllocExceptions(1);
  dfaStoreException(2,&str[0]);
  dfaStoreState(3);

  // sink
  dfaAllocExceptions(0);
  dfaStoreState(3);

  temp_dfa = dfaBuild("--+-");
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  result_auto = new StringAutomaton(result_dfa,num_tracks);

  return result_auto;
  return nullptr;
}

bool StringAutomaton::IsExepEqualChar(std::vector<char> exep, std::vector<char> cvec, int var) {
  for(int i = 0; i < var; i++) {
    if(exep[i] != cvec[i])
      return false;
  }
  return true;
}

bool StringAutomaton::IsExepIncludeChar(std::vector<char> exep, std::vector<char> cvec, int var) {
  for(int i = 0; i < var; i++) {
    if(exep[i] != 'X' && exep[i] != cvec[i])
      return false;
  }
  return true;
}

// resulting dfa has 1 more bit for lambda stuff
DFA_ptr StringAutomaton::PrependLambda(DFA_ptr dfa, int var) {
  if(var != DEFAULT_NUM_OF_VARIABLES) {
    LOG(FATAL) << "mismatched incoming var";
  }
  DFA_ptr M = dfa, temp = nullptr, result = nullptr;
  trace_descr tp;
  paths state_paths, pp;
  std::vector<std::pair<std::vector<char>,int>> state_exeps;
  int num_states = M->ns+1;
  int sink = Automaton::find_sink(M);
  bool has_sink = true;

  if(sink < 0) {
    has_sink = false;
    sink = num_states;
    num_states++;
  } else {
    sink++; // +1 for new state
  }

  char* statuses;
  int* mindices;
  int len = VAR_PER_TRACK; // 1 more than default_num_var

  mindices = GetBddVariableIndices(len);
  statuses = new char[num_states+1];

  // begin dfa building process
  dfaSetup(num_states, len, mindices);

  // setup for initial state
  state_paths = pp = make_paths(M->bddm, M->q[0]);
  while(pp) {
    if(pp->to != sink-1) {
      std::vector<char> curr(len,'0');
      for(unsigned j = 0; j < var; j++) {
        for(tp = pp->trace; tp && (tp->index != mindices[j]); tp = tp->next);
        if(tp) {
          if(tp->value) curr[j] = '1';
          else curr[j] = '0';
        }
        else
          curr[j] = 'X';
      }
      curr.push_back('\0');
      state_exeps.push_back(std::make_pair(curr,pp->to+1));
    }
    pp = pp->next;
  }
  kill_paths(state_paths);

  // add lambda loop to self
  std::vector<char> str(len,'1');
  str.push_back('\0');
  state_exeps.push_back(std::make_pair(str,0));
  dfaAllocExceptions(state_exeps.size());
  for(unsigned k = 0; k < state_exeps.size(); ++k) {
    dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
  }
  dfaStoreState(sink);

  state_exeps.clear();
  if(M->f[0] == 1) {
    statuses[0] = '+';
  } else {
    statuses[0] = '-';
  }

  // rest of states (shift 1)
  for(unsigned i = 0; i < M->ns; i++) {
    state_paths = pp = make_paths(M->bddm, M->q[i]);

    while(pp) {
      if(pp->to != sink-1) {
        std::vector<char> curr(len,'0');
        for(unsigned j = 0; j < var; j++) {
          for(tp = pp->trace; tp && (tp->index != mindices[j]); tp = tp->next);
          if(tp) {
            if(tp->value) curr[j] = '1';
            else curr[j] = '0';
          }
          else
            curr[j] = 'X';
        }
        curr.push_back('\0');
        state_exeps.push_back(std::make_pair(curr,pp->to+1));
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    dfaAllocExceptions(state_exeps.size());
    for(unsigned k = 0; k < state_exeps.size(); ++k) {
      dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
    }
    dfaStoreState(sink);
    state_exeps.clear();

    if(M->f[i] == 1) {
      statuses[i+1] = '+';
    } else if(M->f[i] == -1) {
      statuses[i+1] = '-';
    } else {
      statuses[i+1] = '0';
    }
  }

  if(!has_sink) {
    dfaAllocExceptions(0);
    dfaStoreState(sink);
    statuses[sink] = '-';
  }

  statuses[num_states] = '\0';
  temp = dfaBuild(statuses);
  result = dfaMinimize(temp);
  dfaFree(temp);

  delete[] statuses;

  return result;
}

// incoming dfa has extrabit for lambda
// remove lambda transitions and project away extra bit
DFA_ptr StringAutomaton::TrimLambdaPrefix(DFA_ptr dfa, int var, bool project_bit) {
  if(var != VAR_PER_TRACK) {
    LOG(FATAL) << "not correct var";
  }
  DFA_ptr result_dfa = nullptr, temp_dfa = nullptr;
  paths state_paths, pp;
  trace_descr tp;
  char* statuses;
  int *indices = Automaton::GetBddVariableIndices(var);
  int sink = find_sink(dfa);
  CHECK_GT(sink,-1);
  std::vector<char> lambda_vec(var,'1');
  // start at start-state
  // if transition is lambda, we need to add that "to" state to the
  // pool of possible start states
  std::vector<bool> states_visited(dfa->ns,false);
  std::vector<int> reachable;
  std::queue<int> states_to_visit;

  states_to_visit.push(dfa->s);
  states_visited[dfa->s] = true;
  reachable.push_back(dfa->s);

  while(!states_to_visit.empty()) {
    int state = states_to_visit.front();
    states_to_visit.pop();
    state_paths = pp = make_paths(dfa->bddm, dfa->q[state]);
    std::vector<char> exep(var,'X');
    while(pp) {
      if(pp->to == sink) {
        pp = pp->next;
        continue;
      }

      for(int j = 0; j < var; j++) {
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) exep[j] = '1';
          else exep[j] = '0';
        }
        else
          exep[j] = 'X';
      }

      if (IsExepEqualChar(exep, lambda_vec,var) ) {
        if(states_visited[pp->to]) {
          pp = pp->next;
          continue;
        }
        states_to_visit.push(pp->to);
        states_visited[pp->to] = true;
        reachable.push_back(pp->to);
      }
      pp = pp->next;
    }
    kill_paths(state_paths);
  }

  int num_initial = reachable.size();
  int num_bits = std::ceil(std::log2(num_initial));
  int len = var + num_bits;

  // one new "initial" state, which encompasses all reachable states
  // by lambda
  int num_states = dfa->ns+1;
  std::vector<std::pair<std::vector<char>,int>> state_exeps;
  indices = GetBddVariableIndices(len);
  statuses = new char[num_states+1];

  // if any of the reachable states are final, then the new
  // initial state is final
  statuses[0] = '-';
  for(int i = 0; i < reachable.size(); i++) {
    if(dfa->f[reachable[i]] == 1) {
      statuses[0] = '+';
    }
  }

  dfaSetup(num_states,len,indices);
  // setup new "initial" state first
  for(int i = 0; i < reachable.size(); i++) {
    state_paths = pp = make_paths(dfa->bddm, dfa->q[reachable[i]]);
    std::vector<char> exep(var,'X');
    while(pp) {
      if(pp->to == sink) {
        pp = pp->next;
        continue;
      }
      for(int j = 0; j < var; j++) {
        for(tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if(tp) {
          if(tp->value) {
            exep[j] = '1';
          } else {
            exep[j] = '0';
          }
        } else {
          exep[j] = 'X';
        }
      }

      if (!IsExepEqualChar(exep, lambda_vec,var)) {
        std::vector<char> extra_bit_value = GetBinaryFormat(i, num_bits); // i = current state
        std::vector<char> v = exep;
        v.insert(v.end(), extra_bit_value.begin(), extra_bit_value.end());
        state_exeps.push_back(std::make_pair(v, pp->to + 1));
      }
      pp = pp->next;
    }
    kill_paths(state_paths);
  }

  dfaAllocExceptions(state_exeps.size());
  for(int i = 0; i < state_exeps.size(); i++) {
    dfaStoreException(state_exeps[i].second,&state_exeps[i].first[0]);
  }
  dfaStoreState(sink+1);
  state_exeps.clear();

  // continue with rest of states
  for(int i = 0; i < dfa->ns; i++) {
    statuses[i+1] = '-';
    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
    while(pp) {
      if (pp->to == sink) {
        pp = pp->next;
        continue;
      }
      std::vector<char> exep(var,'X');
      for (int j = 0; j < var; j++) {
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) exep[j] = '1';
          else exep[j] = '0';
        }
        else
          exep[j] = 'X';
      }
      // if not lambda, then add transition, with 0s padded on end
      if (!IsExepEqualChar(exep, lambda_vec,var)) {
        for (int k = 0; k < num_bits; k++) {
          exep.push_back('0');
        }
        exep.push_back('\0');
        state_exeps.push_back(std::make_pair(exep,pp->to+1));
      } else if(dfa->f[pp->to == 1]) {
        statuses[i+1] = '+';
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    dfaAllocExceptions(state_exeps.size());
    for(int j = 0; j < state_exeps.size(); j++) {
      dfaStoreException(state_exeps[j].second, &state_exeps[j].first[0]);
    }
    dfaStoreState(sink+1);
    state_exeps.clear();

    if(dfa->f[i] == 1) {
      statuses[i+1] = '+';
    }
  }

  statuses[num_states] = '\0';

  temp_dfa = dfaBuild(statuses);
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  if(project_bit) {
    // project away the last bit as well
    num_bits++;
  }

  for(int i = 0; i < num_bits; i++) {
    int bit = len-i-1;
    temp_dfa = dfaProject(result_dfa,(unsigned)bit);
    dfaFree(result_dfa);
    result_dfa = dfaMinimize(temp_dfa);
    dfaFree(temp_dfa);
  }

  delete[] statuses;

  return result_dfa;
}

// var should be 9
DFA_ptr StringAutomaton::TrimLambdaSuffix(DFA_ptr dfa, int var, bool project_bit) {
  if(var != VAR_PER_TRACK) {
    LOG(FATAL) << "Bad nuber o bits!";
  }

  DFA_ptr result_dfa = nullptr, temp = nullptr;
  paths state_paths, pp;
  trace_descr tp;
  char* statuses = new char[dfa->ns+1];
  int *indices = Automaton::GetBddVariableIndices(var);
  int sink = find_sink(dfa);
  CHECK_GT(sink,-1);

  std::vector<std::pair<std::vector<char>,int>> state_exeps;
  std::vector<char> lambda_vec(var,'1');
  dfaSetup(dfa->ns, var, indices);
  for(int i = 0; i < dfa->ns; i++) {
    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
    statuses[i] = '-';
    while (pp) {
      if (pp->to != sink) {
        std::vector<char> exep(var,'X');
        for (unsigned j = 0; j < var; j++) {
          for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);

          if (tp) {
            if (tp->value) exep[j] = '1';
            else exep[j] = '0';
          }
          else
            exep[j] = 'X';
        }

        bool is_lam = IsExepEqualChar(exep,lambda_vec,var);
        if (is_lam && i == pp->to) {

        }
        else {
          exep.push_back('\0');
          state_exeps.push_back(std::make_pair(exep, pp->to));
          if(is_lam && dfa->f[pp->to] == 1) {
            statuses[i] = '+';
          }
        }
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    dfaAllocExceptions(state_exeps.size());
    for (unsigned k = 0; k < state_exeps.size(); k++) {
      dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
    }
    dfaStoreState(sink);
    state_exeps.clear();
  }
  statuses[dfa->ns] = '\0';
  temp = dfaBuild(statuses);
  result_dfa = dfaMinimize(temp);
  dfaFree(temp);

  if(project_bit) {
    // project away extra bit
    temp = dfaProject(result_dfa, var - 1);
    dfaFree(result_dfa);
    result_dfa = dfaMinimize(temp);
    dfaFree(temp);
  }

  delete[] statuses;

  return result_dfa;
}

DFA_ptr StringAutomaton::TrimPrefix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  RelationalStringAutomaton_ptr temp_multi = nullptr, subject_multi = nullptr,
                          trim_multi = nullptr, intersect_multi = nullptr;
  StringAutomaton_ptr result_string_auto = nullptr;

  // (x,x,lambda) until track 2 is lambda
  // (x,lambda,x) until end
  temp_multi = MakePrefixSuffix(0,1,2,3);
  subject_multi = new StringAutomaton(subject_dfa,0,3, DEFAULT_NUM_OF_VARIABLES);
  trim_multi = new StringAutomaton(trim_dfa,1,3, DEFAULT_NUM_OF_VARIABLES);

  intersect_multi = temp_multi->Intersect(subject_multi);
  delete temp_multi;
  delete subject_multi;

  temp_multi = intersect_multi;
  intersect_multi = temp_multi->Intersect(trim_multi);
  delete temp_multi;
  delete trim_multi;

  // 3rd track has lambda prefix, so get it (automatically removes lambda prefix/suffix)
  result_string_auto = intersect_multi->GetKTrack(2);
  result_dfa = dfaCopy(result_string_auto->getDFA());
  delete intersect_multi;
  delete result_string_auto;

  return result_dfa;
}

DFA_ptr StringAutomaton::TrimSuffix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  RelationalStringAutomaton_ptr temp_multi = nullptr, subject_multi = nullptr,
                          trim_multi = nullptr, intersect_multi = nullptr;
  StringAutomaton_ptr result_string_auto = nullptr;

  // (x,x,lambda) until track 2 is lambda
  // (x,lambda,x) until end
  temp_multi = MakePrefixSuffix(0,1,2,3);
  subject_multi = new StringAutomaton(subject_dfa,0,3,DEFAULT_NUM_OF_VARIABLES);
  // gotta prepend trim_dfa first, to go on track 3
  temp_dfa = PrependLambda(trim_dfa,var);
  trim_multi = new StringAutomaton(temp_dfa,2,3,VAR_PER_TRACK);
  dfaFree(temp_dfa);

  intersect_multi = temp_multi->Intersect(subject_multi);
  delete temp_multi;
  delete subject_multi;

  temp_multi = intersect_multi;
  intersect_multi = temp_multi->Intersect(trim_multi);
  delete temp_multi;
  delete trim_multi;

  result_string_auto = intersect_multi->GetKTrack(1);
  result_dfa = dfaCopy(result_string_auto->getDFA());
  delete intersect_multi;
  delete result_string_auto;

  return result_dfa;
}

DFA_ptr StringAutomaton::concat(DFA_ptr prefix_dfa, DFA_ptr suffix_dfa, int var) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  RelationalStringAutomaton_ptr temp_multi = nullptr, prefix_multi = nullptr,
                          suffix_multi = nullptr, intersect_multi = nullptr;
  StringAutomaton_ptr result_string_auto = nullptr;

  // (x,x,lambda) until track 2 is lambda
  // (x,lambda,x) until end

  temp_multi = MakePrefixSuffix(0,1,2,3);
  prefix_multi = new StringAutomaton(prefix_dfa,1,3,var);
  temp_dfa = PrependLambda(suffix_dfa,var);
  suffix_multi = new StringAutomaton(temp_dfa,2,3,VAR_PER_TRACK);
  dfaFree(temp_dfa);
  intersect_multi = temp_multi->Intersect(prefix_multi);
  delete temp_multi;
  delete prefix_multi;
  temp_multi = intersect_multi;
  intersect_multi = temp_multi->Intersect(suffix_multi);
  delete temp_multi;
  delete suffix_multi;
  result_string_auto = intersect_multi->GetKTrack(0);
  result_dfa = dfaCopy(result_string_auto->getDFA());
  delete intersect_multi;
  delete result_string_auto;
  return result_dfa;
}

DFA_ptr StringAutomaton::PreConcatPrefix(DFA_ptr concat_dfa, DFA_ptr suffix_dfa, int var) {
  return TrimSuffix(concat_dfa,suffix_dfa,var);
}

DFA_ptr StringAutomaton::PreConcatSuffix(DFA_ptr concat_dfa, DFA_ptr prefix_dfa, int var) {
  return TrimPrefix(concat_dfa,prefix_dfa,var);
}

} /* namespace Theory */
} /* namespace Vlab */
