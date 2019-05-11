/*
 * Automaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "Automaton.h"
#include "StringAutomaton.h"

namespace Vlab {
namespace Theory {

const int Automaton::VLOG_LEVEL = 9;

int Automaton::num_misses = 0;
int Automaton::num_hits = 0;
std::chrono::duration<double> Automaton::diff = std::chrono::steady_clock::now() - std::chrono::steady_clock::now();
redox::Redox* Automaton::rdx_ = nullptr;

//std::map<std::pair<std::string,std::string>,DFA> Automaton::stupid_cache;
std::map<std::string,DFA_ptr> Automaton::stupid_cache;

int Automaton::name_counter = 0;
int Automaton::next_state = 0;

unsigned long Automaton::next_id = 0;

std::unordered_map<int, int*> Automaton::bdd_variable_indices;
bool Automaton::count_bound_exact_;

const std::string Automaton::Name::NONE = "none";
const std::string Automaton::Name::BOOL = "BoolAutomaton";
const std::string Automaton::Name::UNARY = "UnaryAutomaton";
const std::string Automaton::Name::INT = "IntAutomaton";
const std::string Automaton::Name::STRING = "StringAutomaton";
const std::string Automaton::Name::BINARYINT = "BinaryIntAutomaton";

Automaton::Automaton(Automaton::Type type)
        : type_(type), is_counter_cached_{false}, dfa_(nullptr), num_of_bdd_variables_(0), id_(Automaton::next_id++) {
}

Automaton::Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables)
        : type_(type), is_counter_cached_{false}, dfa_(dfa), num_of_bdd_variables_(num_of_variables), id_(Automaton::next_id++) { }

Automaton::Automaton(const Automaton& other)
        : type_(other.type_), is_counter_cached_{false}, dfa_(nullptr), num_of_bdd_variables_(other.num_of_bdd_variables_), id_(Automaton::next_id++) {
          if (other.dfa_)
          {
            dfa_ = dfaCopy(other.dfa_);
          }
}

Automaton::~Automaton() {
	if(dfa_ != nullptr) {
		dfaFree(dfa_);
	}
//  DVLOG(VLOG_LEVEL) << "deleted " << " [" << this->id_ << "]";
}

//Automaton_ptr Automaton::clone() const {
//  return new Automaton(*this);
//}

// TODO implement as pure virtual function
std::string Automaton::str() const {
  switch (type_) {
  case Automaton::Type::NONE:
    return Automaton::Name::NONE;
  case Automaton::Type::BOOL:
    return Automaton::Name::BOOL;
  case Automaton::Type::UNARY:
    return Automaton::Name::UNARY;
  case Automaton::Type::INT:
    return Automaton::Name::INT;
  case Automaton::Type::STRING:
    return Automaton::Name::STRING;
  case Automaton::Type::BINARYINT:
    return Automaton::Name::BINARYINT;
  case Automaton::Type::MULTITRACK:
    return "Multi-track";
  default:
    LOG(FATAL)<< "Unknown automaton type!";
    return "";
  }
}

Automaton::Type Automaton::getType() const {
  return type_;
}

unsigned long Automaton::getId() {
  return id_;
}

DFA_ptr Automaton::getDFA() {
  return dfa_;
}

int Automaton::get_number_of_bdd_variables() {
  return num_of_bdd_variables_;
}

bool Automaton::IsEmptyLanguage() const {
  bool result = DFAIsMinimizedEmtpy(this->dfa_);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsEmptyLanguage() " << std::boolalpha << result;
  return result;
}

bool Automaton::IsOnlyAcceptingEmptyInput() const {
  bool result = DFAIsMinimizedOnlyAcceptingEmptyInput(this->dfa_);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsOnlyAcceptingEmptyInput() " << std::boolalpha << result;
  return result;
}

bool Automaton::IsInitialStateAccepting() const {
  return IsAcceptingState(GetInitialState());
}

bool Automaton::IsAcceptingState(const int state_id) const {
  bool result = Automaton::DFAIsAcceptingState(this->dfa_, state_id);
  //DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsAcceptingState(" << state_id << ") " << std::boolalpha << result;
  return result;
}
bool Automaton::IsInitialState(const int state_id) const {
  bool result = Automaton::DFAIsInitialState(this->dfa_, state_id);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsInitialState(" << state_id << ") " << std::boolalpha << result;
  return result;
}

bool Automaton::IsSinkState(const int state_id) const {
  bool result = Automaton::DFAIsSinkState(this->dfa_, state_id);
  //DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsSinkState(" << state_id << ") " << std::boolalpha << result;
  return result;
}

bool Automaton::IsOneStepAway(const int from_state, const int to_state) const {
  bool result = Automaton::DFAIsOneStepAway(this->dfa_, from_state, to_state);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsSinkState(" << from_state << "," << to_state << ") " << std::boolalpha << result;
  return result;
}

bool Automaton::IsEqual(const Automaton_ptr other_automaton) const {
  bool result = Automaton::DFAIsEqual(this->dfa_, other_automaton->dfa_);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsEqual("<< other_automaton->id_ <<  ")" << std::boolalpha << result;
  return result;
}

int Automaton::GetInitialState() const {
  int initial_state = Automaton::DFAGetInitialState(this->dfa_);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->GetInitialState() = " << initial_state;
  return initial_state;
}

int Automaton::GetSinkState() const {
  int sink_state = Automaton::DFAGetSinkState(this->dfa_);
  //DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->GetSinkState() = " << sink_state;
  return sink_state;
}

Automaton_ptr Automaton::Complement() {
  DFA_ptr complement_dfa = Automaton::DFAComplement(this->dfa_);
  Automaton_ptr complement_auto = MakeAutomaton(complement_dfa, this->GetFormula()->Complement(), num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << complement_auto->id_ << " = [" << this->id_ << "]->Complement()";
  return complement_auto;
}

Automaton_ptr Automaton::Union(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}
	DFA_ptr union_dfa = Automaton::DFAUnion(this->dfa_, other_automaton->dfa_);
  Automaton_ptr union_auto = MakeAutomaton(union_dfa, this->GetFormula()->Union(other_automaton->GetFormula()), num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << union_auto->id_ << " = [" << this->id_ << "]->Union(" << other_automaton->id_ << ")";
  return union_auto;
}

Automaton_ptr Automaton::Intersect(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}

  // std::string id1, id2;
  // std::ostringstream stream1, stream2;
  //
  // this->ToDot(stream1, true);
  // id1 = stream1.str();
  // other_automaton->ToDot(stream2, true);
  // id2 = stream2.str();
  //
  // std::pair<std::string,std::string> stupid_key(id1,id2);
  // DFA_ptr intersect_dfa = nullptr;
  // LOG(FATAL) << "HERE";
  // if(stupid_cache.find(stupid_key) != stupid_cache.end()) {
  //   intersect_dfa = dfaCopy(&stupid_cache[stupid_key]);
  //   num_hits++;
  // } else {
  //   intersect_dfa = Automaton::DFAIntersect(this->dfa_, other_automaton->dfa_);
  //   stupid_cache[stupid_key] = *(dfaCopy(intersect_dfa));
  //   num_misses++;
  // }
  auto intersect_dfa = Automaton::DFAIntersect(this->dfa_, other_automaton->dfa_);

  Automaton_ptr intersect_auto =  MakeAutomaton(intersect_dfa, this->GetFormula()->Intersect(other_automaton->GetFormula()), num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << intersect_auto->id_ << " = [" << this->id_ << "]->Intersect(" << other_automaton->id_ << ")";
  return intersect_auto;
}

Automaton_ptr Automaton::Difference(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}
	DFA_ptr difference_dfa = Automaton::DFADifference(this->dfa_, other_automaton->dfa_);
  Automaton_ptr difference_auto = MakeAutomaton(difference_dfa, this->GetFormula()->Intersect(other_automaton->GetFormula()), num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << difference_auto->id_ << " = [" << this->id_ << "]->Difference(" << other_automaton->id_ << ")";
  return difference_auto;
}

Automaton_ptr Automaton::Concat(Automaton_ptr other_automaton) {
  LOG(FATAL) << "Dont use me, broken; use stringautomaton concat method";
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}

	int flag = 0;
	DFA_ptr initial_dfa = nullptr;
	DFA_ptr tmp_dfa;
	DFA_ptr left_dfa = this->dfa_, right_dfa = other_automaton->dfa_;

  if(DFAIsMinimizedEmtpy(left_dfa) or DFAIsMinimizedEmtpy(right_dfa)) {
    LOG(INFO) << "Its true!";
    return MakeAutomaton(DFAMakePhi(num_of_bdd_variables_),this->GetFormula()->clone() ,num_of_bdd_variables_);
  } if (DFAIsMinimizedOnlyAcceptingEmptyInput(left_dfa)) {
		return other_automaton->clone();
	} else if (DFAIsMinimizedOnlyAcceptingEmptyInput(right_dfa)) {
		return this->clone();
	}

	bool left_hand_side_accepts_emtpy_input = DFAIsAcceptingState(left_dfa, left_dfa->s);

//	if (left_hand_side_accepts_emtpy_input) {
//		auto any_input_other_than_empty = Automaton::DFAMakeAcceptingAnyAfterLength(1, num_of_bdd_variables_);
//		if (left_hand_side_accepts_emtpy_input) {
//			left_dfa = DFAIntersect(left_dfa, any_input_other_than_empty);
//		}
//	}

//	LOG(INFO) << "Left num states = " << left_dfa->ns;
//	LOG(INFO) << "Right num states = " << right_dfa->ns;
	for(int i = 0; i < left_dfa->ns; i++)
//	for(int i = left_dfa->ns - 1; i >= 0; i--)
	{

		if(left_dfa->f[i] == 1) {
			next_state = i;
			if(num_of_bdd_variables_ == 0) {
			  LOG(FATAL) << "WAT";
			}
			DFA_ptr d = DFAConcat(left_dfa, other_automaton->dfa_,num_of_bdd_variables_);
			if(initial_dfa == nullptr) {
				initial_dfa = d;
			} else {
				tmp_dfa = DFAUnion(initial_dfa,d);
				dfaFree(initial_dfa);
				dfaFree(d);
				initial_dfa = tmp_dfa;
			}
		}
	}

//	if (left_hand_side_accepts_emtpy_input) {
//		tmp_dfa = initial_dfa;
//		initial_dfa = DFAUnion(tmp_dfa,other_automaton->dfa_);
//		delete tmp_dfa;
//	}

	//DFA_ptr concat_dfa = Automaton::DFAConcat(this->dfa_,other_automaton->dfa_,num_of_bdd_variables_);
	Automaton_ptr concat_auto = MakeAutomaton(initial_dfa,this->GetFormula()->clone() ,num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << concat_auto->id_ << " = [" << this->id_ << "]->concat(" << other_automaton->id_ << ")";
  return concat_auto;
}

bool Automaton::isCyclic() {
  bool result = false;
  std::map<int, bool> is_discovered;
  std::map<int, bool> is_stack_member;
  int sink_state = GetSinkState();
  is_discovered[sink_state] = true; // avoid sink state

  result = isCyclic(this->dfa_->s, is_discovered, is_stack_member);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->isCyclic() ? " << std::boolalpha << result;
  return result;
}

bool Automaton::isInCycle(int state) {
  std::map<int, bool> is_stack_member;
  return isStateReachableFrom(state, state, is_stack_member);
}

bool Automaton::isStateReachableFrom(int search_state, int from_state) {
  std::map<int, bool> is_stack_member;
  return isStateReachableFrom(search_state, from_state, is_stack_member);
}

BigInteger Automaton::Count(const unsigned long bound) {
  if (not is_counter_cached_) {
    SetSymbolicCounter();
  }

  BigInteger result = counter_.Count(bound);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->count(" << bound << ") : " << result;
  return result;
}

SymbolicCounter Automaton::GetSymbolicCounter() {
  if (is_counter_cached_) {
    return counter_;
  }
  SetSymbolicCounter();
  return counter_;
}

/**
 * Counting with matrix exponentiation by successive squaring
 */
BigInteger Automaton::CountByMatrixMultiplication(unsigned long bound) {
  if (not is_counter_cached_) {
    SetSymbolicCounter();
  }

  BigInteger result = counter_.CountbyMatrixMultiplication(bound);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->count(" << bound << ") : " << result;
  return result;
}

BigInteger Automaton::SymbolicCount(int bound, bool count_less_than_or_equal_to_bound) {
  std::stringstream cmd;
  std::string str_result;
  std::string tmp_math_file = Option::Theory::TMP_PATH + "/math_script.m";
  std::ofstream out_file(tmp_math_file.c_str());

  generateMatrixScript(bound, out_file, count_less_than_or_equal_to_bound);
//  generateGFScript(bound, out_file, count_less_than_or_equal_to_bound);
  cmd << "math -script " << tmp_math_file;
  try {
    DVLOG(VLOG_LEVEL) << "run_cmd(`" << cmd.str() << "`)";
    str_result = Util::Cmd::run_cmd(cmd.str());
  } catch (std::string& e) {
    LOG(ERROR) << e;
  }

  return BigInteger (str_result);
}

BigInteger Automaton::SymbolicCount(double bound, bool count_less_than_or_equal_to_bound) {
  return SymbolicCount(static_cast<int>(bound), count_less_than_or_equal_to_bound);
}

std::map<std::string,std::vector<std::string>> Automaton::GetModelsWithinBound(int num_models, int bound) {
	//inspectAuto(false,true);

	if(bound == -1 and num_models == -1) {
		LOG(FATAL) << "both bound and num_models cant be -1";
	} else if(bound == -1) {
		auto counter = GetSymbolicCounter();
		bound = counter.GetMinBound(num_models);
	}

//	LOG(INFO) << "bound : " << bound;
//	LOG(INFO) << "models: " << num_models;

	// compute BFS for unweighted graph (dfa)
	std::queue<int> states_to_process;
	std::vector<int> distances(this->dfa_->ns,INT_MAX);
	std::set<int> final_states;

	std::vector<int> shortest_accepting_path(this->dfa_->ns,INT_MAX);
	for(int start_state = 0; start_state < this->dfa_->ns; start_state++) {
		distances[start_state] = 0;
		states_to_process.push(start_state);

		while(not states_to_process.empty()) {
			int s = states_to_process.front();
			states_to_process.pop();
			// mark final states for later
			if(this->dfa_->f[s] == 1) {
				final_states.insert(s);
			}

			for(auto iter : getNextStates(s)) {
				if(distances[iter] == INT_MAX) {
					states_to_process.push(iter);
					distances[iter] = distances[s] + 1;
				}
			}
		}

		int shortest = INT_MAX;
		for(auto final : final_states) {
			if(distances[final] < shortest) {
				shortest = distances[final];
			}
		}
		shortest_accepting_path[start_state] = shortest;


		distances = std::vector<int>(this->dfa_->ns,INT_MAX);
	}

//	for(int i = 0; i < this->dfa_->ns; i++) {
//		LOG(INFO) << "shortest path for state " << i << " = " << shortest_accepting_path[i];
//	}
//
//	LOG(INFO) << "Done computing shortest paths to final state";

	// assume num_tracks > 1; Otherwise, juse call normal version
	int models_so_far = 0;
	int num_variables = this->num_of_bdd_variables_;

	std::vector<std::pair<int,std::vector<char>>> next_states;

	// cache the process for finding next transitions from a state
	std::vector<std::vector<std::pair<int,std::vector<char>>>> next_states_matrix(this->dfa_->ns);
	for(int i = 0; i < this->dfa_->ns; i++) {
		int current_state = i;
		std::vector<std::pair<int,std::vector<char>>> inner_next_states;
		std::vector<unsigned> nodes;
		std::vector<std::vector<char>> transition_stack;
		std::vector<char> current_transition;
		int sink = GetSinkState();

		unsigned p, l, r, index; // BDD traversal variables
		p = this->dfa_->q[current_state];
		nodes.push_back(p);
		transition_stack.push_back(std::vector<char>());
		while (not nodes.empty()) {
			p = nodes.back();
			nodes.pop_back();
			current_transition = transition_stack.back();
			transition_stack.pop_back();
			LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
			if (index == BDD_LEAF_INDEX) {
				int to_state = l;
				// if to_state is sink state, ignore
				if(to_state == sink) {
					continue;
				}

				while (current_transition.size() < (unsigned) num_of_bdd_variables_) {
					current_transition.push_back('X');
				}
				// put loops first, other states at back
				if(to_state != current_state) {
					next_states_matrix[i].push_back(std::make_pair(to_state, current_transition));
				} else {
					next_states_matrix[i].insert(next_states_matrix[i].begin(),std::make_pair(to_state,current_transition));
				}

			} else {
				while (current_transition.size() < index) {
					unsigned i = current_transition.size();
					current_transition.push_back('X');
				}
				std::vector<char> left = current_transition;
				left.push_back('0');
				std::vector<char> right = current_transition;
				right.push_back('1');
				transition_stack.push_back(right);
				nodes.push_back(r);
				transition_stack.push_back(left);
				nodes.push_back(l);
			}
		}
	}


	int start = this->dfa_->s;
	int sink = GetSinkState();
	bool get_more_models = true;
	std::vector<char> characters;
	std::stack<std::pair<int,std::vector<char>>> models_to_process;
	// since we're not expanding dont-care characters ('X') yet, the models we find are unfinished
	std::set<std::vector<char>> unfinished_models;

	models_to_process.push(std::make_pair(start,characters));

	// BLASTOFF!
	while(not models_to_process.empty() and get_more_models) {
		std::pair<int,std::vector<char>> current_model = models_to_process.top();
		models_to_process.pop();

		int current_state = current_model.first;
		int length = current_model.second.size() / num_variables;

		if(shortest_accepting_path[current_state] + length > bound) {
			continue;
		}

		// check if its final state; if so, record the model
		if(this->dfa_->f[current_state] == 1) {
			if((count_bound_exact_ and length == bound) or (not count_bound_exact_ and length <= bound)) {

				int num_x = 0;
				for(int k = 0; k < current_model.second.size(); k++) {
					if(current_model.second[k] == 'X') {
						num_x++;
					}
				}

				unfinished_models.insert(current_model.second);
				// set finish condition if necessary
				if(num_models != -1 and models_so_far >= num_models) {
					get_more_models = false;
					continue;
				}
			}
		}

		for(auto iter : next_states_matrix[current_state]) {
		// next_state is in first position
			int to_state = iter.first;
			// if the current length + shortest path to final state from to_state + 1 (for transition from current -> to_state)
			// is greater than bound, ignore
			if(to_state == sink || length + shortest_accepting_path[to_state]+1 > bound) {
				continue;
			}

			if(to_state != sink and (length < bound or bound == -1)) {
				std::vector<char> transition = iter.second;

				// transition is in second position
				characters = current_model.second;
				for(int k = 0; k < num_variables; k++) {
					// since tracks are interleaved, track i's characters don't lie in order in the transition we got
					characters.push_back(transition[k]);
				}


				models_to_process.push(std::make_pair(to_state,characters));
			}
		}
	}

	//LOG(INFO) << "Got unfinished";
	std::vector<std::vector<bool>> finished_models;
	for(auto iter : unfinished_models) {
		std::vector<std::vector<bool>> models;
		models.push_back(std::vector<bool>());

		for(int k = 0; k < iter.size(); k++) {

			// if a character is X (dont care), duplicate transition, one for 1, one for 0
			if(iter[k] == 'X') {
				// dont add both transitions for X if we are at the desired number of models
				if(models.size() + finished_models.size() >= num_models) {
					for(int i = 0; i < models.size(); i++) {
						models[i].push_back(0);
					}
				} else {
					std::vector<std::vector<bool>> temp_models;
					for(int i = 0; i < models.size(); i++) {
						// dont add both transitions for X if we are at the desired number of models
						if(models.size() + temp_models.size() + finished_models.size() < num_models) {
							std::vector<bool> m = models[i];
							m.push_back(1);
							temp_models.push_back(m);
						}
						models[i].push_back(0);
					}
					models.insert(models.end(),temp_models.begin(),temp_models.end());
				}
			} else {
				for(int i = 0; i < models.size(); i++) {
					if(iter[k] == '0') {
						models[i].push_back(0);
					} else {
						models[i].push_back(1);
					}
				}
			}
		}

//		for(auto i2 : models) {
//			std::string s;
//			for(int k = 0; k < i2.size(); k++) {
//				if(i2[k]) s+= '1';
//				else s+='0';
//			}
//			LOG(INFO) << s;
//		}
//		std::cin.get();

		finished_models.insert(finished_models.end(),models.begin(),models.end());
	}

	//LOG(INFO) << "Got finished models";

	std::set<std::string> printable_models;
	for(auto iter : finished_models) {
		// quit early if we have enough models
		if(printable_models.size() >= num_models) {
			break;
		}
		std::string model;
		int length = iter.size() / num_variables;
		for(int k = 0; k < length; k++) {
			unsigned char c = 0;

			// var_per_track-1 since we dont' care about the last bit, which is used for lambda
			for(int j = 0; j < num_variables; j++) {
				int index = (k*num_variables + j);
				if(iter[index]) {
					c |= 1;
				} else {
					c |= 0;
				}
				if(j != 7) {
					c <<= 1;
				}
			}

//			char c_arr[4];
//			charToAscii(c_arr,c);
//			model += c_arr;
			model += c;
		}
		printable_models.insert(model);
	}

	auto formula = this->GetFormula();
	if(formula == nullptr) {
		LOG(FATAL) << "Formula not set!";
	}
	auto var_coeffs = formula->GetVariableCoefficientMap();
	std::map<std::string,std::vector<std::string>> variable_values;
	for(auto iter : var_coeffs) {
		variable_values[iter.first] = std::vector<std::string>();
	}

	// should be only 1 track, so should have a variable
	std::string var_name = formula->GetVariableAtIndex(0);

	for(auto iter : printable_models) {
		variable_values[var_name].push_back(iter);
	}

	return variable_values;
}

void Automaton::SetCountBoundExact(bool value) {
	count_bound_exact_ = value;
}

bool Automaton::isCyclic(int state, std::map<int, bool>& is_discovered, std::map<int, bool>& is_stack_member) {
  if (not is_discovered[state]) {
    is_discovered[state] = true;
    is_stack_member[state] = true;
    for (auto next_state : getNextStates(state)) {
      if ((not is_discovered[next_state]) and isCyclic(next_state, is_discovered, is_stack_member)) {
        return true;
      } else if (is_stack_member[next_state]) {
        return true;
      }
    }
  }
  is_stack_member[state] = false;
  return false;
}

bool Automaton::isStateReachableFrom(int search_state, int from_state, std::map<int, bool>& is_stack_member) {
  is_stack_member[from_state] = true;

  for (auto next_state : getNextStates(from_state)) {
    if (next_state == search_state) {
      return true;
    } else if ((not is_stack_member[next_state]) and (not IsSinkState(next_state)) and
      isStateReachableFrom(search_state, next_state, is_stack_member)) {
      return true;
    }
  }

  is_stack_member[from_state] = false;
  return false;
}

/**
 * @returns graph representation of automaton
 */
Graph_ptr Automaton::toGraph() {
  Graph_ptr graph = new Graph();
  GraphNode_ptr node = nullptr, next_node = nullptr;
  for (int s = 0; s < this->dfa_->ns; s++) {
    node = new GraphNode(s);
    if (s == 0) {
      graph->setStartNode(node);
    }

    if (this->IsSinkState(s)) {
      graph->setSinkNode(node);
    } else if (this->IsAcceptingState(s)) {
      graph->addFinalNode(node);
    } else {
      graph->addNode(node);
    }
  }
  node = nullptr;
  for (auto& entry : graph->getNodeMap()) {
    node = entry.second;
    for (int id : getNextStates(node->getID())) {
      next_node = graph->getNode(id);
      node->addNextNode(next_node);
      next_node->addPrevNode(node);
    }
  }

  return graph;
}

/**
 * Assumes automaton is minimized and there is a sink state
 * @returns true if automaton is a singleton
 */
bool Automaton::isAcceptingSingleWord() {
  unsigned p, l, r, index; // BDD traversal variables
  std::map<unsigned, unsigned> next_states;
  std::vector<unsigned> nodes;
  std::vector<int> bit_stack;
  unsigned sink_state = (unsigned) this->GetSinkState();
  bool is_accepting_single_word = true;
  bool is_final_state = false;
  int bit_counter = 0;

  for (int s = 0; s < this->dfa_->ns; s++) {
    is_final_state = IsAcceptingState(s);
    p = this->dfa_->q[s];
    nodes.push_back(p);
    bit_stack.push_back(0);
    while (not nodes.empty()) {
      p = nodes.back();
      nodes.pop_back();
      bit_counter = bit_stack.back();
      bit_stack.pop_back();
      LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
      if (index == BDD_LEAF_INDEX) {
        if (sink_state != l) {
          next_states[l]++;
          if (bit_counter != num_of_bdd_variables_ or (next_states[l] > 1) or (next_states.size() > 1) or is_final_state) {
            is_accepting_single_word = false;
            break;
          }
        }
      } else {

        bit_stack.push_back(bit_counter + 1);
        nodes.push_back(l);
        bit_stack.push_back(bit_counter + 1);
        nodes.push_back(r);
      }
    }

    nodes.clear();
    bit_stack.clear();
    next_states.clear();
    is_final_state = false;
    p = l = r = index = -1;
    if (not is_accepting_single_word) {
      break;
    }
  }

  return is_accepting_single_word;
}

std::vector<bool>* Automaton::getAnAcceptingWord(std::function<bool(unsigned& index)> next_node_heuristic) {
  int sink_state = GetSinkState();
  NextState start_state = std::make_pair(this->dfa_->s, std::vector<bool>());
  std::vector<bool>* bit_vector = new std::vector<bool>();
  std::map<int, bool> is_stack_member;
  is_stack_member[sink_state] = true;

  if (getAnAcceptingWord(start_state, is_stack_member, *bit_vector, next_node_heuristic)) {
    return bit_vector;
  }

  return nullptr;
}

std::vector<bool>* Automaton::getAnAcceptingWordRandom(std::function<bool(unsigned& index)> next_node_heuristic) {

  //LOG(INFO) << "----------BEGIN Automaton::getAnAcceptingWordRandom-----------";

	int sink_state = GetSinkState();
	//LOG(INFO) << "sink_state = " << sink_state;
	NextState state = std::make_pair(this->dfa_->s, std::vector<bool>());
	std::vector<bool>* path = new std::vector<bool>();

	int k = 0;
	double r = 1.25;
	double thresh = 0.15;
	std::mt19937 rng;
	rng.seed(std::random_device()());
	std::uniform_real_distribution<double> dist(0.0,1.0);

	int t = 0;
	while(true) {
	  //LOG(INFO) << "begin while loop iteration";
		auto states = getNextStatesOrdered(state.first, next_node_heuristic);

		// if accepting state, determine whether to stop or continue.
		// if accepting state, only go on if there are more states to visit besides sink state
		if(this->IsAcceptingState(state.first)) {
			double x = dist(rng);
			if(x < thresh || (states.size() == 1 and states[0].first == sink_state)) {
				// stop here, report solution
				break;
			} else {
				// keep going, but increase probability we will stop in the future
				thresh *= r;
			}
		}
    //LOG(INFO) << "get k";
    std::uniform_int_distribution<int> dist2(0,states.size()-1);
		do {
			k = dist2(rng);
		  //LOG(INFO) << "  k = " << k;
		} while(states[k].first == sink_state);
		state = states[k];
		path->insert(path->end(),state.second.begin(),state.second.end());
	  //LOG(INFO) << "end while loop iteration";
	}

  //LOG(INFO) << "Got random!";
	return path;
}

std::vector<char> Automaton::decodeException(std::vector<char>& exception) {
  std::vector<char> decoded_exceptions_in_ascii;
  std::vector<char> tmp_holder;
  decoded_exceptions_in_ascii.push_back(0);

  for (auto ch : exception) {
    for (auto& decoded_ch : decoded_exceptions_in_ascii) {
      decoded_ch <<= 1; // by default it shifts by one and adds zero
      if (ch == '1') {
        decoded_ch |= 1;
      } else if (ch == 'X') {
        tmp_holder.push_back(decoded_ch); // ending with zero handled by shift
        decoded_ch |= 1;
      } // else ch == '0' is handled by initial shift
    }
    decoded_exceptions_in_ascii.insert(decoded_exceptions_in_ascii.end(), tmp_holder.begin(), tmp_holder.end());
    tmp_holder.clear();
  }
  return decoded_exceptions_in_ascii;
}

bool Automaton::getAnAcceptingWord(NextState& state, std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::function<bool(unsigned& index)> next_node_heuristic) {
  is_stack_member[state.first] = true;
  path.insert(path.end(), state.second.begin(), state.second.end());


  if (this->IsAcceptingState(state.first)) {
    return true;
  }


  for (auto& next_state : getNextStatesOrdered(state.first, next_node_heuristic)) {
    if (not is_stack_member[next_state.first]) {
      if (getAnAcceptingWord(next_state, is_stack_member, path, next_node_heuristic)) {
        return true;
      }
    }
  }

  path.erase(path.end() - state.second.size(), path.end());
  is_stack_member[state.first] = false;
  return false;
}

char* Automaton::getAnExample(bool accepting) {
  return dfaMakeExample(this->dfa_, 1, num_of_bdd_variables_, (unsigned*)GetBddVariableIndices(num_of_bdd_variables_));
}

std::ostream& operator<<(std::ostream& os, const Automaton& automaton) {
  return os << automaton.str();
}

void Automaton::CleanUp() {
  LOG(INFO) << "num_hits    = " << num_hits;
  LOG(INFO) << "num_misses  = " << num_misses;
  LOG(INFO) << "hit ratio   = " << (double)num_hits / (double)(num_misses+num_hits);
  LOG(INFO) << "ChangeMapIndices time = " << std::chrono::duration <long double, std::milli> (diff).count() << " ms";

	for(auto &it : bdd_variable_indices) {
		delete[] it.second;
		it.second = nullptr;
	}
	bdd_variable_indices.clear();
}

bool Automaton::DFAIsMinimizedEmtpy(const DFA_ptr minimized_dfa) {
    return (minimized_dfa->ns == 1 && minimized_dfa->f[minimized_dfa->s] != 1)? true : false;
}

// TODO implement general is empty function
bool Automaton::DFAIsEmpty(const DFA_ptr dfa) {
  //bool result = true;
  for (int s = 0; s < dfa->ns; ++s) {
    if (DFAIsAcceptingState(dfa, s)) {
      return false;
      // check if the accepting state is reachable
//      LOG(FATAL) << "Not implemented";
    }
  }
  return true;
  //return result;
}

bool Automaton::DFAIsMinimizedOnlyAcceptingEmptyInput(const DFA_ptr minimized_dfa) {
  if (not Automaton::DFAIsAcceptingState(minimized_dfa, minimized_dfa->s)) {
    return false;
  }
  for (int s = 0; s < minimized_dfa->ns; s++) {
    if (Automaton::DFAIsAcceptingState(minimized_dfa, s) and s != minimized_dfa->s) {
      return false;
    } else if (DFAIsOneStepAway(minimized_dfa, s, minimized_dfa->s)) { // if initial state is reachable in a minimized auto, there is a loop
      return false;
    }
  }
  return true;
}

bool Automaton::DFAIsAcceptingState(const DFA_ptr dfa, const int state_id) {
  return (dfa->f[state_id] == 1);
}

bool Automaton::DFAIsInitialState(const DFA_ptr dfa, const int state_id) {
  return (state_id == dfa->s);
}

bool Automaton::DFAIsSinkState(const DFA_ptr dfa, const int state_id) {
  return (bdd_is_leaf(dfa->bddm, dfa->q[state_id])
            and (bdd_leaf_value(dfa->bddm, dfa->q[state_id]) == (unsigned) state_id)
            and dfa->f[state_id] == -1);
}

bool Automaton::DFAIsOneStepAway(const DFA_ptr dfa, const int from_state, const int to_state) {
  unsigned p, l, r, index; // BDD traversal variables
  std::stack<unsigned> nodes;

  p = dfa->q[from_state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top();
    nodes.pop();
    LOAD_lri(&dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      if (l == (unsigned) to_state) {
        return true;
      }
    } else {
      nodes.push(l);
      nodes.push(r);
    }
  }
  return false;
}

bool Automaton::DFAIsEqual(const DFA_ptr dfa1, const DFA_ptr dfa2) {
  DFA_ptr impl_1 = dfaProduct(dfa1, dfa2, dfaIMPL);
  DFA_ptr impl_2 = dfaProduct(dfa2, dfa1, dfaIMPL);
  DFA_ptr result_dfa = dfaProduct(impl_1,impl_2,dfaAND);
  dfaFree(impl_1);
  dfaFree(impl_2);
  dfaNegation(result_dfa);
  DFA_ptr minimized_dfa = dfaMinimize(result_dfa);
  dfaFree(result_dfa);
  bool result = DFAIsMinimizedEmtpy(minimized_dfa);
  dfaFree(minimized_dfa);
  return result;
}

int Automaton::DFAGetInitialState(const DFA_ptr dfa) {
  return dfa->s;
}

int Automaton::DFAGetSinkState(const DFA_ptr dfa) {
  for (int s = 0; s < dfa->ns; ++s) {
    if (Automaton::DFAIsSinkState(dfa, s)) {
      return s;
    }
  }
  return -1;
}

DFA_ptr Automaton::DFAMakePhi(const int number_of_bdd_variables) {
  char statuses[1] {'-'};
  dfaSetup(1, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));
  dfaAllocExceptions(0);
  dfaStoreState(0);
  return dfaBuild(statuses);
}

/**
 *
 * @returns a dfa that accepts any input including an accepting initial state
 */
DFA_ptr Automaton::DFAMakeAny(const int number_of_bdd_variables) {
  char statuses[1] {'+'};
  dfaSetup(1, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));
  dfaAllocExceptions(0);
  dfaStoreState(0);
  return dfaBuild(statuses);
}

/**
 *
 * @returns a dfa that accepts any input except initial state is not accepting
 */
DFA_ptr Automaton::DFAMakeAnyButNotEmpty(const int number_of_bdd_variables) {
  char statuses[2] { '-', '+' };
  dfaSetup(2, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));
  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  return dfaBuild(statuses);
}

DFA_ptr Automaton::DFAMakeEmpty(const int number_of_bdd_variables) {
  char statuses[2] { '+', '-' };
  dfaSetup(2, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));
  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  return dfaBuild(statuses);
}

DFA_ptr Automaton::DFAComplement(const DFA_ptr dfa) {
  DFA_ptr complement_dfa = dfaCopy(dfa);
  dfaNegation(complement_dfa);
  return complement_dfa;
}

DFA_ptr Automaton::DFAUnion(const DFA_ptr dfa1, const DFA_ptr dfa2) {
  DFA_ptr union_dfa = dfaProduct(dfa1, dfa2, dfaOR);
  DFA_ptr minimized_dfa = dfaMinimize(union_dfa);
  dfaFree(union_dfa);
  return minimized_dfa;
}

DFA_ptr Automaton::DFAIntersect(const DFA_ptr dfa1, const DFA_ptr dfa2) {

  // std::string id1, id2;
  //
  // std::stringstream os1;
  // {
  //   cereal::BinaryOutputArchive ar(os1);
  //   Util::Serialize::save(ar,dfa1);
  // }
  // id1 = os1.str();
  //
  // std::stringstream os2;
  // {
  //   cereal::BinaryOutputArchive ar(os2);
  //   Util::Serialize::save(ar,dfa2);
  // }
  // id2 = os2.str();
  //
  //
  //
  // std::string stupid_key1 = id1 + id2;
  // std::string stupid_key2 = id2 + id1;
  // DFA_ptr intersect_dfa = nullptr, minimized_dfa = nullptr;
  // // LOG(FATAL) << "HERE";
  // if(stupid_cache.find(stupid_key1) != stupid_cache.end()) {
  //   std::stringstream is(stupid_cache[stupid_key1]);
  //   {
  //     cereal::BinaryInputArchive ar(is);
  //     Util::Serialize::load(ar,intersect_dfa);
  //   }
  //   minimized_dfa = dfaMinimize(intersect_dfa);
  //   dfaFree(intersect_dfa);
  //   num_hits++;
  // } else if (stupid_cache.find(stupid_key2) != stupid_cache.end()) {
  //   std::stringstream is(stupid_cache[stupid_key2]);
  //   {
  //     cereal::BinaryInputArchive ar(is);
  //     Util::Serialize::load(ar,intersect_dfa);
  //   }
  //   minimized_dfa = dfaMinimize(intersect_dfa);
  //   dfaFree(intersect_dfa);
  //   num_hits++;
  // } else {
  //   intersect_dfa = dfaProduct(dfa1, dfa2, dfaAND);
  //   minimized_dfa = dfaMinimize(intersect_dfa);
  //   dfaFree(intersect_dfa);
  //   intersect_dfa = minimized_dfa;
  //
  //   std::stringstream os;
  //   {
  //     cereal::BinaryOutputArchive ar(os);
  //     Util::Serialize::save(ar,intersect_dfa);
  //   }
  //   stupid_cache[stupid_key1] = os.str();
  //   // stupid_cache[stupid_key2] = os.str();
  //   num_misses++;
  // }

  DFA_ptr intersect_dfa = dfaProduct(dfa1, dfa2, dfaAND);
  DFA_ptr minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
  return minimized_dfa;
}

DFA_ptr Automaton::DFADifference(const DFA_ptr dfa1, DFA_ptr dfa2) {
  dfaNegation(dfa2); // efficient
  DFA_ptr difference_dfa = Automaton::DFAIntersect(dfa1, dfa2);
  dfaNegation(dfa2); // restore back
  return difference_dfa;
}

DFA_ptr Automaton::DFAProjectAway(const DFA_ptr dfa, const int index) {
  DFA_ptr projected_dfa = dfaProject(dfa, (unsigned)index);
  DFA_ptr minimized_dfa = dfaMinimize(projected_dfa);
  dfaFree(projected_dfa);
  return minimized_dfa;
}

DFA_ptr Automaton::DFAProjectAway(const DFA_ptr dfa, std::vector<int> map, const std::vector<int> indices) {
	DFA_ptr temp,result_dfa = dfa;
	int flag = 0;

	for(auto index : indices) {
		temp = dfaProject(result_dfa,(unsigned)index);
		if(flag)
			dfaFree(result_dfa);
		result_dfa = dfaMinimize(temp);
		flag = 1;
		dfaFree(temp);
	}
	dfaReplaceIndices(result_dfa,&map[0]);
	return result_dfa;
}

DFA_ptr Automaton::DFAProjectAwayAndReMap(const DFA_ptr dfa, const int number_of_bdd_variables, const int index) {
  DFA_ptr projected_dfa = dfaProject(dfa, (unsigned)index);
  if (index < (unsigned)(number_of_bdd_variables - 1)) {
    int* indices_map = new int[number_of_bdd_variables];
    for (int i = 0, j = 0; i < number_of_bdd_variables; i++) {
      if ((unsigned)i != index) {
        indices_map[i] = j;
        j++;
      }
    }
    dfaReplaceIndices(projected_dfa, indices_map);
    delete[] indices_map;
  }

  DFA_ptr minimized_dfa = dfaMinimize(projected_dfa);
  dfaFree(projected_dfa);
  return minimized_dfa;
}

DFA_ptr Automaton::DFAProjectTo(const DFA_ptr dfa, const int number_of_bdd_variables, const int index) {
  DFA_ptr projected_dfa = dfaCopy(dfa);
  for (int i = 0 ; i < number_of_bdd_variables; ++i) {
    if (i != index) {
      DFA_ptr tmp_dfa = projected_dfa;
      projected_dfa = Automaton::DFAProjectAway(tmp_dfa, i);
      dfaFree(tmp_dfa);
    }
  }

  int* indices_map = CreateBddVariableIndices(number_of_bdd_variables);
  indices_map[index] = 0;
  indices_map[0] = index;
  dfaReplaceIndices(projected_dfa, indices_map);
  delete[] indices_map;
  return projected_dfa;
}

DFA_ptr Automaton::DFAMakeAcceptingAnyWithInRange(const int start, const int end, const int number_of_bdd_variables) {
  CHECK((start >= 0) && (end >= start));
  // 1 initial state and 1 sink state
  const int number_of_states = end + 2;
  char *statuses = new char[number_of_states+1];
  dfaSetup(number_of_states, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));

  // 0 to start - 1 not accepting, start to end accepting states
  for(int i = 0; i <= end; ++i) {
    dfaAllocExceptions(0);
    dfaStoreState(i + 1);
    if(i >= start) {
      statuses[i] = '+';
    } else {
      statuses[i] = '-';
    }
  }

  //the sink state
  dfaAllocExceptions(0);
  dfaStoreState(number_of_states - 1);  // sink state
  statuses[number_of_states - 1] = '-';
  statuses[number_of_states] = '\0';

  DFA_ptr result_dfa = dfaBuild(statuses);
  delete[] statuses;
  return result_dfa;
}

DFA_ptr Automaton::DFAMakeAcceptingAnyAfterLength(const int length, const int number_of_bdd_variables) {
  CHECK(length >= 0);
  // 1 initial state
  const int number_of_states = length + 1;
  char *statuses = new char[number_of_states+1];
  dfaSetup(number_of_states, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));

  // 0 to length - 1 not accepting
  for(int i = 0; i < length; ++i) {
    dfaAllocExceptions(0);
    dfaStoreState(i + 1);
    statuses[i] = '-';
  }

  // final state
  dfaAllocExceptions(0);
  dfaStoreState(length);
  statuses[length] = '+';
  statuses[number_of_states] = '\0';
  DFA_ptr result_dfa = dfaBuild(statuses);
  delete[] statuses;
  return result_dfa;
}

std::set<std::string> Automaton::DFAGetTransitionsFromTo(DFA_ptr dfa, const int from, const int to, const int number_of_bdd_variables) {
  const int* bdd_indices = GetBddVariableIndices(number_of_bdd_variables);
  std::set<std::string> transitions;
  paths pp = make_paths(dfa->bddm, dfa->q[from]);
  while (pp) {
    if (pp->to == to) {
      std::string current_exception;
      for (int j = 0; j < number_of_bdd_variables; ++j) {
        trace_descr tp = nullptr;
        for (tp = pp->trace; tp && (tp->index != (unsigned)bdd_indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            current_exception.push_back('1');
          } else {
            current_exception.push_back('0');
          }
        } else {
          current_exception.push_back('X');
        }
      }
      current_exception.push_back('\0');
      transitions.insert(current_exception);
    }
    pp = pp->next;
  }
  return transitions;
}

DFA_ptr Automaton::DFAReverse(const DFA_ptr dfa, int number_of_bdd_variables) {

  LOG(FATAL) << "Not yet ready; see will";

  bool has_sink = true;
  int num_states = dfa->ns;
  int sink = DFAGetSinkState(dfa);

  if(sink < 0) {
    LOG(INFO) << "No sink";
    has_sink = false;
    sink = num_states++;
  }


  int *indices = GetBddVariableIndices(number_of_bdd_variables);

  paths state_paths = nullptr, pp = nullptr;
	trace_descr tp = nullptr;

  int num_duplicates = 0;
  int final_state = num_states++;
  int start_state = dfa->s;

  std::vector<std::map<std::string, std::set<int>>> exceptions(num_states);
  char* statuses = new char[num_states+1];

//  for(int i = 0; i < dfa->ns; i++) {
//    if(dfa->f[i] == 1) {
//      final_state = i;
//      break;
//    }
//  }


  std::vector<std::map<std::string,int>> new_exeps(dfa->ns);
  for(int i = 0; i < dfa->ns; i++) {
    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
		while (pp) {
		  if(pp->to != sink) {
		    std::string current_exception = "";
        for (int j = 0; j < number_of_bdd_variables; j++) {
          for (tp = pp->trace; tp && (tp->index != (unsigned) indices[j]); tp = tp->next);
          if (tp) {
            if (tp->value) {
              current_exception.push_back('1');
            } else {
              current_exception.push_back('0');
            }
          } else {
            current_exception.push_back('X');
          }
        }

        if(dfa->f[pp->to] == 1) {
          current_exception.push_back('1');
          new_exeps[i][current_exception] = final_state;
          current_exception.pop_back();
        }
        current_exception.push_back('0');
        new_exeps[i][current_exception] = pp->to;
		  }
		  tp = nullptr;
		  pp = pp->next;
		}
    kill_paths(state_paths);
		state_paths = pp = nullptr;
  }

LOG(INFO) << "Second loop";

  for(int i = 0; i < dfa->ns; i++) {
    int to_state, from_state;
    for(auto exep_iter : new_exeps[i]) {
      if(exep_iter.second == final_state) {
        from_state = 0;
      } else if(exep_iter.second == start_state) {
        from_state = final_state;
      } else {
        from_state = exep_iter.second;
      }

      if(i == final_state) {
        to_state = start_state;
      } else if(i == start_state) {
        to_state = final_state;
      } else {
        to_state = i;
      }

      std::set<std::string> expanded_exeps = Automaton::ExpandTransition(exep_iter.first);

      for(auto set_iter : expanded_exeps) {
        exceptions[from_state][set_iter].insert(to_state);
        if (exceptions[from_state][set_iter].size() > num_duplicates) {
          num_duplicates = exceptions[from_state][set_iter].size();
        }
      }
    }
  }

//  for (int i = 0; i < dfa->ns; i++) {
//		state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
//		while (pp) {
//      if (pp->to != sink) {
//        std::string current_exception = "";
//        for (int j = 0; j < number_of_bdd_variables; j++) {
//          for (tp = pp->trace; tp && (tp->index != (unsigned) indices[j]); tp = tp->next);
//          if (tp) {
//            if (tp->value) {
//              current_exception.push_back('1');
//            } else {
//              current_exception.push_back('0');
//            }
//          } else {
//            current_exception.push_back('X');
//          }
//        }
//
////        if(i == pp->to) {
////        	current_exception.push_back('1');
////        } else {
////        	current_exception.push_back('0');
////        }
////        current_exception.push_back('\0');
//
//
//
//
//        int to_state, from_state;
//
//        if(dfa->f[pp->to] == 1) {
//          from_state = 0;
//        } else if(pp->to == start_state) {
//          from_state = final_state;
//        } else {
//          from_state = pp->to;
//        }
//
//        if(i == final_state) {
//          to_state = start_state;
//        } else if(i == start_state) {
//          to_state = final_state;
//        } else {
//          to_state = i;
//        }
//
//        std::set<std::string> expanded_exeps = Automaton::ExpandTransition(current_exception);
//
//        for(auto set_iter : expanded_exeps) {
//          exceptions[from_state][set_iter].insert(to_state);
//          if (exceptions[from_state][set_iter].size() > num_duplicates) {
//            num_duplicates = exceptions[from_state][set_iter].size();
//          }
//        }
//        tp = nullptr;
//      }
//      pp = pp->next;
//    }
//
//    kill_paths(state_paths);
//		state_paths = pp = nullptr;
//  }

  number_of_bdd_variables+=1;

  int num_extrabits = std::ceil(std::log2(num_duplicates));
  LOG(INFO) << "Num duplicates = " << num_duplicates;
  LOG(INFO) << "num extrabits  = " << num_extrabits;
  int temp_num_bdd_variables = number_of_bdd_variables+num_extrabits;
  int *reverse_indices = GetBddVariableIndices(temp_num_bdd_variables);

	dfaSetup(num_states, temp_num_bdd_variables, reverse_indices);
  for(int i = 0; i < num_states; i++) {

    if(not has_sink and i == sink) {
      dfaAllocExceptions(0);
      dfaStoreState(sink);
      statuses[sink] = '-';
      continue;
    }

    // each entry in exceptions[i] corresponds to (exception,set<int>)
    // allocate proper extrabits for each exception (due to nondeterminism)
    std::map<std::string,int> current_exceptions;
    for (auto entry : exceptions[i]) {
      // entry.first is the exception/path/character
      int current_number = 0;
      for(auto set_iter : entry.second) {
        std::string number_as_binary_string = Automaton::GetBinaryStringMSB(current_number++, num_extrabits);
        std::string exep = entry.first + number_as_binary_string;
        exep.push_back('\0');
        current_exceptions[exep] = set_iter;
        if(set_iter >= num_states) {
        }
//        LOG(INFO) << exep << " -> " << set_iter;
      }
    }
//    LOG(INFO) << "";

    dfaAllocExceptions(current_exceptions.size());
    for(auto entry : current_exceptions) {
      dfaStoreException(entry.second, const_cast<char *>(entry.first.data()));
    }
    dfaStoreState(sink);

    if(i == final_state) {
      statuses[i] = '+';
    } else {
      statuses[i] = '-';
    }

  }

//	if(not has_sink) {
//	  dfaAllocExceptions(0);
//	  dfaStoreState(sink);
//	  statuses[sink] = '-';
//	}



	statuses[num_states] = '\0';
	DFA_ptr temp_dfa = dfaBuild(statuses);

//	return temp_dfa;
	DFA_ptr reverse_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);

	for(int i = temp_num_bdd_variables-1; i >= number_of_bdd_variables; i--) {
    temp_dfa = dfaProject(reverse_dfa, i);
    dfaFree(reverse_dfa);
    reverse_dfa = dfaMinimize(temp_dfa);
    dfaFree(temp_dfa);
  }
	delete[] statuses;
	return reverse_dfa;
}

DFA_ptr Automaton::DFAConcat(const DFA_ptr dfa1, const DFA_ptr dfa2, const int number_of_bdd_variables) {
  //LOG(FATAL) << "I'm broken, fix me! Use StringAutomaton::concat instead";


	if (DFAIsMinimizedEmtpy(dfa1) or DFAIsMinimizedEmtpy(dfa2)) {
		return DFAMakeEmpty(number_of_bdd_variables);
	} else if (DFAIsMinimizedOnlyAcceptingEmptyInput(dfa1)) {
		return dfaCopy(dfa2);
	} else if (DFAIsMinimizedOnlyAcceptingEmptyInput(dfa2)) {
		return dfaCopy(dfa1);
	}



	// TODO refactor handling empty string case
	bool left_hand_side_accepts_emtpy_input = false;//DFAIsAcceptingState(dfa1, dfa1->s);
	bool right_hand_side_accepts_empty_input = false;//DFAIsAcceptingState(dfa2, dfa2->s);
	DFA_ptr left_dfa = dfa1, right_dfa = dfa2;

	if (left_hand_side_accepts_emtpy_input or right_hand_side_accepts_empty_input) {
		auto any_input_other_than_empty = Automaton::DFAMakeAcceptingAnyAfterLength(1, number_of_bdd_variables);
		if (left_hand_side_accepts_emtpy_input) {
			left_dfa = DFAIntersect(dfa1, any_input_other_than_empty);
		}


		if (right_hand_side_accepts_empty_input) {
			right_dfa = DFAIntersect(dfa2, any_input_other_than_empty);
		}
		dfaFree(any_input_other_than_empty);
	}

	int* indices = GetBddVariableIndices(number_of_bdd_variables);
	int tmp_num_of_variables,
			state_id_shift_amount,
			expected_num_of_states,
			sink_state_left_auto,
			sink_state_right_auto,
			to_state = 0,
			loc,
			i = 0,
			j = 0;

	bool is_start_state_reachable = false;
	paths state_paths = nullptr, pp = nullptr;
	trace_descr tp = nullptr;

	std::map<std::string, int> exceptions_left_auto;
	std::map<std::string, int> exceptions_right_auto;
	std::map<std::string, int> exceptions_fix;
	std::map<std::string, int> disconnected_exceptions_fix;
	char* statuses = nullptr;
	tmp_num_of_variables = number_of_bdd_variables;
	//int both_extrabit = tmp_num_of_variables++;
	int suffix_extrabit_0 = tmp_num_of_variables++;
	//tmp_num_of_variables = number_of_bdd_variables + 1; // add one extra bit


	state_id_shift_amount = left_dfa->ns-1;
  expected_num_of_states = left_dfa->ns + right_dfa->ns - 1;
//	expected_num_of_states = left_dfa->ns + right_dfa->ns;
//	is_start_state_reachable = TEMPisStartStateReachableFromAnAcceptingState(right_dfa);
//	if (not is_start_state_reachable) {
//		expected_num_of_states = expected_num_of_states  - 1; // if start state is reachable from an accepting state, it will be merge with accepting states of left hand side
//	}
	// variable initializations
	sink_state_left_auto = DFAGetSinkState(left_dfa);
	sink_state_right_auto = DFAGetSinkState(right_dfa);
	bool left_sink = true, right_sink = true;
	int sink = sink_state_left_auto;

	if(sink_state_left_auto < 0 && sink_state_right_auto < 0) {
		left_sink = right_sink = false;
		sink = expected_num_of_states;
		expected_num_of_states++;
	} else if(sink_state_left_auto < 0) {
		left_sink = false;
		sink = sink_state_right_auto + state_id_shift_amount;
//		if(not is_start_state_reachable) {
//			sink--;
//		}
	} else if(sink_state_right_auto < 0) {
		right_sink = false;
	} else {
		expected_num_of_states--;
	}
	statuses = new char[expected_num_of_states + 1];
	int* concat_indices = GetBddVariableIndices(tmp_num_of_variables);

	dfaSetup(expected_num_of_states, tmp_num_of_variables, concat_indices); //sink states are merged
	state_paths = pp = make_paths(right_dfa->bddm, right_dfa->q[right_dfa->s]);
	while (pp) {
		if (!right_sink || pp->to != sink_state_right_auto ) {


		  if(pp->to == 0) {
		    to_state = next_state;
		  } else {
		    to_state = pp->to + state_id_shift_amount;
			  if (left_sink && right_sink && pp->to > (unsigned)sink_state_right_auto ) {
			    to_state--;
			  }
		  }


			// if there is a self loop keep it
//			if (pp->to == (unsigned)right_dfa->s ) {
//				//to_state -= 2;
//				to_state = next_state;
//			} else {
//				if (left_sink && right_sink && pp->to > (unsigned)sink_state_right_auto ) {
//					to_state--; //to new state, sink state will be eliminated and hence need -1
//				}
//				if ((not is_start_state_reachable) && pp->to > (unsigned)right_dfa->s) {
//					to_state--; // to new state, init state will be eliminated if init is not reachable
//				}
//			}

			std::string current_exception = "";
			for (j = 0; j < number_of_bdd_variables; j++) {
				//the following for loop can be avoided if the indices are in order
				for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
				if (tp) {
					if (tp->value) {
						current_exception.push_back('1');
					}
					else {
						current_exception.push_back('0');
					}
				}
				else {
					current_exception.push_back('X');
				}
			}

      current_exception.push_back('1');

			//current_exception.push_back('1'); // new path
			current_exception.push_back('\0');
			exceptions_right_auto[current_exception] = to_state;
		}
		tp = nullptr;
		pp = pp->next;
	}

	kill_paths(state_paths);
	state_paths = pp = nullptr;
	for (i = 0; i < left_dfa->ns; i++) {
		state_paths = pp = make_paths(left_dfa->bddm, left_dfa->q[i]);
		while (pp) {
			if (left_sink && pp->to == (unsigned)sink_state_left_auto) {
				pp = pp->next;
				continue;
			}
			to_state = pp->to;
			std::string current_exception = "";
			for (j = 0; j < number_of_bdd_variables; j++) {
				for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
				if (tp) {
					if (tp->value) {
						current_exception.push_back('1');
					} else {
						current_exception.push_back('0');
					}
				} else {
					current_exception.push_back('X');
				}
			}

      current_exception.push_back('0');
			//current_exception.push_back('0'); // add extra bit, '0' is used for the exceptions coming from left auto
			current_exception.push_back('\0');
			exceptions_left_auto[current_exception] = to_state;
			tp = nullptr;
			pp = pp->next;
		}
		// generate concat automaton

		if (DFAIsAcceptingState(left_dfa,i) && next_state == i) {
			dfaAllocExceptions(exceptions_left_auto.size() + exceptions_right_auto.size());
			for (auto entry : exceptions_left_auto) {
				dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
			}

			for (auto entry : exceptions_right_auto) {
				dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
			}
			exceptions_right_auto.clear();

			dfaStoreState(sink);
			if (DFAIsAcceptingState(right_dfa,0)) {
				statuses[i]='+';
			}
			else {
				statuses[i]='-';
			}
		} else {
			dfaAllocExceptions(exceptions_left_auto.size());
			for (auto entry : exceptions_left_auto) {
				dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
			}
			dfaStoreState(sink);
			statuses[i] = '-';
		}
		exceptions_left_auto.clear();

		kill_paths(state_paths);
		state_paths = pp = nullptr;
	}



	//  initflag is 1 iff init is reached by some state. In this case,
	for (i = 0; i < (right_dfa->ns); i++) {
		if (i != sink_state_right_auto ) {
			if ( i != right_dfa->s) {
//			if ( i != right_dfa->s || is_start_state_reachable) {
				state_paths = pp = make_paths(right_dfa->bddm, right_dfa->q[i]);
				while (pp) {
					if (!right_sink || pp->to != (unsigned)sink_state_right_auto) {

					  if(pp->to == 0) {
					    to_state = next_state;
					  } else {
					    to_state = pp->to + state_id_shift_amount;
					    if ( right_sink && left_sink && pp->to > (unsigned)sink_state_right_auto) {
                to_state--; //to new state, sink state will be eliminated and hence need -1
              }
					  }

//						to_state = pp->to + state_id_shift_amount;
//						if ( right_sink && left_sink && pp->to > (unsigned)sink_state_right_auto) {
//							to_state--; //to new state, sink state will be eliminated and hence need -1
//						}
//
//						if ( (not is_start_state_reachable) && pp->to > (unsigned)right_dfa->s) {
//							to_state--; // to new state, init state will be eliminated if init is not reachable
//						}

						std::string current_exception = "";
						for (j = 0; j < number_of_bdd_variables; j++) {
							for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp =tp->next);
							if (tp) {
								if (tp->value){
									current_exception.push_back('1');
								}
								else {
									current_exception.push_back('0');
								}
							}
							else {
								current_exception.push_back('X');
							}
						}

						//current_exception.push_back('0'); // old value
						current_exception.push_back('\0');

            exceptions_fix[current_exception] = to_state;

						tp = nullptr;
					}
					pp = pp->next;
				}

				dfaAllocExceptions(exceptions_fix.size());
				for (auto entry : exceptions_fix) {
					dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
				}



				loc = state_id_shift_amount + i;
//				if ( (not is_start_state_reachable) && i > right_dfa->s) {
//					loc--;
//				}
				if (left_sink && right_sink && i > sink_state_right_auto) {
					loc--;
				}

				//if(TEST and i == right_dfa->ns-1) {
          //dfaStoreState(loc);
        //} else {
          dfaStoreState(sink);
        //}
				if (DFAIsAcceptingState(right_dfa,i)) {
					statuses[loc]='+';
				} else {
					statuses[loc]='-';
				}

				kill_paths(state_paths);
				state_paths = pp = nullptr;
			}
		} else if(!left_sink && right_sink) {
			dfaAllocExceptions(0);
			dfaStoreState(sink);
			statuses[sink] = '-';
		}
		exceptions_fix.clear();
	}
	if(!right_sink && !left_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuses[sink] = '-';
	}

//  LOG(INFO) << 1;

	statuses[expected_num_of_states]='\0';
	DFA_ptr concat_dfa = dfaMinimize(dfaBuild(statuses));
	delete[] statuses; statuses = nullptr;
//  LOG(INFO) << 2;
//	DFA_ptr tmp_dfa = dfaProject(concat_dfa, (unsigned) number_of_bdd_variables);
//	dfaFree(concat_dfa);
//	concat_dfa = dfaMinimize(tmp_dfa);
//	dfaFree(tmp_dfa); tmp_dfa = nullptr;

//  if(right_dfa->ns == 27) {
//    auto temp_auto = new StringAutomaton(concat_dfa,10);
//    temp_auto->inspectAuto(false,true);
//    std::cin.get();
//  }
//  if(right_dfa->ns == 27) dfaRightQuotient(concat_dfa,(unsigned)suffix_extrabit_0);
  DFA_ptr tmp_dfa = dfaProject(concat_dfa, (unsigned)suffix_extrabit_0);
  dfaFree(concat_dfa);
  concat_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);

	if (left_hand_side_accepts_emtpy_input) {
		tmp_dfa = concat_dfa;
		concat_dfa = DFAUnion(tmp_dfa,dfa2);
		delete tmp_dfa;
		delete left_dfa; left_dfa = nullptr;
	}
	if (right_hand_side_accepts_empty_input) {
		tmp_dfa = concat_dfa;
		concat_dfa = DFAUnion(tmp_dfa,dfa1);
		delete tmp_dfa;
		delete right_dfa; right_dfa = nullptr;
	}

  return concat_dfa;
}



int* Automaton::GetBddVariableIndices(const int number_of_bdd_variables) {
  auto it = bdd_variable_indices.find(number_of_bdd_variables);
  if (it != bdd_variable_indices.end())
  {
    return it->second;
  }
  int* indices = CreateBddVariableIndices(number_of_bdd_variables);
  bdd_variable_indices[number_of_bdd_variables] = indices;
  return indices;
}

int* Automaton::CreateBddVariableIndices(const int number_of_bdd_variables) {
  int* indices = new int[number_of_bdd_variables];
  for (int i = 0; i < number_of_bdd_variables; ++i) {
    indices[i] = i;
  }
  return indices;
}

std::vector<char> Automaton::GetBinaryFormat(unsigned long number, int bit_length) {
  unsigned subject = number;
  std::vector<char> binary_str (bit_length + 1, '\0');
  for (int index = bit_length - 1; index >= 0; --index) {
    if (subject & 1) {
      binary_str[index] = '1';
    } else {
      binary_str[index] = '0';
    }
    if (subject > 0) {
      subject >>= 1;
    }
  }

  return binary_str;
}

std::vector<char> Automaton::GetReversedBinaryFormat(unsigned long number, int bit_length) {
  unsigned subject = number;
  std::vector<char> binary_str (bit_length + 1, '\0');
  for (int index = 0; index < bit_length; ++index) {
    if (subject & 1) {
      binary_str[index] = '1';
    } else {
      binary_str[index] = '0';
    }
    if (subject > 0) {
      subject >>= 1;
    }
  }

  return binary_str;
}

std::string Automaton::GetBinaryStringMSB(unsigned long number, int bit_length) {
  int index = bit_length;
  unsigned subject = number;
  std::string binary_string (bit_length + 1, '\0');

  for (index--; index >= 0; index--) {
    if (subject & 1) {
      binary_string[index] = '1';
    } else {
      binary_string[index] = '0';
    }
    if (subject > 0) {
      subject >>= 1;
    }
  }

  return binary_string;
}

std::set<std::string> Automaton::ExpandTransition(std::string exception) {
  std::queue<std::string> work_queue;
  std::set<std::string> expanded_exceptions;

  work_queue.push(exception);

  while(not work_queue.empty()) {
    std::string exep = work_queue.front();
    work_queue.pop();

    bool found_x = false;

    for(int i = 0; i < exep.length(); i++) {
      if(exep[i] == 'X') {
        exep[i] = '0';
        work_queue.push(exep);
        exep[i] = '1';
        work_queue.push(exep);
        found_x = true;
        break;
      }
    }

    if(not found_x) {
      expanded_exceptions.insert(exep);
    }
  }

  return expanded_exceptions;
}

/**
 * That function replaces the getSharp1WithExtraBit 111111111 and
 * getSharp0WithExtraBit 111111110. (getSharp0WithExtraBit is not
 * the same as in LibStranger 111111100)
 * @return binary representation of reserved word
 */
std::vector<char> Automaton::getReservedWord(char last_char, int length, bool extra_bit) {
  std::vector<char> reserved_word;

  int i;
  for (i = 0; i < length - 1; i++) {
    reserved_word.push_back('1');
  }
  reserved_word.push_back(last_char);

  if (extra_bit) {
    reserved_word.push_back('1');
  }

  reserved_word.push_back('\0');

  return reserved_word;
}

void Automaton::Minimize() {
  DFA_ptr tmp = this->dfa_;
  this->dfa_ = dfaMinimize(tmp);
  dfaFree(tmp);
  DVLOG(VLOG_LEVEL) << this->id_ << " = [" << this->id_ << "]->minimize()";
}

void Automaton::ProjectAway(unsigned index) {
  DFA_ptr tmp = this->dfa_;
  this->dfa_ = dfaProject(tmp, index);
  dfaFree(tmp);

  if (index < (unsigned)(this->num_of_bdd_variables_ - 1)) {
    int* indices_map = new int[this->num_of_bdd_variables_];
    for (int i = 0, j = 0; i < this->num_of_bdd_variables_; i++) {
      if ((unsigned)i != index) {
        indices_map[i] = j;
        j++;
      }
    }
    dfaReplaceIndices(this->dfa_, indices_map);
    delete[] indices_map;
  }

  this->num_of_bdd_variables_ = this->num_of_bdd_variables_ - 1;

  DVLOG(VLOG_LEVEL) << this->id_ << " = [" << this->id_ << "]->project(" << index << ")";
}

bool Automaton::hasIncomingTransition(int state) {
	LOG(FATAL) << "implement me!";
//  for (int i = 0; i < this->dfa_->ns; i++) {
//    if (hasNextState(i, state)) {
//      return true;
//    }
//  }
//  return false;
}

/**
 * TODO will remove this function with a better approach in its uses
 * @returns true if a start state is reachable from an accepting state, false otherwise
 */
bool Automaton::TEMPisStartStateReachableFromAnAcceptingState(DFA_ptr dfa) {
  paths state_paths, pp;
  for (int i = 0; i < dfa->ns; i++) {
    if (DFAIsAcceptingState(dfa,i)) {
      state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
      while (pp) {
        if (pp->to == (unsigned) dfa->s) {
          kill_paths(state_paths);
          return true;
        }
        pp = pp->next;
      }
      kill_paths(state_paths);
    }
  }
  return false;
}

std::vector<std::pair<int,std::vector<char>>> Automaton::GetNextTransitions(int state) {
  std::vector<std::pair<int,std::vector<char>>> next_states;
  std::vector<unsigned> nodes;
  std::vector<std::vector<char>> transition_stack;
  std::vector<char> current_transition;
  int sink = GetSinkState();

  unsigned p, l, r, index; // BDD traversal variables
  p = this->dfa_->q[state];
  nodes.push_back(p);
  transition_stack.push_back(std::vector<char>());
  while (not nodes.empty()) {
    p = nodes.back();
    nodes.pop_back();
    current_transition = transition_stack.back();
    transition_stack.pop_back();
    LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
    	int to_state = l;
    	// if to_state is sink state, ignore
    	if(to_state == sink) {
    		continue;
    	}

      while (current_transition.size() < (unsigned) num_of_bdd_variables_) {
        current_transition.push_back('X');
      }
      // put loops first, other states at back
      if(to_state != state) {
        next_states.push_back(std::make_pair(to_state, current_transition));
      } else {
        next_states.insert(next_states.begin(),std::make_pair(to_state,current_transition));
      }

    } else {
      while (current_transition.size() < index) {
        unsigned i = current_transition.size();
        current_transition.push_back('X');
      }
      std::vector<char> left = current_transition;
      left.push_back('0');
      std::vector<char> right = current_transition;
      right.push_back('1');
      transition_stack.push_back(right);
      nodes.push_back(r);
      transition_stack.push_back(left);
      nodes.push_back(l);
    }
  }

  return next_states;
}

/**
 * @return next state from the state by taking transition path (1 step away)
 */
int Automaton::getNextState(int state, std::vector<char>& exception) {
  int next_state = -1; // only for initialization
   unsigned p, l, r, index = 0; // BDD traversal variables

   CHECK_EQ(num_of_bdd_variables_, exception.size());

   p = this->dfa_->q[state];

   for (int i = 0; i < num_of_bdd_variables_; i++) {
     LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
     if (index == BDD_LEAF_INDEX) {
       next_state = l;
       break;
     } else {
       if (exception[i] == '0') {
         p = l;
       } else if (exception[i] == '1') {
         p = r;
       }
     }
   }

   if (index != BDD_LEAF_INDEX) {
     LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
     if (index == BDD_LEAF_INDEX) {
       next_state = l;
     } else {
       LOG(FATAL) << "Please check this algorithm, something wrong with bdd traversal";
     }
   }

   return next_state;
}

/**
 * @return vector of states that are 1 walk away
 */
std::set<int> Automaton::getNextStates(int state) {
  unsigned p, l, r, index; // BDD traversal variables
  std::set<int> next_states;
  std::stack<unsigned> nodes;

  p = this->dfa_->q[state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top();
    nodes.pop();
    LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      next_states.insert(l);
    } else {
      nodes.push(l);
      nodes.push(r);
    }
  }
  return next_states;
}

/**
 * Returns next states with an example transition for each
 */
std::vector<NextState> Automaton::getNextStatesOrdered(int state, std::function<bool(unsigned& index)> next_node_heuristic) {
  std::vector<NextState> next_states;
  std::map<int, bool> visited;
  std::vector<unsigned> nodes;
  std::vector<std::vector<bool>> transition_stack;
  std::vector<bool> current_transition;


  unsigned p, l, r, index; // BDD traversal variables
  p = this->dfa_->q[state];
  nodes.push_back(p);
  transition_stack.push_back(std::vector<bool>());
  while (not nodes.empty()) {
    p = nodes.back();
    nodes.pop_back();
    current_transition = transition_stack.back();
    transition_stack.pop_back();
    LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      if (visited[l]) {
        // avoid cycles
      } else {
        state = l;
        while (current_transition.size() < (unsigned) num_of_bdd_variables_) {
          unsigned i = current_transition.size();
          if (next_node_heuristic and next_node_heuristic(i)) {
            current_transition.push_back(1); // add 1 for don't cares
          } else {
            current_transition.push_back(0); // add 0 for don't cares
          }
        }
        next_states.push_back(std::make_pair(l, current_transition));
      }
    } else {

      while (current_transition.size() < index) {
        unsigned i = current_transition.size();
        if (next_node_heuristic and next_node_heuristic(i)) {
          current_transition.push_back(1); // add 1 for don't cares
        } else {
          current_transition.push_back(0); // add 0 for don't cares
        }
      }

      std::vector<bool> left = current_transition;
      left.push_back(0);
      std::vector<bool> right = current_transition;
      right.push_back(1);
      if (next_node_heuristic and next_node_heuristic(index)) {
        transition_stack.push_back(left);
        nodes.push_back(l);
        transition_stack.push_back(right);
        nodes.push_back(r);
      } else {
        transition_stack.push_back(right);
        nodes.push_back(r);
        transition_stack.push_back(left);
        nodes.push_back(l);
      }
    }
  }

  return next_states;
}

std::set<int> Automaton::getStatesReachableBy(int walk) {
  return getStatesReachableBy(walk, walk);
}

std::set<int> Automaton::getStatesReachableBy(int min_walk, int max_walk) {
  std::set<int> states;

  std::stack<std::pair<int, int>> state_stack;
  int sink_state = GetSinkState();
  if (sink_state != this->dfa_->s) {
    state_stack.push(std::make_pair(this->dfa_->s, 0));
  }
  while (not state_stack.empty()) {
    auto current = state_stack.top(); state_stack.pop();

    if (current.second >= min_walk and current.second <= max_walk) {
      states.insert(current.first);
    }

    if (current.second < max_walk) {
      for (auto next_state : getNextStates(current.first)) {
        if (sink_state != next_state) {
          state_stack.push(std::make_pair(next_state, current.second + 1));
        }
      }
    }
  }
  return states;
}

void Automaton::SetSymbolicCounter() {
  std::vector<Eigen::Triplet<BigInteger>> entries;
  const int sink_state = GetSinkState();
  unsigned left, right, index;
  for (int s = 0; s < this->dfa_->ns; ++s) {
    if (sink_state != s) {
      // Node is a pair<sbdd_node_id, bdd_depth>
      Node current_bdd_node {dfa_->q[s], 0}, left_node, right_node;
      std::stack<Node> bdd_node_stack;
      bdd_node_stack.push(current_bdd_node);
      while (not bdd_node_stack.empty()) {
        current_bdd_node = bdd_node_stack.top(); bdd_node_stack.pop();
        LOAD_lri(&dfa_->bddm->node_table[current_bdd_node.first], left, right, index);
        if (index == BDD_LEAF_INDEX) {
          if (sink_state != left) {
            const int exponent = num_of_bdd_variables_ - current_bdd_node.second;
            if (exponent == 0) {
              entries.push_back(Eigen::Triplet<BigInteger>(s, left, 1));
            } else if (exponent < 31) {
              entries.push_back(Eigen::Triplet<BigInteger>(s, left, static_cast<int>(std::pow(2, exponent))));
            } else {
              entries.push_back(Eigen::Triplet<BigInteger>(s, left, boost::multiprecision::pow(boost::multiprecision::cpp_int(2), exponent)));
            }
          }
        } else {
          left_node.first = left;
          left_node.second = current_bdd_node.second + 1;
          right_node.first = right;
          right_node.second = current_bdd_node.second + 1;
          bdd_node_stack.push(left_node);
          bdd_node_stack.push(right_node);
        }
      }

      // combine all accepting states into one artifical accepting state
      if (IsAcceptingState(s)) {
        entries.push_back(Eigen::Triplet<BigInteger>(s, this->dfa_->ns, 1));
      }
    }
  }
  Eigen::SparseMatrix<BigInteger> count_matrix (this->dfa_->ns + 1, this->dfa_->ns + 1);
  count_matrix.setFromTriplets(entries.begin(), entries.end());
  decide_counting_schema(count_matrix);
  count_matrix.makeCompressed();
  count_matrix.finalize();
  counter_.set_transition_count_matrix(count_matrix);
  counter_.set_initialization_vector(count_matrix.innerVector(count_matrix.cols()-1));
  is_counter_cached_ = true;
}

/**
 * Default is set to string variable counting
 */
void Automaton::decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) {
  counter_.set_type(SymbolicCounter::Type::STRING);
  if(count_bound_exact_) {
  	count_matrix.insert(this->dfa_->ns, this->dfa_->ns) = 0;
  } else {
  	count_matrix.insert(this->dfa_->ns, this->dfa_->ns) = 1; // allows us to count all lengths up to given bound
  }
}

void Automaton::generateGFScript(int bound, std::ostream& out, bool count_less_than_or_equal_to_bound) {
  LOG(FATAL) << "Refactor me with CountMatrix or add SparseCountMatrix";
//  AdjacencyList adjacency_count_list = getAdjacencyCountList();
//  unsigned node_size = adjacency_count_list.size();
//  unsigned updated_node_size = node_size + 1;
//  adjacency_count_list.resize(updated_node_size);
//
//  Node artificial;
//
//  // add a self-loop if we count up to bound (bound inclusive)
//  if (count_less_than_or_equal_to_bound) {
//    artificial.first = node_size;
//    artificial.second = 1;
//    adjacency_count_list[node_size].push_back(artificial);
//  }
//
//  for (int i = 0; (unsigned)i < node_size; i++) {
//    if (is_accepting_state(i)) {
//      artificial.first = i;
//      artificial.second = 1;
//      adjacency_count_list[node_size].push_back(artificial);
//    }
//  }
//
//  out << "bound = " << bound + 2 << ";\n";
//  out << "ID = IdentityMatrix[" << updated_node_size << "];\n\n";
//  out << "A = SparseArray[ { ";
//  std::string row_seperator = "";
//  std::string col_seperator = "";
//  int c = 0;
//  for (auto& transitions : adjacency_count_list) {
//    out << row_seperator;
//    row_seperator = "";
//    col_seperator = "";
//    for(auto& node : transitions) {
//      out << col_seperator;
//      out << "{" << node.first + 1 << ", " << c + 1 << "} -> " << node.second;
//      col_seperator = ", ";
//      row_seperator = ", ";
//    }
//    c++;
//  }
//  out << "}];\n\n";
//  out << "X = ID - A t;\n\n";
//  out << "Xsubmatrix = X[[ {";
//  std::string seperator = "";
//  for(unsigned i = 1; i < updated_node_size; i++) {
//    out << seperator << i;
//    seperator = ",";
//  }
//  out << "},{";
//  for(unsigned i = 1; i < updated_node_size - 1; i++){
//    out << i << ",";
//  }
//
//  out << updated_node_size << "}";
//
//  out << "]];\n";
//
//  out << "b = CoefficientList[-Det[Xsubmatrix],t];\n";
//  out << "c = CoefficientList[Det[X],t];\n";
//  out << "maxLen = Max[Map[Length, {b,c}]]\n";
//  out << "bPadLen = Max[0, maxLen - Length[b]];\n";
//  out << "cPadLen = Max[0, maxLen - Length[c]];\n";
//  out << "b = ArrayPad[b, {0, bPadLen}];\n";
//  out << "c = ArrayPad[c, {0, cPadLen}];\n";
//  out << "p = -c[[ Range[2,maxLen] ]] / c[[1]];\n";
//  out << "a = Table[0,{maxLen}];\n";
//  out << "a[[1]] = b[[1]]/c[[1]];\n";
//  out << "For[ i = 2, i <= maxLen, i++, a[[i]] = (b[[i]] - Total[c[[2;;i]]*a[[i-1;;1;;-1]]]) / c[[1]] ];\n";
//  out << "numPaths = LinearRecurrence[p,a,{bound,bound}][[1]];\n";
//  out << "Print[N[numPaths]];";
//
//  out << std::endl;
}

void Automaton::generateMatrixScript(int bound, std::ostream& out, bool count_less_than_or_equal_to_bound) {
  LOG(FATAL) << "Refactor me with CountMatrix or add SparseCountMatrix";
//  AdjacencyList adjacency_count_list = getAdjacencyCountList();
//  unsigned node_size = adjacency_count_list.size();
//  unsigned updated_node_size = node_size + 1;
//  adjacency_count_list.resize(updated_node_size);
//
//  Node artificial;
//
//  // add a self-loop if we count up to bound (bound inclusive)
//  if (count_less_than_or_equal_to_bound) {
//    artificial.first = node_size;
//    artificial.second = 1;
//    adjacency_count_list[node_size].push_back(artificial);
//  }
//
//  for (int i = 0; (unsigned)i < node_size; i++) {
//    if (is_accepting_state(i)) {
//      artificial.first = i;
//      artificial.second = 1;
//      adjacency_count_list[node_size].push_back(artificial);
//    }
//  }
//
//  out << "A = SparseArray[{";
//  std::string row_seperator = "";
//  std::string col_seperator = "";
//  int c = 0;
//  for (auto& transitions : adjacency_count_list) {
//    out << row_seperator;
//    row_seperator = "";
//    col_seperator = "";
//    for(auto& node : transitions) {
//      out << col_seperator;
//      out << "{" << node.first + 1 << ", " << c + 1 << "} -> " << node.second;
//      col_seperator = ", ";
//      row_seperator = ", ";
//    }
//    c++;
//  }
//  out << "}];\n";
//  // state indexes are off by one
//  out << "numPaths = MatrixPower[A, " << bound + 2 << "][[" << this->dfa_->s + 1 << ", " << this->dfa_->ns + 1 << "]];\n";
//  out << "Print[N[numPaths]];";
//  out << std::endl;
}

/**
 * TODO Reimplement, combine with toDot
 *
 */
void Automaton::toDotAscii(bool print_sink, std::ostream& out) {

  print_sink = print_sink || (dfa_->ns == 1 and dfa_->f[0] == -1);
  int sink_state = GetSinkState();

  out << "digraph MONA_DFA {\n"
          " rankdir = LR;\n "
          " center = true;\n"
          " size = \"700.5,1000.5\";\n"
          " edge [fontname = Courier];\n"
          " node [height = .5, width = .5];\n"
          " node [shape = doublecircle];";

  for (int i = 0; i < dfa_->ns; i++) {
    if (dfa_->f[i] == 1) {
      out << " " << i << ";";
    }
  }

  out << "\n node [shape = circle];";

  for (int i = 0; i < dfa_->ns; i++) {
    if (dfa_->f[i] == -1) {
      if (i != sink_state || print_sink) {
        out << " " << i << ";";
      }
    }
  }

  out << "\n node [shape = box];";

  for (int i = 0; i < dfa_->ns; i++) {
    if (dfa_->f[i] == 0) {
      out << " " << i << ";";
    }
  }

  out << "\n init [shape = plaintext, label = \"\"];\n" << " init -> " << dfa_->s << ";\n";

  LOG(FATAL) << "Reimplement toDotAscii";
//  paths state_paths, pp;
//  trace_descr tp;
//
//  for (int i = 0; i < dfa_->ns; i++) {
//    state_paths = pp = make_paths(dfa_->bddm, dfa_->q[i]);
//    while (pp) {
//      if ((int)pp->to == sink_state && not print_sink) {
//        pp = pp->next;
//        continue;
//      }
//
//      for (j = 0; j < num_of_variables; j++) {
//        for (tp = pp->trace; tp && (tp->index != (unsigned) variable_indices[j]); tp = tp->next)
//          ;
//
//        if (tp) {
//          if (tp->value)
//            character[j] = '1';
//          else
//            character[j] = '0';
//        } else
//          character[j] = 'X';
//      }
//      character[j] = '\0';
//      if (num_of_variables == 8) {
//        //break mona character into ranges of ascii chars (example: "0XXX000X" -> [\s-!], [0-1], [@-A], [P-Q])
//        size = 0;
//        getTransitionChars(character, num_of_variables, buffer, &size);
//        //get current index
//        k = toTransIndecies[pp->to];
//        //print ranges
//        for (l = 0; l < size; l++) {
//          toTrans[pp->to][k++] = buffer[l];
//          buffer[l] = 0;    //do not free just detach
//        }
//        toTransIndecies[pp->to] = k;
//      } else {
////        k = toTransIndecies[pp->to];
////        toTrans[pp->to][k] = (char*) malloc(sizeof(char) * (strlen(character) + 1));
////        strcpy(toTrans[pp->to][k], character);
////        toTransIndecies[pp->to] = k + 1;
//      }
//      pp = pp->next;
//    }
//
//    //print transitions out of state i
//    for (j = 0; j < dfa->ns; j++) {
//      size = toTransIndecies[j];
//      if (size == 0 || (sink_state == j && not print_sink)) {
//        continue;
//      }
//      ranges = mergeCharRanges(toTrans[j], &size);
//      //print edge from i to j
//      out << " " << i << " -> " << j << " [label=\"";
//      bool print_label = (j != sink_state || print_sink);
//      l = 0;    //to help breaking into new line
//      //for each trans k on char/range from i to j
//      for (k = 0; k < size; k++) {
//        //print char/range
//        if (print_label) {
//          out << " " << ranges[k];
//        }
//        l += strlen(ranges[k]);
//        if (l > 18) {
//          if (print_label) {
//            out << "\\n";
//          }
//          l = 0;
//        } else if (k < (size - 1)) {
//          if (print_label) {
//            out << ",";
//          }
//        }
//        free(ranges[k]);
//      }      //for
//      out << "\"];\n";
//      if (size > 0)
//        free(ranges);
//    }
//    //for each state free charRange
//    //merge with loop above for better performance
//    for (j = 0; j < dfa->ns; j++) {
//      if (j == sink_state && not print_sink) {
//        continue;
//      }
//      size = toTransIndecies[j];
//      for (k = 0; k < size; k++) {
//        free(toTrans[j][k]);
//      }
//    }
//
//    kill_paths(state_paths);
//  }    //end for each state
//
//  free(character);
//  free(buffer);
//  for (i = 0; i < dfa->ns; i++) {
//    free(toTrans[i]);
//  }
//  free(toTrans);
//  free(toTransIndecies);

  out << "}" << std::endl;
}

void Automaton::ToDot(std::ostream& out, bool print_sink) {
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, l;
  char **buffer;
  int *used, *allocated;
  int* offsets = GetBddVariableIndices(num_of_bdd_variables_);
  int no_free_vars = num_of_bdd_variables_;
  DFA_ptr a = this->dfa_;
  int sink = GetSinkState();

  print_sink = print_sink || (dfa_->ns == 1 and dfa_->f[0] == -1);

  out << "digraph MONA_DFA {\n"
          " rankdir = LR;\n"
          " center = true;\n"
          " size = \"7.5,10.5\";\n"
          " edge [fontname = Courier];\n"
          " node [height = .5, width = .5];\n"
          " node [shape = doublecircle];";
  for (i = 0; i < a->ns; i++) {
    if (a->f[i] == 1) {
      out << " " << i << ";";
    }
  }
  out << "\n node [shape = circle];";
  for (i = 0; i < a->ns; i++) {
    if (a->f[i] == -1) {
      if (i != sink || print_sink) {
        out << " " << i << ";";
      }
    }
  }
  out << "\n node [shape = box];";
  for (i = 0; i < a->ns; i++) {
    if (a->f[i] == 0) {
      out << " " << i << ";";
    }
  }
  out << "\n init [shape = plaintext, label = \"\"];\n"
          " init -> " << a->s << ";\n";

  buffer = (char **) mem_alloc(sizeof(char *) * a->ns);
  used = (int *) mem_alloc(sizeof(int) * a->ns);
  allocated = (int *) mem_alloc(sizeof(int) * a->ns);

  for (i = 0; i < a->ns; i++) {
    if (i == sink && not print_sink) {
      continue;
    }
    state_paths = pp = make_paths(a->bddm, a->q[i]);

    for (j = 0; j < a->ns; j++) {
      if (i == sink && not print_sink) {
        continue;
      }
      buffer[j] = 0;
      used[j] = allocated[j] = 0;
    }

    while (pp) {
      if (pp->to == (unsigned) sink && not print_sink) {
        pp = pp->next;
        continue;
      }
      if (used[pp->to] >= allocated[pp->to]) {
        allocated[pp->to] = allocated[pp->to] * 2 + 2;
        buffer[pp->to] = (char *) mem_resize(buffer[pp->to], sizeof(char) * allocated[pp->to] * no_free_vars);
      }

      for (j = 0; j < no_free_vars; j++) {
        char c;
        for (tp = pp->trace; tp && (tp->index != (unsigned)offsets[j]); tp = tp->next)
          ;

        if (tp) {
          if (tp->value) {
            c = '1';
          } else {
            c = '0';
          }
        } else {
          c = 'X';
        }

        buffer[pp->to][no_free_vars * used[pp->to] + j] = c;
      }
      used[pp->to]++;
      pp = pp->next;
    }

    for (j = 0; j < a->ns; j++) {
      if (j == sink && not print_sink) {
        continue;
      }
      if (buffer[j]) {
        out << " " << i << " -> " << j << " [label=\"";
        for (k = 0; k < no_free_vars; k++) {
          for (l = 0; l < used[j]; l++) {
            out << buffer[j][no_free_vars * l + k];
            if (l + 1 < used[j]) {
              if (k + 1 == no_free_vars)
                out << ',';
              else
                out << ' ';
            }
          }
          if (k + 1 < no_free_vars)
            out << "\\n";
        }
        out << "\"];\n";
        mem_free(buffer[j]);
      }
    }
    kill_paths(state_paths);
  }

  mem_free(allocated);
  mem_free(used);
  mem_free(buffer);
  add_print_label(out);
  out << "}" << std::endl;
}

void Automaton::add_print_label(std::ostream& out) {
  return;
}

void Automaton::toBDD(std::ostream& out) {
//
////  Automaton::BddDump(out,this->dfa_->bddm);
////  for(int i = 0; i < this->dfa_->ns; i++) {
////    out << this->dfa_->f[i] << ",";
////  }
////  out << "\n";
////  return;
//
//  Table *table = tableInit();
//
//  /* remove all marks in a->bddm */
//  bdd_prepare_apply1(this->dfa_->bddm);
//
//  /* build table of tuples (idx,lo,hi) */
//
//  /* renumber lo/hi pointers to new table ordering */
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx != -1) {
//      table->elms[i].lo = bdd_mark(this->dfa_->bddm, table->elms[i].lo) - 1;
//      table->elms[i].hi = bdd_mark(this->dfa_->bddm, table->elms[i].hi) - 1;
//    }
//    out << table->elms[i].idx << "," << table->elms[i].lo << ","  << table->elms[i].hi << ";";
//  }
//
//  for (int i = 0; i < this->dfa_->ns; i++) {
//    _export(this->dfa_->bddm, this->dfa_->q[i], table);
//    out << "{" << this->dfa_->f[i] << "|<" << i << "> " << i << "}";
//    if ((unsigned) (i + 1) < table->noelems) {
//      out << "|";
//    }
//    out << " s1:" << i << " -> " << bdd_mark(this->dfa_->bddm, this->dfa_->q[i]) - 1 << " [style=bold];\n";
//  }
////  out << dfa_->ns << dfa_->s;
////  for(int i = 0; i < this->dfa_->ns; i++) {
////    out << dfa_->f[i] << (bdd_mark(dfa_->bddm, dfa_->q[i]) - 1);
////  }
////
//
////  out << "digraph MONA_DFA_BDD {\n"
////          "  center = true;\n"
////          "  size = \"100.5,70.5\"\n"
////      "  orientation = landscape;\n"
////          "  node [shape=record];\n"
////          "   s1 [shape=record,label=\"";
///*
//  for (int i = 0; i < this->dfa_->ns; i++) {
//    out << "{" << this->dfa_->f[i] << "|<" << i << "> " << i << "}";
//    if ((unsigned) (i + 1) < table->noelems) {
//      out << "|";
//    }
//  }
//  out << "\"];" << std::endl;
//
//  out << "  node [shape = circle];";
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx != -1) {
//      out << " " << i << " [label=\"" << table->elms[i].idx << "\"];";
//    }
//  }
//
//  out << "\n  node [shape = box];";
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx == -1) {
//      out << " " << i << " [label=\"" << table->elms[i].lo << "\"];";
//    }
//  }
//  out << std::endl;
//
//  for (int i = 0; i < this->dfa_->ns; i++) {
//    out << " s1:" << i << " -> " << bdd_mark(this->dfa_->bddm, this->dfa_->q[i]) - 1 << " [style=bold];\n";
//  }
//
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx != -1) {
//      int lo = table->elms[i].lo;
//      int hi = table->elms[i].hi;
//      out << " " << i << " -> " << lo << " [style=dashed];\n";
//      out << " " << i << " -> " << hi << " [style=filled];\n";
//    }
//  }
//  */
//  out << "}" << std::endl;
//  tableFree(table);
Table *table = tableInit();

  /* remove all marks in a->bddm */
  bdd_prepare_apply1(this->dfa_->bddm);

  /* build table of tuples (idx,lo,hi) */
  for (int i = 0; i < this->dfa_->ns; i++) {
    _export(this->dfa_->bddm, this->dfa_->q[i], table);
    out << "{" << this->dfa_->f[i] << "|<" << i << "> " << i << "}";
    out << " s1:" << i << " -> " << bdd_mark(this->dfa_->bddm, this->dfa_->q[i]) - 1 << " [style=bold];\n";
    if ((unsigned) (i + 1) < table->noelems) {
      out << "|";
    }
  }
  out << "\"];" << std::endl;
  /* renumber lo/hi pointers to new table ordering */
  for (unsigned i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx != -1) {
      table->elms[i].lo = bdd_mark(this->dfa_->bddm, table->elms[i].lo) - 1;
      table->elms[i].hi = bdd_mark(this->dfa_->bddm, table->elms[i].hi) - 1;
      out << " " << i << " [label=\"" << table->elms[i].idx << "," << table->elms[i].lo << "," << table->elms[i].hi << "\"];";
    }

  }





//  out << "  node [shape = circle];";
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx != -1) {
//      out << " " << i << " [label=\"" << table->elms[i].idx << "\"];";
//    }
//  }
//
//  out << "\n  node [shape = box];";
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx == -1) {
//      out << " " << i << " [label=\"" << table->elms[i].lo << "\"];";
//    }
//  }
//  out << std::endl;
//
//
//  for (unsigned i = 0; i < table->noelems; i++) {
//    if (table->elms[i].idx != -1) {
//      int lo = table->elms[i].lo;
//      int hi = table->elms[i].hi;
//      out << " " << i << " -> " << lo << " [style=dashed];\n";
//      out << " " << i << " -> " << hi << " [style=filled];\n";
//    }
//  }
  out << "}" << std::endl;
  tableFree(table);
}

void Automaton::BddDump(std::ostream& out, bdd_manager *bddm) {
  int i;
  for (i = 0; i < bdd_roots_length(bddm); i++)
    BddDumpNode(out, bddm, BDD_ROOT(bddm, i));
  for (i = 0; i < bdd_roots_length(bddm); i++)
    BddReverseMarks(out, bddm, BDD_ROOT(bddm, i));
}

void Automaton::BddDumpNode(std::ostream& out, bdd_manager *bddm, bdd_ptr p) {
  if ((signed) bdd_mark(bddm, p) >= 0) {
    bdd_set_mark(bddm, p, ~bdd_mark(bddm, p));
    if (!bdd_is_leaf(bddm, p)) {
      //printf("%-3u: idx=%-3u lo=%-3u hi=%-3u\n",
	     out << p << ": idx=" << bdd_ifindex(bddm, p) << " lo=" << bdd_else(bddm, p) << " hi=" << bdd_then(bddm, p) << "\n";
      BddDumpNode(out, bddm, bdd_else(bddm, p));
      BddDumpNode(out, bddm, bdd_then(bddm, p));
    }
    else
      out << p << ": state=" << bdd_leaf_value(bddm,p) << "\n";
  }
}

void Automaton::BddReverseMarks(std::ostream& out, bdd_manager *bddm, bdd_ptr p) {
  if ((signed) bdd_mark(bddm, p) < 0) {
    bdd_set_mark(bddm, p, ~bdd_mark(bddm, p));
    if (!bdd_is_leaf(bddm, p)) {
      BddReverseMarks(out, bddm, bdd_else(bddm, p));
      BddReverseMarks(out, bddm, bdd_then(bddm, p));
    }
  }
}


void Automaton::exportDfa(std::string file_name) {
  char* file_name_ptr = &*file_name.begin();
  // order 0 for boolean variables
  // we dont care about variable names but they are used in
  // MONA DFA file format with dfaExport()
  char **names = new char*[this->num_of_bdd_variables_];
  char *orders = new char[this->num_of_bdd_variables_];
  std::string name = "a";
  for (int i = 0; i < this->num_of_bdd_variables_; i++) {
    orders[i] = i;
    names[0] = &*name.begin();
  }

  dfaExport(this->dfa_, nullptr, this->num_of_bdd_variables_, names, orders);
}

DFA_ptr Automaton::importDFA(std::string file_name) {
  char **names = new char*[this->num_of_bdd_variables_];
  int ** orders = new int*[this->num_of_bdd_variables_];
  return dfaImport(&*file_name.begin(), &names, orders);
}

int Automaton::inspectAuto(bool print_sink, bool force_mona_format) {
  std::stringstream file_name;
  file_name << "./output/inspect_auto_" << name_counter++ << ".dot";
  std::string file = file_name.str();
  std::ofstream outfile(file.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file << std::endl;
    exit(2);
  }
  if (Automaton::Type::INT == type_ or Automaton::Type::STRING == type_) {
    if (force_mona_format) {
      ToDot(outfile, print_sink);
    } else {
      toDotAscii(print_sink, outfile);
    }
  } else {
    ToDot(outfile, print_sink);
  }
  std::string dot_cmd("xdot " + file + " &");
  return std::system(dot_cmd.c_str());
}

int Automaton::inspectBDD() {
  std::stringstream file_name;
  file_name << "./output/inspect_BDD_" << name_counter++ << ".dot";
  std::string file = file_name.str();
  std::ofstream outfile(file.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file << std::endl;
    exit(2);
  }
  toBDD(outfile);
  std::string dot_cmd("xdot " + file + " &");
  return std::system(dot_cmd.c_str());
}

void Automaton::getTransitionCharsHelper(pCharPair result[], char* transitions, int* indexInResult, int currentBit, int var){
  int i;
  boolean allX;
  if (transitions[currentBit] == 'X')
  {
    allX = TRUE;
    for (i = currentBit + 1; i < var; i++){
      if (transitions[i] != 'X'){
        allX = FALSE;
        break;
      }
    }
    if (allX == FALSE){
      transitions[currentBit] = '0';
      getTransitionCharsHelper(result, transitions, indexInResult, currentBit, var);
      transitions[currentBit] = '1';
      getTransitionCharsHelper(result, transitions, indexInResult, currentBit, var);
      transitions[currentBit] = 'X';
    }
    else {
      // convert to a char range (c1,cn)
      pCharPair charPairPtr = (pCharPair) malloc(sizeof(CharPair));
      char* firstBin = (char*) malloc((var+1)*(sizeof (char)));
      char* lastBin = (char*) malloc((var+1)*(sizeof (char)));
      // fill up prev bits
      for (i = 0; i < currentBit; i++){
        lastBin[i] = firstBin[i] = transitions[i];
      }
      // fill up first with 0's and last with 1's
      for (i = currentBit; i < var; i++){
        firstBin[i] = '0';
        lastBin[i] = '1';
      }
      lastBin[var] = firstBin[var] = '\0';
      char firstChar = strtobin(firstBin, var);
      char lastChar = strtobin(lastBin, var);
      charPairPtr->first = firstChar;
      charPairPtr->last = lastChar;
      result[*indexInResult] = charPairPtr;
      (*indexInResult)++;
      free(firstBin);
      free(lastBin);
    }

  }

  else if (currentBit == (var - 1))
  {
    // convert into a single char pair (c,c)
    pCharPair charPairPtr = (pCharPair) malloc(sizeof(CharPair));
    char* firstBin = (char*) malloc((var+1)*(sizeof (char)));
    // fill up prev bits
    for (i = 0; i <= currentBit; i++){
      firstBin[i] = transitions[i];
    }
    unsigned char char_ = strtobin(firstBin, var);
    charPairPtr->first = charPairPtr->last = char_;
    result[*indexInResult] = charPairPtr;
    (*indexInResult)++;
    free(firstBin);
  }

  else {
    if (currentBit < (var - 1))
      getTransitionCharsHelper(result, transitions, indexInResult, currentBit + 1, var);
  }

}

/**
 * Given a mona char in 'transitions', returns in 'result' a set of CharPairs representing all ASCII chars/ranges included in this char
 * where *pSize is the number of these ranges.
 * Note that a CharPair is a pair of char values (each of type char).
 * Example: input="0XXX000X"  ==> output=(NUL,SOH), (DLE,DC1), (\s,!), (0,1), (@,A), (P,Q), (`,a), (p,q) , *pSize=8
 * Example: input="00000000"  ==> output=(NUL,NUL), *pSize=1
 * Example: input="XXXXXXXX"  ==> output=(NUL,255), *pSize=1
 */
void Automaton::getTransitionChars(char* transitions, int var, pCharPair result[], int* pSize){
  CHECK(strlen(transitions) == var);
  char* trans = (char*) malloc((var + 1)* sizeof(char));
  strcpy(trans, transitions);
  int indexInResult = 0;
  getTransitionCharsHelper(result, trans, &indexInResult, 0, var);
  *pSize = indexInResult;
  free(trans);
}

/* Given a list of CharPairs in 'charRanges', returns a list of STRINGS representing all ASCII chars/ranges included in the
 * input list after merging them where *pSize is the number of these ranges
 * Note values in input are of type char while values of output are the char value (of type char) converted into a string (of type char*)
 * For non printable chars, either its name in ASCII chart (NUL, SOH, CR, LF, ...etc) or its Decimal value is output
 * Example: input=(NUL,SOH), (DLE,DC1), (\s,!), (0,1), (@,A), (P,Q), (`,a), (p,q)  ==> output="[NUL-SOH]", "[DLE-DC1]", "[\s - ! ]", "[ 0 - 1 ]", "[ @ - A ]", "[ P - Q ]", "[ ` - a ]", "[ p - q ]" , *pSize=8
 * Example: input=(NUL,US), (!,!), (",#), ($,'), ((,/), (0,?), (@,DEL), (128, 255)  ==> output="[NUL-US]", "[!-255]", *pSize=1
 * Example: input=(NUL,NUL)  ==> output="NUL", *pSize=1
 * Example: input=(255,255)  ==> output="255", *pSize=1
 * Example: input=(NUL,255)  ==> output="[NUL-255]", *pSize=1
 */
char** Automaton::mergeCharRanges(pCharPair charRanges[], int* p_size){
  int size = *p_size;
  int i, k, newSize;
  char newFirst, newLast;

  if (size == 0)
    return NULL;
  newSize = 0;
  char** ranges = (char**)malloc(sizeof(char*) * size);
  for (i = 0; i < size; i = k + 1){
    k = i;
    while(k < (size - 1)){
      if (((charRanges[k]->last) + 1) != charRanges[k + 1]->first)
        break;
      else
        k++;
    }
    newFirst = charRanges[i]->first;
    newLast = charRanges[k]->last;
    if (newFirst == newLast){
      ranges[newSize] = (char*)malloc(4 * sizeof(char));
      charToAscii(ranges[newSize], newFirst);
    }
    else{
      ranges[newSize] = (char*)malloc(10 * sizeof(char));
      fillOutCharRange(ranges[newSize], newFirst, newLast);
    }
    newSize++;
  }
  *p_size = newSize;
  return ranges;
}

/**
 * Given char ci, fills s with ASCII decimal value of n as a
 * string.
 * s: must not be null, allocated before to be of size >= 4
 */
void Automaton::charToAsciiDigits(unsigned char ci, char s[])
{
    int i, j;
    unsigned char c;
    CHECK(s != NULL);
    i = 0;
    do {       /* generate digits in reverse order */
        s[i++] = ci % 10 + '0';   /* get next digit */
    } while ((ci /= 10) > 0);     /* delete it */

    s[i] = '\0';
  for (i = 0, j = (int)strlen(s)-1; i<j; i++, j--) {
    c = s[i];
    s[i] = s[j];
    s[j] = c;
  }
}

/**
 * give a char c, returns its ASCII value in asciiVal
 * as a string of length <= 3. For non printable chars
 * it returns their ascii chart value according to ascii table or
 * their decimal value if above 126.
 * asciiVal must be allocated before with size >= 4
 */
void Automaton::charToAscii(char* asciiVal, unsigned char c){
  int i = 0;
  CHECK(asciiVal != NULL);
  char* charName[] = {"NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS ", "HT ", "LF ", "VT ", "FF ", "CR ", "SO ", "SI ", "DLE",
      "DC1", "DC2", "CD3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM ", "SUB", "ESC", "FS ", "GS ", "RS ", "US "};
  if (c < 32){
    strcpy(asciiVal, charName[(int)c]);
    return;
  }
  else if (c > 126){
    charToAsciiDigits(c, asciiVal);
    CHECK(strlen(asciiVal) == 3);
    return;
  }
  else {
    switch(c){
      case ' ': // ' ' -> \\s
        asciiVal[i++] = '\\';
        asciiVal[i++] = '\\';
        asciiVal[i++] = 's';
        break;
      case '\t': // ' ' -> \\t
        asciiVal[i++] = '\\';
        asciiVal[i++] = '\\';//needed to escape first back slash for dot file parser
        asciiVal[i++] = 't';
        break;
      case '"':
        asciiVal[i++] = '\\';//needed to escape double quote for dot file parser
        asciiVal[i++] = '"';
        break;
      case '\\':
        asciiVal[i++] = '\\';
        asciiVal[i++] = '\\';//needed to escape first back slash for dot file parser
        break;
      default:
        asciiVal[i++] = c;
    }
    asciiVal[i] = '\0';
    return;
  }

}

/**
 * given two characters returns a string (char*) range == "[firstChar-lastChar]"
 */
void Automaton::fillOutCharRange(char* range, char firstChar, char lastChar){
  int i = 0;
  if (firstChar == lastChar){
    charToAscii(range, firstChar);
    CHECK(strlen(range) <= 3);
    return;
  }

  char* char1 = (char*)(malloc ((4) * (sizeof(char))));
  char* char2 = (char*)(malloc ((4) * (sizeof(char))));
  //[firstChar-lastChar]
  range[i++] = '[';

  //put first char in range
  charToAscii(char1, firstChar);
  CHECK(strlen(char1) <= 3);
  strncpy(range+i, char1, strlen(char1));
  i += strlen(char1);
  range[i++] = '-';
  //put second char in range
  charToAscii(char2, lastChar);
  CHECK(strlen(char2) <= 3);
  strncpy(range+i, char2, strlen(char2));
  i += strlen(char2);

  range[i++] = ']';

  range[i] = '\0';
  CHECK(strlen(range) <= 9);

  free(char1);
  free(char2);
}

char* Automaton::bintostr(unsigned long n, int k) {
  char *str;

  // no extra bit
  str = (char *) malloc(k + 1);
  str[k] = '\0';

  for (k--; k >= 0; k--) {
    if (n & 1)
      str[k] = '1';
    else
      str[k] = '0';
    if (n > 0)
      n >>= 1;
  }
  //printf("String:%s\n", str);
  return str;
}

unsigned char Automaton::strtobin(char* binChar, int var){
  // no extra bit
  char* str = binChar;
  int k = var;
  unsigned char c = 0;
  for (k = 0; k < var; k++) {
    if (str[k] == '1')
      c |= 1;
    else
      c |= 0;
    if (k < (var-1))
      c <<= 1;
  }
  return c;
}

int Automaton::find_sink(DFA_ptr dfa) {
  if(dfa == nullptr) {
    LOG(FATAL) << "Null dfa? Really?";
  }
  for (int i = 0; i < dfa->ns; i++) {
    int state_id = i;
    if ((bdd_is_leaf(dfa->bddm, dfa->q[state_id])
          and (bdd_leaf_value(dfa->bddm, dfa->q[state_id]) == (unsigned) state_id)
          and dfa->f[state_id] == -1)) {
      return i;
    }
  }

  return -1;
}

/*
 * BEGIN LIBSTRANGER ToUPPER toLOWER stuff
 */

void Automaton::getUpperCaseCharsHelper(char** result, char* transitions, int* indexInResult, int currentBit, int var, char* prev){
	int i;
	if (transitions[currentBit] == 'X')
	{
		transitions[currentBit] = '0';
		getUpperCaseCharsHelper(result, transitions, indexInResult, currentBit, var, prev);
		transitions[currentBit] = '1';
		getUpperCaseCharsHelper(result, transitions, indexInResult, currentBit, var, prev);
		transitions[currentBit] = 'X';
	}
	// things that do not contain upper case
	else if ( (transitions[0] == '1' && currentBit == 0) ||
			  (transitions[1] == '0' && currentBit == 1) ||
			  (transitions[2] == '0' && currentBit == 2) ||
			  (transitions[5] == '1' && transitions[3] == '1' && currentBit == 5) ||
			  (transitions[7] ==  transitions[3] && currentBit == 7)
			 )
	{
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof (char)));
		for (i = 0; i < var; i++){
			result[*indexInResult][i] = transitions[i];
		}
		result[*indexInResult][var] = '0';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
	}
	else if ( (transitions[3] != transitions[4] && (currentBit == 4 )) ||
			  (transitions[3] != transitions[6] && currentBit == 6 ) ||
			  (transitions[3] != transitions[7] && currentBit == 7 ) ||
			  (transitions[5] == '1' && transitions[3] ==  '0' && currentBit == 5)
				 ){
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof(char)));
		for (i = 0; i < var; i++)
			result[*indexInResult][i] = transitions[i];
		// only difference between capital and small is bit number 2
		result[*indexInResult][2] = '0';
		// extrabit should be 1 since we may already have same small letter originally with 0
		result[*indexInResult][var] = '1';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
	}
	else{
		if (currentBit < (var-1)){
			getUpperCaseCharsHelper(result, transitions, indexInResult, currentBit + 1, var, prev);
		}
		else
			assert(FALSE);
	}
}

void Automaton::getLowerUpperCaseCharsPrePostHelper(char** result, char* transitions, int* indexInResult, int currentBit, int var, char* prev, boolean lowerCase, boolean preImage){
	int i;
	if (transitions[currentBit] == 'X')
	{
		transitions[currentBit] = '0';
		getLowerUpperCaseCharsPrePostHelper(result, transitions, indexInResult, currentBit, var, prev, lowerCase, preImage);
		transitions[currentBit] = '1';
		getLowerUpperCaseCharsPrePostHelper(result, transitions, indexInResult, currentBit, var, prev, lowerCase, preImage);
		transitions[currentBit] = 'X';
	}
	// things that do not contain lower case
	else if ( (transitions[0] == '1' && currentBit == 0) ||
			  (transitions[1] == '0' && currentBit == 1) ||
			  (currentBit == 2 && ((transitions[2] == '1' && lowerCase) || (transitions[2] == '0' && !lowerCase))) ||
			  (transitions[5] == '1' && transitions[3] == '1' && currentBit == 5) ||
			  (transitions[7] ==  transitions[3] && currentBit == 7)
			 )
	{
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof (char)));
		for (i = 0; i < var; i++){
			result[*indexInResult][i] = transitions[i];
		}
		result[*indexInResult][var] = '0';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
	}
	else if ( (transitions[3] != transitions[4] && (currentBit == 4 )) ||
			  (transitions[3] != transitions[6] && currentBit == 6 ) ||
			  (transitions[3] != transitions[7] && currentBit == 7 ) ||
			  (transitions[5] == '1' && transitions[3] ==  '0' && currentBit == 5)
				 ){
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof(char)));
		for (i = 0; i < var; i++)
			result[*indexInResult][i] = transitions[i];
		// only difference between capital and small is bit number 2
		if (!preImage){
			if (lowerCase)
				result[*indexInResult][2] = '1';
			else
				result[*indexInResult][2] = '0';
        }
		// extrabit should be 1 since we may already have same small letter originally with 0
		result[*indexInResult][var] = '1';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
		if (preImage){
			result[*indexInResult] = (char*) malloc((var+2)*(sizeof(char)));
			for (i = 0; i < var; i++)
				result[*indexInResult][i] = transitions[i];
			// only difference between capital and small is bit number 2
			if (lowerCase)
				result[*indexInResult][2] = '1';
			else
				result[*indexInResult][2] = '0';
			// extrabit should be 1 since we may already have same small letter originally with 0
			result[*indexInResult][var] = '1';//extrabit
			result[*indexInResult][var+1] = '\0';
			(*indexInResult)++;
		}
	}
	else{
			if (currentBit < (var-1)){
				getLowerUpperCaseCharsPrePostHelper(result, transitions, indexInResult, currentBit + 1, var, prev, lowerCase, preImage);
			}
			else
				assert(FALSE);
	}

}

void Automaton::getLowerUpperCaseCharsPrePost(char* transitions, int var, char** result, int* pSize, boolean lowerCase, boolean preImage){
	int indexInResult = 0;
	char* prev = (char*) malloc(var*(sizeof(char)));
	getLowerUpperCaseCharsPrePostHelper(result, transitions, &indexInResult, 0, var, prev, lowerCase, preImage);
	*pSize = indexInResult;
}

DFA* Automaton::dfaPrePostToLowerUpperCaseHelper(DFA* M, int var, int* oldIndices, boolean lowerCase, boolean preImage){
	DFA *result;
	paths state_paths, pp;
	trace_descr tp;
	int i, j, n, k;
	char *exeps;
	int *to_states;
	int sink;
	long max_exeps;
	char *statuces;
	int len;
	int ns = M->ns;

	bool has_sink = true;

	len = var + 1;
	int* indices = allocateArbitraryIndex(len);

	max_exeps = 1 << len; //maybe exponential

	sink = find_sink(M);
	if(sink < 0) {
		has_sink = false;
		sink = ns;
		ns++;
	}

	char* symbol = (char *) malloc((len + 1) * sizeof(char));//len+1 since we need extra bit
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((ns + 1) * sizeof(char));
	int numOfChars = 1 << len;
	char** charachters = (char**) malloc(numOfChars * (sizeof (char*)));
	int size = 0;


	dfaSetup(ns, len, indices);
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
		while (pp) {
			if (pp->to != sink) {
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp
							= tp->next)
						;
					if (tp) {
						if (tp->value)
							symbol[j] = '1';
						else
							symbol[j] = '0';
					} else
						symbol[j] = 'X';
				}
				symbol[var] = '\0';
				// convert symbol into a list of chars where we replace each capital letter with small letter
				getLowerUpperCaseCharsPrePost(symbol, var, charachters, &size, lowerCase, preImage);
				for (n = 0; n < size; n++)
				{
//						printf("%s, ", charachters[n]);
					to_states[k] = pp->to;
					for (j = 0; j < len; j++)
						exeps[k * (len + 1) + j] = charachters[n][j];
					exeps[k * (len + 1) + len] = '\0';
					free(charachters[n]);
					k++;
				}
//					printf("\n");
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		// if accept state create a self loop on lambda
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink);

		if (M->f[i] == 1)
			statuces[i] = '+';
		else
			statuces[i] = '-';
	}

	// create artificial sink if original dfa did not have one
	if(not has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuces[sink] = '-';
	}

	statuces[ns] = '\0';
	DFA* tmpM = dfaBuild(statuces);
	result = dfaProject(tmpM, ((unsigned)var));
	dfaFree(tmpM);
	tmpM = dfaMinimize(result);
	dfaFree(result);result = NULL;

	free(exeps);
	free(symbol);
	free(to_states);
	free(statuces);
	free(indices);
	free(charachters);

	return tmpM;
}

DFA* Automaton::dfaToLowerCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, TRUE, FALSE);
}

DFA* Automaton::dfaToUpperCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, FALSE, FALSE);
}

DFA* Automaton::dfaPreToLowerCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, FALSE, TRUE);
}

DFA* Automaton::dfaPreToUpperCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, TRUE, TRUE);
}


/*
 * BEGIN LIBSTRANGER REPLACE STUFF
 */

DFA_ptr Automaton::DFAExtendExtrabit(DFA_ptr M, int var) {
	DFA_ptr result_dfa = nullptr,temp_dfa = nullptr;
	trace_descr tp;
	paths state_paths, pp;
	std::vector<std::pair<std::vector<char>,int>> state_exeps;
	int nvar = var+1;
	int sink = find_sink(M);
	int num_states = M->ns;

	// dfa M may not have sink; make necessary preparations
	bool has_sink = true;
	if(sink < 0) {
		sink = num_states;
		num_states++;
		has_sink = false;
	}

	int *indices = GetBddVariableIndices(nvar);
	char* statuses = new char[num_states+1];

	dfaSetup(num_states,nvar,indices);

	for(int i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		while(pp) {
			if(pp->to != sink) {
				std::vector<char> curr(nvar,'X');
				for(unsigned j = 0; j < var; j++) {
					for(tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
					if(tp) {
						if(tp->value) curr[j] = '1';
						else curr[j] = '0';
					}
					else
						curr[j] = 'X';
				}
				// add new bit, set to 0
				curr[var] = '0';
				//curr[var+1] = '0';
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

		if(M->f[i] == 1) {
			statuses[i] = '+';
		} else {
			statuses[i] = '-';
		}
	}

	// if necessary, create new sink state
	if(not has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuses[sink] = '-';
	}

	statuses[num_states] = '\0';
	temp_dfa = dfaBuild(statuses);
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	delete[] statuses;
	return result_dfa;
}


bool Automaton::check_emptiness_minimized(DFA *M){
    return (M->ns == 1 && M->f[M->s] == -1)? true : false;
}

int Automaton::check_emptiness(DFA_ptr M1, int var, int* indices) {
	if (M1->f[M1->s] == 1)
		return false;
    if (M1->ns == 1 && M1->f[M1->s] == -1)
        return true;


	char *satisfyingexample = NULL;
	int i;
	unsigned *uindices = (unsigned *) malloc((var+1) * sizeof(unsigned));

	//conver int to unsigned
	for (i = 0; i < var; i++)
		uindices[i] = (indices[i] <= 0 ? 0 : indices[i]);
	uindices[i] = '\0';

	satisfyingexample = dfaMakeExample(M1, 1, var, uindices);

	mem_free(uindices);
    int result = ((satisfyingexample == NULL) ? 1 : 0);
    free(satisfyingexample);
    return result;
}

int Automaton::check_intersection(DFA_ptr M1, DFA_ptr M2, int var, int* indices) {
	DFA *M;
	int result;
	M = DFAIntersect(M1, M2);
	result = 1 - check_emptiness(M, var, indices);
	dfaFree(M);
	return result;
}

int Automaton::check_equivalence(DFA_ptr M1, DFA_ptr M2, int var, int* indices) {
	DFA *M[4];
	int result, i;

	M[0] = dfaProduct(M1, M2, dfaIMPL);
	M[1] = dfaProduct(M2, M1, dfaIMPL);
	M[2] = DFAIntersect(M[0], M[1]);
	//M[3] = dfa_negate(M[2], var, indices);
	M[3] = DFAComplement(M[2]);
	result = check_emptiness(M[3], var, indices);

	for (i = 0; i < 4; i++)
		dfaFree(M[i]);

	return result;
}

//Assume that 11111111(255) and 11111110(254) are reserved words in ASCII (the length depends on k)
//Sharp1 is 111111111 which will be used as a reserved symbol
char * Automaton::getSharp1(int k) {
	char *str;

	str = (char *) malloc(k + 1);
	str[k] = '\0';
	for (k--; k >= 0; k--) {
		str[k] = '1';
	}
	//printf("String Sharp 1:%s\n", str);
	return str;
}

//Assume that 11111111(255) and 11111110(254) are reserved words in ASCII, (the length depends on k)
//Sharp0 is 111111110 which will be used as a reserved symbol
char * Automaton::getSharp0(int k) {
	char *str;

	str = (char *) malloc(k + 1);
	str[k] = '\0';
	k--;
	str[k] = '0';
	for (k--; k >= 0; k--) {
		str[k] = '1';
	}
	//printf("String Sharp 1:%s\n", str);
	return str;
}

//Sharp1 is 111111111 which will be used as a reserved symbol
//the length is k+1 and the extra bit is set to 1
char * Automaton::getSharp1WithExtraBit(int k) {
	char *str;

	// add one extra bit for later used
	str = (char *) malloc(k + 2);
	str[k + 1] = '\0';
	str[k] = '1'; //the last bit dont care

	for (k--; k >= 0; k--) {
		str[k] = '1';
	}
	//printf("String Sharp 1:%s\n", str);
	return str;
}

//Sharp0 is 111111110 which will be used as a reserved symbol
//the length is k+1 and the extra bit is set to 1
char * Automaton::getSharp0WithExtraBit(int k) {
	char *str;

	// add one extra bit for later used
	str = (char *) malloc(k + 2);
	str[k + 1] = '\0';
	str[k] = '0'; //the last bit dont care
	k--;
	str[k] = '0';
	for (k--; k >= 0; k--) {
		str[k] = '1';
	}
	//printf("String Sharp 0:%s\n", str);
	return str;
}

DFA *Automaton::dfaSharpStringWithExtraBit(int var, int *indices) {

	char *sharp1;
	sharp1 = getSharp1WithExtraBit(var);
	dfaSetup(2, var + 1, indices);
	dfaAllocExceptions(1);
	dfaStoreException(1, sharp1);
	dfaStoreState(0);
	dfaAllocExceptions(0);
	dfaStoreState(1);

	return dfaBuild("-+");
}

//Sharp0 is 111111110 which will be used as a reserved symbol
char * Automaton::getArbitraryStringWithExtraBit(int k) {
	char *str;

	// add one extra bit for later used
	str = (char *) malloc(k + 2);
	str[k + 1] = '\0';
	str[k] = '0'; //the last bit dont care

	for (k--; k >= 0; k--) {
		str[k] = 'X';
	}
	//printf("Arbitrary String :%s\n", str);
	return str;
}

// A DFA that accepts all strings (Sigma*) except 11111111 and 111111110
DFA * Automaton::dfaAllStringASCIIExceptReserveWords(int var, int *indices) {

	dfaSetup(2, var, indices);
	dfaAllocExceptions(2);
	//n = 255; //reserve word for sharp1
	char* sharp1 = getSharp1(var);
	dfaStoreException(1, sharp1);
	free(sharp1); sharp1 = NULL;
	//n = 254;
	char* sharp0 = getSharp0(var);
	dfaStoreException(1, sharp0);
	free(sharp0); sharp0 = NULL;
	dfaStoreState(0);

	dfaAllocExceptions(0);
	dfaStoreState(1);

	return dfaBuild("+-");
}

DFA_ptr Automaton::dfa_star_M_star(DFA *M, int var, int *indices) {
	DFA *result;
	DFA *tmpM;
	paths state_paths, pp;
	trace_descr tp;
	int i, j, k;
	char *exeps;
	char *addedexeps;
	int *to_states;
	int *added_to_states;
	int sink;
	long max_exeps;
	char *statuces;
	int len;
	int ns = M->ns + 1;
	int shift = 1;
	char *arbitrary = getArbitraryStringWithExtraBit(var);
	len = var + 1; //one extra bit

	max_exeps = 1 << len; //maybe exponential

	bool has_sink = true;
	sink = find_sink(M);
	if(sink < 0) {
		has_sink = false;
		sink = ns;
		ns++;
	}
	//assert(sink>-1);
	//printf("\n\n SINK %d\n\n\n", sink);

	dfaSetup(ns, len, indices);
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	addedexeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	to_states = (int *) malloc(max_exeps * sizeof(int));
	added_to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((ns + 1) * sizeof(char));

	//construct the added paths for the initial state
	state_paths = pp = make_paths(M->bddm, M->q[M->s]);
	//printf("\n\n INIT %d \n\n", M1->s);

	k = 0;
	while (pp) {
		if (pp->to != sink) {
			added_to_states[k] = pp->to + shift;
			for (j = 0; j < var; j++) {
				//the following for loop can be avoided if the indices are in order
				for (tp = pp->trace; tp && (tp->index != indices[j]); tp
						= tp->next)
					;
				if (tp) {
					if (tp->value)
						addedexeps[k * (len + 1) + j] = '1';
					else
						addedexeps[k * (len + 1) + j] = '0';
				} else
					addedexeps[k * (len + 1) + j] = 'X';
			}
			addedexeps[k * (len + 1) + var] = '1'; //new path
			addedexeps[k * (len + 1) + len] = '\0';
			k++;
		}
		pp = pp->next;
	}
	kill_paths(state_paths);

	//initial state
	dfaAllocExceptions(k + 1);
	for (k--; k >= 0; k--)
		dfaStoreException(added_to_states[k], addedexeps + k * (len + 1));
	dfaStoreException(0, arbitrary);
	dfaStoreState(sink + shift);
	statuces[0] = '-';

	//M
	for (i = 0; i < M->ns; i++) {

		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;

		while (pp) {
			if (pp->to != sink) {
				to_states[k] = pp->to + shift;
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp
							= tp->next)
						;

					if (tp) {
						if (tp->value)
							exeps[k * (len + 1) + j] = '1';
						else
							exeps[k * (len + 1) + j] = '0';
					} else
						exeps[k * (len + 1) + j] = 'X';
				}
				exeps[k * (len + 1) + var] = '1'; //old value
				exeps[k * (len + 1) + len] = '\0';
				k++;
			}
			pp = pp->next;
		}
		if (M->f[i] == 1) { //add added paths
			dfaAllocExceptions(k + 1);
			for (k--; k >= 0; k--)
				dfaStoreException(to_states[k], exeps + k * (len + 1));
			dfaStoreException(i + shift, arbitrary); //for appending S* for the final state
			dfaStoreState(sink + shift);
			statuces[i + shift] = '+';
		} else {
			dfaAllocExceptions(k);
			for (k--; k >= 0; k--)
				dfaStoreException(to_states[k], exeps + k * (len + 1));
			dfaStoreState(sink + shift);
			statuces[i + shift] = '-';
		}
		kill_paths(state_paths);
	}

	// add artificial sink state if necessary
	if(not has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuces[sink] = '-';
	}

	statuces[ns] = '\0';
	//result = dfaBuild(statuces);
	tmpM = dfaBuild(statuces);
	//dfaPrintVitals(tmpM);
	//printf("Original M\n");
	//dfaPrintVerbose(M);
	//printf("Star M Star\n");
	//dfaPrintVerbose(tmpM);

	result = dfaProject(tmpM, (unsigned) var); //var is the index of the extra bit
	//printf("Projection of Star M Star\n");
	//dfaPrintVerbose(result);

	free(exeps);
	free(addedexeps);
	free(to_states);
	free(added_to_states);
	free(statuces);
    free(arbitrary);
	dfaFree(tmpM);
    tmpM = dfaMinimize(result);
    dfaFree(result);
	return tmpM;
}

DFA_ptr Automaton::dfa_general_replace_extrabit(DFA* M1, DFA* M2, DFA* M3, int var, int* indices){
	DFA_ptr result;
	DFA_ptr M1_bar;
	DFA_ptr M2_bar;
	DFA_ptr M_inter;
	DFA_ptr M_rep;
	DFA_ptr M_sharp = dfaSharpStringWithExtraBit(var, indices);

	M1_bar = dfa_replace_step1_duplicate(M1, var, indices);

	M2_bar = dfa_replace_step2_match_compliment(M2, var, indices);

	M_inter = DFAIntersect(M1_bar, M2_bar);

	if(check_intersection(M_sharp, M_inter, var, indices)>0){
		//replace match patterns
		M_rep = dfa_replace_step3_general_replace(M_inter, M3, var, indices);
		result = dfaProject(M_rep, (unsigned) var);
		dfaFree(M_rep);

	}else { //no match
		result = dfaCopy(M1);
	}
	//printf("free M1_bar\n");
	dfaFree(M1_bar);
	//printf("free M2_bar\n");
	dfaFree(M2_bar);
	//printf("free M_inter\n");
	dfaFree(M_inter);
	//printf("free M_sharp\n");
	dfaFree(M_sharp);

	DFA *tmp = dfaMinimize(result);
	dfaFree(result);
	return tmp;
}


DFA_ptr Automaton::dfa_replace_step1_duplicate(DFA *M, int var, int *indices) {
	DFA* result;
		DFA *temp;
	paths state_paths, pp;
	trace_descr tp;
	int i, j, k;
	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int len, shift, newns, sink;
	char *sharp1;
	char *sharp0;
	sharp1 = getSharp1WithExtraBit(var);
	sharp0 = getSharp0WithExtraBit(var);
	len = var + 1; //one extra bit
	shift = M->ns; // map M2 transitions to new M
	max_exeps = 1 << len; //maybe exponential


	newns = 2 * (M->ns) - 1; //number of states after duplicate. The sink state is not duplicated.
	bool has_sink = true;
	sink = find_sink(M);
	if(sink < 0) {
		// revert the -1 from above, since no sink state originally
		newns++;
		// make new sink state;
		has_sink = false;
		sink = newns;
		newns++;
	}


	dfaSetup(newns, len, indices);
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((newns + 1) * sizeof(char));

	for (i = 0; i < M->ns; i++) {

		if (i != sink) {
			state_paths = pp = make_paths(M->bddm, M->q[i]);
			k = 0;

			while (pp) {
				if (pp->to != sink) {
					to_states[k] = pp->to;
					for (j = 0; j < var; j++) {
						//the following for loop can be avoided if the indices are in order
						for (tp = pp->trace; tp && (tp->index != indices[j]); tp
								= tp->next)
							;

						if (tp) {
							if (tp->value)
								exeps[k * (len + 1) + j] = '1';
							else
								exeps[k * (len + 1) + j] = '0';
						} else
							exeps[k * (len + 1) + j] = 'X';
					}
					exeps[k * (len + 1) + var] = '0'; //old value
					exeps[k * (len + 1) + len] = '\0';
					k++;
				}
				pp = pp->next;
			}
			dfaAllocExceptions(k + 1);
			for (k--; k >= 0; k--)
				dfaStoreException(to_states[k], exeps + k * (len + 1));
			if (i > sink)
				dfaStoreException(i + shift - 1, sharp1);
			else
				dfaStoreException(i + shift, sharp1);

			dfaStoreState(sink);

			if (M->f[i] == 1)
				statuces[i] = '+';
			else
				statuces[i] = '-';
			kill_paths(state_paths);
		} else {
			dfaAllocExceptions(0);
			dfaStoreState(sink);
			statuces[i] = '-';
		}
	}

	for (i = 0; i < M->ns; i++) {
		if (i != sink) {
			state_paths = pp = make_paths(M->bddm, M->q[i]);
			k = 0;

			while (pp) {
				if ((pp->to) != sink) {
					if ((pp->to) > sink)
						to_states[k] = pp->to + shift - 1; //to new state, sink state will be eliminated and hence need -1
					else
						to_states[k] = pp->to + shift; //to new state

					for (j = 0; j < var; j++) {
						//the following for loop can be avoided if the indices are in order
						for (tp = pp->trace; tp && (tp->index != indices[j]); tp
								= tp->next)
							;

						if (tp) {
							if (tp->value)
								exeps[k * (len + 1) + j] = '1';
							else
								exeps[k * (len + 1) + j] = '0';
						} else
							exeps[k * (len + 1) + j] = 'X';
					}
					exeps[k * (len + 1) + var] = '1'; //bar value
					exeps[k * (len + 1) + len] = '\0';
					k++;
				}
				pp = pp->next;
			}

			dfaAllocExceptions(k + 1);
			for (k--; k >= 0; k--)
				dfaStoreException(to_states[k], exeps + k * (len + 1));
			dfaStoreException(i, sharp0);
			dfaStoreState(sink);
			if (M->f[i] == 1)
				statuces[i + shift] = '-';
			else if (M->f[i] == -1)
				statuces[i + shift] = '-';
			else
				statuces[i + shift] = '-';
			kill_paths(state_paths);
		}
	}

	// add artificial sink state if necessary
	if(not has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuces[sink] = '-';
	}

	statuces[newns] = '\0';
	//assert(i+shift == newns);
	temp = dfaBuild(statuces);
	//dfaPrintVitals(result);
	//printf("FREE EXEPS\n");
	free(exeps);
	//printf("FREE ToState\n");
	free(to_states);
	//printf("FREE STATUCES\n");
	free(statuces);
	//dfaFree(tmpM);
		result = dfaMinimize(temp);
		dfaFree(temp);

	return result;
}

DFA_ptr Automaton::dfa_replace_step2_match_compliment(DFA *M, int var, int *indices) {
	DFA *result;
		DFA *temp;
	DFA *M_neg;
	DFA *M_tneg;
	//	DFA *M_e;
	paths state_paths, pp;
	trace_descr tp;
	int i, j, y, k;
	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int len, shift, newns, sink, sink_M_neg;
	char *sharp1;
	char *sharp0;
	sharp1 = getSharp1WithExtraBit(var);
	sharp0 = getSharp0WithExtraBit(var);

	M_tneg = dfa_star_M_star(M, var, indices);

	dfaNegation(M_tneg);

	//Union empty string manually
	//M_neg = dfa_union_empty_M(M_tneg, var, indices);
	DFA_ptr empty_dfa = DFAMakeEmpty(var+1);
	//M_tneg->f[0] = 1;
	M_neg = DFAUnion(M_tneg,empty_dfa);

	dfaFree(empty_dfa);

	sink_M_neg = find_sink(M_neg);
	if (sink_M_neg < 0) {
		//THERE IS no SINK STATES
		//printf("No Sink of M_neg :[%d]\n", sink_M_neg);
		shift = M_neg->ns; // map M transitions to new M
		newns = M->ns + M_neg->ns; //number of states for new M. Note that there maybe no sink state in M_neg.
	} else {
		//THERE IS no SINK STATES
		//printf("Sink of M_neg :[%d] will be removed.\n", sink_M_neg);
		shift = M_neg->ns - 1; // map M transitions to new M
		newns = M->ns + M_neg->ns - 1; //number of states for new M. Note that there maybe no sink state in M_neg.
	}

	len = var + 1; //one extra bit for bar

	max_exeps = 1 << len; //maybe exponential

	bool has_sink = true;
	sink = find_sink(M);
	if(sink < 0) {
		has_sink = false;
		sink = newns;
		newns++;
	} else {
		sink += shift;
	}

	dfaSetup(newns, len, indices);
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((newns + 1) * sizeof(char));

	//the initial state
	for (i = 0, y = 0; i < M_neg->ns; i++) {
		if (i != sink_M_neg) {
			state_paths = pp = make_paths(M_neg->bddm, M_neg->q[i]);
			k = 0;

			while (pp) {
				if (pp->to != sink_M_neg) {
					if (pp->to > sink_M_neg)
						to_states[k] = pp->to - 1;
					else
						to_states[k] = pp->to;
					for (j = 0; j < var; j++) {
						//the following for loop can be avoided if the indices are in order
						for (tp = pp->trace; tp && (tp->index != indices[j]); tp
								= tp->next)
							;

						if (tp) {
							if (tp->value)
								exeps[k * (len + 1) + j] = '1';
							else
								exeps[k * (len + 1) + j] = '0';
						} else
							exeps[k * (len + 1) + j] = 'X';
					}
					exeps[k * (len + 1) + var] = '0'; //original value
					exeps[k * (len + 1) + len] = '\0';
					k++;
				}
				pp = pp->next;
			}

			if (M_neg->f[i] == 1) {
				dfaAllocExceptions(k + 1);
				for (k--; k >= 0; k--)
					dfaStoreException(to_states[k], exeps + k * (len + 1));
				dfaStoreException(shift, sharp1);
				dfaStoreState(sink);
				statuces[y] = '+';
			} else {
				dfaAllocExceptions(k);
				for (k--; k >= 0; k--)
					dfaStoreException(to_states[k], exeps + k * (len + 1));
				dfaStoreState(sink);
				if (M_neg->f[i] == -1)
					statuces[y + shift] = '-';
				else
					statuces[y + shift] = '-';
			}
			kill_paths(state_paths);
			y++; //y is the number of visited non sink states
		}
		/*		else {
		 //if M_neg exists sink state
		 dfaAllocExceptions(0);
		 dfaStoreState(sink);
		 statuces[i]='0';
		 }
		 */

	}
//	if (sink_M_neg < 0)
//		assert(y==M_neg->ns);
//	else
//		assert(y+1==M_neg->ns);

	for (i = 0; i < M->ns; i++) {
		if (i != sink - shift) {
			state_paths = pp = make_paths(M->bddm, M->q[i]);
			k = 0;

			while (pp) {
				if (pp->to != sink - shift) {
					to_states[k] = pp->to + shift;
					for (j = 0; j < var; j++) {
						//the following for loop can be avoided if the indices are in order
						for (tp = pp->trace; tp && (tp->index != indices[j]); tp
								= tp->next)
							;

						if (tp) {
							if (tp->value)
								exeps[k * (len + 1) + j] = '1';
							else
								exeps[k * (len + 1) + j] = '0';
						} else
							exeps[k * (len + 1) + j] = 'X';
					}
					exeps[k * (len + 1) + var] = '1'; //bar value
					exeps[k * (len + 1) + len] = '\0';
					k++;
				}
				pp = pp->next;
			}

			if (M->f[i] == 1) {
				dfaAllocExceptions(k + 1);
				for (k--; k >= 0; k--)
					dfaStoreException(to_states[k], exeps + k * (len + 1));
				dfaStoreException(0, sharp0); //add sharp1 to the initial state of M
				dfaStoreState(sink);
				statuces[i + shift] = '-';
			} else {
				dfaAllocExceptions(k);
				for (k--; k >= 0; k--)
					dfaStoreException(to_states[k], exeps + k * (len + 1));
				dfaStoreState(sink);
				if (M->f[i] == -1)
					statuces[i + shift] = '-';
				else
					statuces[i + shift] = '-';
			}
			kill_paths(state_paths);
		} else { //sink state
			dfaAllocExceptions(0);
			dfaStoreState(sink);
			statuces[i + shift] = '-';
		}
	}

	// add artificial sink state if necessary
	if(not has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuces[sink] = '-';
	}

	statuces[newns] = '\0';
	//assert(i+shift == newns);
	temp = dfaBuild(statuces);
	//dfaPrintVitals(result);
	//printf("FREE EXEPS\n");
	free(exeps);
	//printf("FREE ToState\n");
	free(to_states);
	//printf("FREE STATUCES\n");
	free(statuces);
	dfaFree(M_neg);
	dfaFree(M_tneg);
	//dfaFree(M_e);
		result = dfaMinimize(temp);
		dfaFree(temp);
	return result;
}

DFA_ptr Automaton::dfa_replace_step3_general_replace(DFA *M, DFA* Mr, int var, int *indices)
{
  DFA *result0 = NULL;
  DFA *result1 = NULL;
  DFA *result2 = NULL;
  DFA *result = NULL;
  DFA *tmp = NULL;

  if(Mr->f[M->s]==1){
    //printf("Replacement [%s]!\n", str);
    result0 = dfa_replace_delete(M, var, indices);
    result = result0;
  }


  tmp = DFAIntersect(Mr, dfaDot(var, indices));
  if(!check_emptiness(tmp, var, indices)){
    result1 = dfa_replace_M_dot(M, tmp, var, indices);
    if(result){
      result = DFAUnion(result, result1);
      dfaFree(result0);
      dfaFree(result1);
    }
    else result = result1;
  }

  dfaFree(tmp);
  DFA_ptr dfa_sigma_c1_to_c2 = DFAMakeAcceptingAnyAfterLength(2,var);

  //tmp = DFAIntersect(Mr, dfaSigmaC1toC2(2, -1, var, indices));
  tmp = DFAIntersect(Mr, dfa_sigma_c1_to_c2);
  dfaFree(dfa_sigma_c1_to_c2);

  if(!check_emptiness(tmp, var, indices)){
    //replace rest rather than single character
    result2 = dfa_replace_M_arbitrary(M, tmp, var, indices);

   if(result){
     result1 = result;
     result = DFAUnion(result1, result2);
     dfaFree(result1);
     dfaFree(result2);
   }
   else result = result2;
  }
  dfaFree(tmp);
  return result;
} //END dfa_replace_stpe3_general_replace

//Replace any c \in {sharp1} \vee bar \vee {sharp2} with \epsilon (Assume 00000000000)
DFA_ptr Automaton::dfa_replace_delete(DFA *M, int var, int *oldindices)
{
      DFA *result = NULL;
  DFA *tmpM2 = NULL;
  DFA *tmpM1 = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, o, z, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var;
  int sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;

  //printf("Start get match exclude\n");
  pairs = get_match_exclude_self(M, var, indices); //for deletion, exclude self state from the closure
  //printf("End get match exclude\n");
  maxCount = get_maxcount(pairs, M->ns);
  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    //printf("Deletion [insert auxiliary bits]!\n");
    aux = get_hsig(maxCount);
    len = var+aux;
    auxbit = (char *) malloc(aux*sizeof(char));
    indices = allocateArbitraryIndex(len);
  }

  max_exeps=1<<len; //maybe exponential

  bool has_sink = true;
  int ns = M->ns;;
  sink=find_sink(M);
  if(sink < 0) {
  	has_sink = false;
  	sink = ns;
  	ns++;
  }

  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i


  dfaSetup(M->ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));


  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {//it is bar value
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0';
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;
	  if(pairs[pp->to]!=NULL && pairs[pp->to]->count>0){ //need to add extra edges to states in reachable closure
	    o=k-1; //the original path
	    for(z=0, tmp=pairs[pp->to]->head;z<pairs[pp->to]->count; z++, tmp = tmp->next){
	      to_states[k]=tmp->value;
	      for (j = 0; j < var; j++) exeps[k*(len+1)+j]=exeps[o*(len+1)+j];
	      set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	      for (j = var; j < len; j++) { //set to xxxxxxxx100
		exeps[k*(len+1)+j]=auxbit[len-j-1];
	      }
	      k++;
	    }
	  }
	}
      }
      pp = pp->next;
    }//end while

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }

  // add artificial sink state if necessary
  if(not has_sink) {
  	dfaAllocExceptions(0);
  	dfaStoreState(sink);
  	statuces[sink] = '-';
  }

  statuces[ns]='\0';
  tmpM2=dfaBuild(statuces);
  //dfaPrintVitals(result);
  for(i=0; i<aux; i++){
    j=len -i;
    tmpM1 =dfaProject(tmpM2, (unsigned) j);
      dfaFree(tmpM2); tmpM2 = NULL;
    tmpM2 = dfaMinimize(tmpM1);
      dfaFree(tmpM1); tmpM1 = NULL;
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);

  if(maxCount>0) free(auxbit);

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);
  free(pairs);
  result = dfaMinimize(tmpM2);	//MUST BE CAREFUL FOR INDICES..INDICES MAY NOT MATCH!!
    dfaFree(tmpM2);
    return result;

}

//Replace sharp1 bar sharp2 to Mr. Mr accepts a set of single chars
//for all i, if pairs[i]!=NULL, add path to each state in pairs[i]
DFA * Automaton::dfa_replace_M_dot(DFA *M, DFA* Mr, int var, int *oldindices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount = 0;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, z, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var;
  int sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;

  //Get from Mr
  int nc;
  int numchars = count_accepted_chars(Mr);
  char* apath[numchars];
  set_accepted_chars(Mr, apath, numchars, var, indices);

  pairs = get_match(M, var, indices);
  maxCount = get_maxcount(pairs, M->ns);

  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    aux = get_hsig(maxCount);
    //	printf("Replace one char: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
    auxbit = (char *) malloc(aux*sizeof(char));
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
  }



  max_exeps=1<<len; //maybe exponential
  int ns = M->ns;
  bool has_sink = true;
  sink=find_sink(M);
  if(sink < 0) {
  	has_sink = false;
  	sink = ns;
  	ns++;
  }


  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i


  dfaSetup(ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));

  //printf("Before Replace Char\n");
  //dfaPrintVerbose(M);

  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0';
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

	}
      }
      pp = pp->next;
    }//end while

    if(pairs[i]!=NULL && pairs[i]->count>0){ //need to add extra edges to states in reachable closure

      for(z=0, tmp=pairs[i]->head;z< pairs[i]->count; z++, tmp = tmp->next){
	set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	for(nc = 0; nc<numchars; nc++){
	  to_states[k]=tmp->value;
	  for (j = 0; j < var; j++) exeps[k*(len+1)+j]=apath[nc][j];
	  for (j = var; j < len; j++) { //set to xxxxxxxx100
	    exeps[k*(len+1)+j]=auxbit[len-j-1];
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;
	} // end for nc
      }	//end for z
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }

  // add artificial sink state if necessary
  if(not has_sink) {
  	dfaAllocExceptions(0);
  	dfaStoreState(sink);
  	statuces[sink] = '-';
  }

  statuces[ns]='\0';
  result=dfaBuild(statuces);
  //dfaPrintVitals(result);
  for(i=0; i<aux; i++){
    j=len-i;
    tmpM =dfaProject(result, (unsigned) j);
    result = dfaMinimize(tmpM);
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);

  //free(apath);
  for(i=0; i<numchars; i++) free(apath[i]);

  if(maxCount>0){
    free(auxbit);
    free(indices);
  }

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);
  free(pairs);

  return dfaMinimize(result);

}// End dfa_replace_M_dot

//Replace every pairs(i,j), so that i can reach j through sharp1 bar sharp0, to i Mr j,
//where Mr is the replacement, whihc can be an arbitrary DFA accepting words >1
DFA_ptr Automaton::dfa_replace_M_arbitrary(DFA *M, DFA *Mr, int var, int *oldindices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount, numberOfSharp;


  paths state_paths, pp;
  trace_descr tp;
  int i, j, z, n, o, k, numsharp2;
  int s=0;
  char *exeps;
  char *auxexeps=NULL;
  int *to_states;
  int *aux_to_states=NULL;
  long max_exeps;
  char *statuces;
  int len=var;
  int ns, sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;

  int extrastates = Mr->ns; //duplicate states for each sharp pair

  //for out going information in Mr
  char ***binOfOut = (char ***) malloc((Mr->ns)*sizeof(char **)); //the string of the nonsink outgoing edge of each state
  int **toOfOut = (int **) malloc((Mr->ns)*sizeof(int *)); // the destination of the nonsink outgoing edge of each state
  int *numOfOut = (int *) malloc((Mr->ns)*sizeof(int)); // how many nonsink outgoing edges of each state
  int *numOfOutFinal = (int *) malloc((Mr->ns)*sizeof(int)); //how many final outgoing edges of each state

  int *startStates = NULL;



  pairs = get_match(M, var, indices);

  maxCount = get_maxcount(pairs, M->ns);
  numberOfSharp = get_number_of_sharp1_state(pairs, M->ns);


  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges

    aux = get_hsig(maxCount);//get the highest significant bit
    auxbit = (char *) malloc(aux*sizeof(char));//the redundant bits to distinguish outgoing edges
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
    s=0;
    startStates = (int *) malloc(numberOfSharp*sizeof(int));
    for(i =0; i<numberOfSharp; i++){
      startStates[i]=-1; //initially it is -1. There is an error if some of them are not set up later.
    }
    auxexeps=(char *)malloc(maxCount*(len+1)*sizeof(char));
    aux_to_states=(int *)malloc(maxCount*sizeof(int));
  }

  initial_out_info(Mr, numOfOut, numOfOutFinal, binOfOut, toOfOut, var, aux, indices);


  max_exeps=1<<len; //maybe exponential
  ns = M->ns + numberOfSharp*extrastates;

  bool has_sink = true;
  sink=find_sink(M);
  if(sink < 0) {
  	has_sink = false;
  	sink = ns;
  	ns++;
  }



  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
  dfaSetup(ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));



  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0'; //all original paths are set to zero
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

	}
      }
      pp = pp->next;
    }//end while

    if(pairs[i]!=NULL && pairs[i]->count>0){ //need to add extra edges to states in reachable closure
      startStates[s]=i; //pairs[startStates[s]] is the destination that later we shall use for region s
      for(o=0; o<numOfOut[Mr->s]; o++){
	to_states[k]=M->ns+s*(extrastates)+toOfOut[Mr->s][o]; // go to the next state of intial state of  Mr
	for(j = 0; j < var; j++) exeps[k*(len+1)+j]=binOfOut[Mr->s][o][j];
	for(j = var; j< len-1; j++) exeps[k*(len+1)+j] = '0';
	exeps[k*(len+1)+j]='1'; //to distinguish the original path
	exeps[k*(len+1)+len]='\0';
	k++;
      }
      s++;
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);

  }//end for i

  assert(s==numberOfSharp);
  assert(i==M->ns);

  //Add replace states
  for(n=0;n<numberOfSharp; n++){
    assert((pairs[startStates[n]]!=NULL) && (pairs[startStates[n]]->count > 0));
    numsharp2 = pairs[startStates[n]]->count;
    for(i=0; i<Mr->ns; i++){ //internal M (exclude the first and the last char)
      if(numOfOutFinal[i]==0){
	dfaAllocExceptions(numOfOut[i]);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	}
	dfaStoreState(sink);
      }else{//need to add aux edges back to sharp destination, for each edge leads to accepting state
	dfaAllocExceptions(numOfOut[i]+numOfOutFinal[i]*numsharp2);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	  if(Mr->f[toOfOut[i][o]]==1){ //add auxiliary back edges
	    for(z=0, tmp=pairs[startStates[n]]->head;z< numsharp2; z++, tmp = tmp->next){
	      aux_to_states[z]=tmp->value;
	      for (j = 0; j < var; j++) auxexeps[z*(len+1)+j]=binOfOut[i][o][j];
	      set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	      for (j = var; j < len; j++) { //set to xxxxxxxx100
		auxexeps[z*(len+1)+j]=auxbit[len-j-1];
	      }
	      auxexeps[z*(len+1)+len]='\0';
	    }

	    for(z--;z>=0;z--)
	      dfaStoreException(aux_to_states[z],auxexeps+z*(len+1));
	  }
	}
	dfaStoreState(sink);
      }
    }//end for Mr internal
  }

  for(i=M->ns; i<ns; i++) statuces[i]='-';

  // add artificial sink state if necessary
  if(not has_sink) {
  	dfaAllocExceptions(0);
  	dfaStoreState(sink);
  }

  statuces[ns]='\0';
  result=dfaBuild(statuces);

  for(i=0; i<aux; i++){
    j=len-i;

    tmpM =dfaProject(dfaMinimize(result), (unsigned) j);

    dfaFree(result);
    result = dfaMinimize(tmpM);
    dfaFree(tmpM);
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);



  if(maxCount>0){
    free(auxbit);
    free(aux_to_states);
    free(auxexeps);
    free(indices);
    free(startStates);
  }

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);

  for(i=0; i<Mr->ns; i++){
    free(binOfOut[i]);
    free(toOfOut[i]);
  }



  free(binOfOut);
  free(toOfOut);
  free(numOfOut);
  free(numOfOutFinal);

  free(pairs);

  return dfaMinimize(result);

}

struct int_list_type **Automaton::get_match_exclude_self(DFA *M, int var, int *indices) {
	int i, next;
	struct int_list_type **result;
	result = (struct int_list_type **) malloc((M->ns)
			* sizeof(struct int_list_type *));
	for (i = 0; i < M->ns; i++) {
		//printf("Start exist sharp1\n");
		next = exist_sharp1_path(M, i, var);
		//printf("End exist sharp1: state[%d]\n", next);
		if (next > -1) //result[i]= remove_value(reachable_closure(M, next, var, indices), i);
			result[i] = reachable_closure(M, next, var, indices);
		else
			result[i] = new_ilt();
	}
	return result;
}

int Automaton::exist_sharp1_path(DFA *M, int start, int var) {
	paths state_paths, pp;
	trace_descr tp;
	int j, sink;
	int finalflag = 1;
	int *indices = allocateAscIIIndexWithExtraBit(var);
	char *sharp1 = getSharp1WithExtraBit(var);
	//printf("Get Sharp1 %s\n", sharp1);
	sink = find_sink(M);
	//assert(sink>-1);
	//printf("Find sink in sharp1: %d\n", sink);
	//assert(start < M->ns);

	if (start == sink){
        free(indices);
        free(sharp1);
		return -1;
    }
	else {
		state_paths = pp = make_paths(M->bddm, M->q[start]);

		while (pp) {
			if (pp->to != sink) {
				//find the path that may contain 111111111
				for (j = 0; j < var + 1; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != j); tp = tp->next)
						;
					if (tp) {
						if (tp->value) {
							//printf("TP value true\n");
							if (sharp1[j] == '0')
								finalflag = 0;
						} else {
							if (sharp1[j] == '1')
								finalflag = 0;
						}
					}
				}
				if (finalflag != 0) {
					free(indices);
                    free(sharp1);
                    int toState = pp->to;
                    kill_paths(state_paths);
					return toState;
				}
			}
			pp = pp->next;
			finalflag = 1;
		}
        kill_paths(state_paths);
	}
	free(indices);
    free(sharp1);
	return -1;
}

//set less significant bit less priority
//the extra bit has the less priority
int* Automaton::allocateAscIIIndexWithExtraBit(int length) {
	int i;
	int* indices;
	indices = (int *) malloc((length + 1) * sizeof(int));
	for (i = 0; i <= length; i++)
		indices[i] = i;
	return indices;
}

//reachable states from \bar* sharp0;
struct int_list_type * Automaton::reachable_closure(DFA *M, int start, int var,
		int *indices) {

	paths state_paths, pp;
	trace_descr tp;
	int j, sink, current;
	struct int_list_type *worklist = NULL;
	struct int_list_type *finallist = NULL;
	int finalflag = 1;
	char *sharp0 = getSharp0WithExtraBit(var);
	int *visited = (int *) malloc(M->ns * sizeof(int));
	for (j = 0; j < M->ns; j++)
		visited[j] = 0;

	sink = find_sink(M);
	//assert(sink>-1);

	worklist = enqueue(worklist, start);

	while (worklist->count > 0) {
		current = dequeue(worklist);
		visited[current] = 1;
		//assert(current!=-1);
		state_paths = pp = make_paths(M->bddm, M->q[current]);
		while (pp) {
			if (pp->to != sink) {
				//find the path that may contain 111111101
				for (j = 0; j < var + 1; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != j); tp = tp->next)
						;

					if (tp) {
						if (tp->value) {
							if (sharp0[j] == '0')
								finalflag = 0;
						} else {
							if (sharp0[j] == '1')
								finalflag = 0;
						}
					}
				}
				if (finalflag != 0)
					finallist = enqueue(finallist, pp->to);

				for (tp = pp->trace; tp && (tp->index != var); tp = tp->next)
					;
				if (((tp && tp->value) || !tp) && (visited[pp->to] == 0)
						&& (finalflag == 0))
					worklist = enqueue(worklist, pp->to);
			}
			pp = pp->next;
			finalflag = 1;
		}
        kill_paths(state_paths);
	}
    free_ilt(worklist);
    free(visited);
    free(sharp0);
	return finallist;
}

//no duplicate
struct int_list_type * Automaton::enqueue(struct int_list_type *list, int value) {
	if (!check_value(list, value))
		list = add_data(list, new_it(value));
	return list;
}

int Automaton::dequeue(struct int_list_type *list){
	struct int_type *data = NULL;
	int i;
	if ((list == NULL) || (list->count == 0))
		return -1;
	else
		data = list->head;
	if (list->count == 1) {
		list->count = 0;
		list->head = list->tail = NULL;
	} else {
		list->head = list->head->next;
		list->count--;
	}
	i = data->value;
	free(data);
	return i;
}

void Automaton::free_ilt(struct int_list_type *list) {
	int tmp = dequeue(list);
	while (tmp != -1)
		tmp = dequeue(list);
	free(list);
}

struct int_type * Automaton::new_it(int i) {
	struct int_type *tmp;
	tmp = (struct int_type *) malloc(sizeof(struct int_type));
	tmp->value = i;
	tmp->next = NULL;
	return tmp;
}

struct int_list_type * Automaton::new_ilt() {
	struct int_list_type *tmp;
	tmp = (struct int_list_type *) malloc(sizeof(struct int_list_type));
	tmp->count = 0;
	tmp->head = tmp->tail = NULL;
	return tmp;
}

struct int_list_type * Automaton::add_data(struct int_list_type *list, struct int_type *data) {
	if (data == NULL)
		return list;

	if (list == NULL)
		list = new_ilt();
	if (list->count > 0) {
		list->tail->next = data;
		list->tail = list->tail->next;
		list->count++;
	} else {
		list->head = list->tail = data;
		list->count = 1;
	}
	return list;
}

int Automaton::check_value(struct int_list_type *list, int value) {
	struct int_type *tmp = NULL;
	if (list != NULL)
		for (tmp = list->head; tmp != NULL; tmp = tmp->next)
			if (tmp->value == value)
				return 1;
	return 0;
}

//return the max pairs[i]->count
int Automaton::get_maxcount(struct int_list_type **pairs, int size) {
	int i;
	int result = 0;
	for (i = 0; i < size; i++) {
		if (pairs[i] != NULL)
			if (result < pairs[i]->count)
				result = pairs[i]->count;
	}
	return result;
}

//return the position of the highest significant bit
int Automaton::get_hsig(int i) {
	int sig, n;
	n = i;
	for (sig = 0; n > 0; sig++)
		n >>= 1;
	return sig;
}

void Automaton::set_bitvalue(char *bit, int length, int value) {
	int i;
	//	bit = (char *) malloc( length*sizeof(char));
	for (i = 0; i < length; i++)
		if (value & (1 << i))
			bit[i] = '1';
		else
			bit[i] = '0';
//	bit[length] = '\0';//causes buffer overrun
	//	printf("\n added bits: %s\n", bit);
}

int* Automaton::allocateArbitraryIndex(int length) {
	int i;
	int* indices;
	indices = (int *) malloc((length) * sizeof(int));
	for (i = 0; i < length; i++)
		indices[i] = i;
	return indices;
}

// A DFA that accepts only one arbitrary character
DFA * Automaton::dfaDot(int var, int *indices){

   dfaSetup(3,var,indices);

   dfaAllocExceptions(2);
   dfaStoreException(2, getSharp1(var));
   dfaStoreException(2, getSharp0(var));
   dfaStoreState(1);
   dfaAllocExceptions(0);
   dfaStoreState(2);
   dfaAllocExceptions(0);
   dfaStoreState(2);

   return dfaBuild("-+-");
}

int Automaton::count_accepted_chars(DFA* M){
  paths state_paths, pp;
  int k=0;
  int sink = find_sink(M);
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  while (pp){
    if(pp->to!=sink && (M->f[pp->to]==1))  k++;
    pp = pp->next;
  }
  return k;
}



void Automaton::set_accepted_chars(DFA* M,char** apath, int numchars, int var, int* indices){

  paths state_paths, pp;
  trace_descr tp;
  int k=0;
  int j;
  int sink = find_sink(M);
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  while (pp){
    if(pp->to!=sink && (M->f[pp->to]==1)){
      apath[k] = (char *) malloc(var*sizeof(char));
       for (j = 0; j < var; j++) {
	 //the following for loop can be avoided if the indices are in order
	 for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	 if (tp) {
	   if (tp->value) apath[k][j]='1';
	   else apath[k][j]='0';
	 }
	 else
	   apath[k][j]='X';
       }
      k++;
    }
    pp = pp->next;
  }
  //assert(k==numchars); // the number of added apaths shall be equal to numchars
}

struct int_list_type ** Automaton::get_match(DFA *M, int var, int *indices) {
	int i, next;
	struct int_list_type **result;
	result = (struct int_list_type **) malloc((M->ns)
			* sizeof(struct int_list_type *));
	for (i = 0; i < M->ns; i++) {
		next = exist_sharp1_path(M, i, var);
		if (next > -1)
			result[i] = reachable_closure(M, next, var, indices);//result[i]= reachable_closure(M, next, var, indices);
		else
			result[i] = new_ilt();
	}
	return result;
}

int Automaton::get_number_of_sharp1_state(struct int_list_type **pairs, int size) {
	int i;
	int result = 0;
	for (i = 0; i < size; i++)
		if (pairs[i] != NULL && pairs[i]->count > 0)
			result++;

	return result;
}

//Get outgoing information from M and fulfill in
//num: number of outgoing edges
//final: number of outgoing edges to final states
//bin: the binary value along the outgoing edge (add aux bits 0 at the tail)
//to: the destination of the outgoing edge

void Automaton::initial_out_info(DFA* M, int* num, int* final, char*** bin, int** to, int var, int aux, int* indices){

  int i, j, k;
  paths state_paths, pp;
  trace_descr tp;
  int sink = find_sink(M);


  //initialize num

  for(i = 0; i<M->ns; i++){
    k =0;
    state_paths = pp = make_paths(M->bddm, M->q[i]);
    while (pp){
      if(pp->to!=sink)  k++;
      pp = pp->next;
    }
    num[i] = k;
    final[i] = 0;
    kill_paths(state_paths);
  }

  //initialize binary of each outgoing edges

  for(i = 0; i<M->ns; i++){
	  if(num[i]>0){
	  bin[i] = (char **) malloc((num[i])*sizeof(char *));
	  to[i] = (int *) malloc((num[i])*sizeof(int));
	  k=0;
	  state_paths = pp = make_paths(M->bddm, M->q[i]);
	  while (pp){
		  if(pp->to!=sink){

			  bin[i][k]=(char *) malloc((var+aux+1)*sizeof(char)); //may lead to memory leak
			  to[i][k] = pp->to;
			  if(M->f[pp->to] == 1) final[i]++;

			  for (j = 0; j < var; j++) {
				  //the following for loop can be avoided if the indices are in order
				  for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

				  if (tp) {
					  if (tp->value) bin[i][k][j]='1';
					  else bin[i][k][j]='0';
				  }
				  else
					  bin[i][k][j]='X';
			  }
			  for(j=var; j<var+aux; j++) bin[i][k][j]='0';

			  bin[i][k][j]= '\0';//end of string
			  k++;
		  }//end if != sink
		  pp = pp->next;
	  }//end while
	  kill_paths(state_paths);
	  }else{
		  bin[i] = NULL;
		  to[i] = NULL;
	  }
  }

}//end initial_out_info

DFA_ptr Automaton::dfa_pre_replace_str(DFA* M1, DFA* M2, char *str, int var, int* indices){

  DFA *result=NULL;
  DFA *M3 = dfa_construct_string(str, var, indices);
  if((str ==NULL)||strlen(str)==0){
    //printf("Replacement [%s]!\n", str);
    result = dfa_insert_everywhere(M1, M2, var, indices);
  }else {
    //printf("Replacement [%s]!\n", str);
    result = dfa_general_replace_extrabit(M1, M3, DFAUnion(M2, M3), var, indices);
  }
  dfaFree(M3);
  return result;
}

DFA * Automaton::dfa_construct_string(char *reg, int var, int *indices) {
	int i;
	char *finals;
	char* binChar;
	DFA* result;
	int len = (int) strlen(reg);
	finals = (char *) malloc((len + 2) * sizeof(char));
	dfaSetup(len + 2, var, indices);
	for (i = 0; i < len; i++) {
		dfaAllocExceptions(1);
		binChar = bintostr((unsigned long) reg[i], var);
		dfaStoreException(i + 1, binChar);
		free(binChar);
		dfaStoreState(len + 1);
		finals[i] = '-';
	}
	dfaAllocExceptions(0);
	dfaStoreState(len + 1);
	finals[len] = '+';
	//assert(len==i);
	//sink state
	dfaAllocExceptions(0);
	dfaStoreState(len + 1);
	finals[len + 1] = '-';
	result = dfaBuild(finals);
	free(finals);
	return result;
}

/******************************************************************

Insertion:insert Mr at every state of M

I.e., Output M' so that L(M')={ w0c0w1c1w2c2w3 | c0c1c2 \in L(M), wi \in L(Mr) }

******************************************************************/


DFA * Automaton::dfa_insert_M_dot(DFA *M, DFA* Mr, int var, int *indices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var+1;
  int sink;

  //Get from Mr
  int nc;
  int numchars = count_accepted_chars(Mr);
  char* apath[numchars];
  bool has_sink = true;
  int num_states = M->ns;
  set_accepted_chars(Mr, apath, numchars, var, indices);


  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  if(sink < 0) {
  	has_sink = false;
  	sink = num_states;
  	num_states++;
  }



  dfaSetup(num_states, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((num_states+1)*sizeof(char));

  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
				to_states[k]=pp->to;
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

					if (tp) {
						if (tp->value) exeps[k*(len+1)+j]='1';
						else exeps[k*(len+1)+j]='0';
					}
					else
						exeps[k*(len+1)+j]='X';
				}
				exeps[k*(len+1)+j]='0';//old value
				exeps[k*(len+1)+len]='\0';
				k++;
			}
			pp = pp->next;
    }//end while

    if(i!=sink){
      for(nc = 0; nc<numchars; nc++){
				to_states[k]=i;
				for (j = 0; j < var; j++) exeps[k*(len+1)+j]=apath[nc][j];
				exeps[k*(len+1)+j]='1';
				exeps[k*(len+1)+len]='\0';
				k++;
      } // end for nc
    }
    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }

  // if original dfa had no sink, add one
  if(not has_sink) {
  	dfaAllocExceptions(0);
  	dfaStoreState(sink);
  	statuces[sink] = '-';
  }

  statuces[num_states]='\0';
  result=dfaBuild(statuces);
  tmpM =dfaProject(result, (unsigned) len-1);
  result = dfaMinimize(tmpM);

  free(exeps);
  free(to_states);
  free(statuces);

  //free(apath);
  for(i=0; i<numchars; i++) free(apath[i]);

  return result;

}// End dfa_insert_M_dot


DFA * Automaton::dfa_insert_M_arbitrary(DFA *M, DFA *Mr, int var, int *indices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, n, o, k;
  char *exeps;
  char *auxexeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var+1;
  int ns, sink;

  int extrastates = Mr->ns; //duplicate states for each sharp pair

  //for out going information in Mr
  char ***binOfOut = (char ***) malloc((Mr->ns)*sizeof(char **)); //the string of the nonsink outgoing edge of each state
  int **toOfOut = (int **) malloc((Mr->ns)*sizeof(int *)); // the destination of the nonsink outgoing edge of each state
  int *numOfOut = (int *) malloc((Mr->ns)*sizeof(int)); // how many nonsink outgoing edges of each state
  int *numOfOutFinal = (int *) malloc((Mr->ns)*sizeof(int)); //how many final outgoing edges of each state


  initial_out_info(Mr, numOfOut, numOfOutFinal, binOfOut, toOfOut, var, 1, indices);


  max_exeps=1<<len; //maybe exponential
  ns = M->ns + (M->ns)*(extrastates);

  bool has_sink = true;
	sink=find_sink(M);
  if(sink < 0) {
  	has_sink = false;
  	sink = ns;
  	ns++;
  }
  //assert(sink >-1);


  dfaSetup(ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));
  auxexeps=(char *)malloc((len+1)*sizeof(char));


  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;
    // add original paths
    while (pp) {
      if(pp->to!=sink){
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0'; //all original paths are set to zero
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

      }
      pp = pp->next;
    }//end while

    //inser Mr

    for(o=0; o<numOfOut[Mr->s]; o++){
      to_states[k]=M->ns+i*(extrastates)+toOfOut[Mr->s][o]; // go to the next state of intial state of  Mr
      for(j = 0; j < var; j++) exeps[k*(len+1)+j]=binOfOut[Mr->s][o][j];
      exeps[k*(len+1)+j]='1'; //to distinguish the original path
      exeps[k*(len+1)+len]='\0';
      k++;
    }


    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }//end for i

  //assert(i==M->ns);

  //Add replace states
  for(n=0; n< M->ns; n++){
    for(i=0; i<Mr->ns; i++){ //internal M (exclude the first and the last char)
      if(numOfOutFinal[i]==0){
	dfaAllocExceptions(numOfOut[i]);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	}
	dfaStoreState(sink);
      }else{//need to add aux edges back to sharp destination, for each edge leads to accepting state
	dfaAllocExceptions(numOfOut[i]+numOfOutFinal[i]);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	  if(Mr->f[toOfOut[i][o]]==1){ //add auxiliary back edge to n
	    for (j = 0; j < var; j++) auxexeps[j]=binOfOut[i][o][j];
	    auxexeps[j]='1';
	    auxexeps[len]='\0';
	    dfaStoreException(n,auxexeps);
	  }
	}
	dfaStoreState(sink);
      }
    }//end for Mr internal
  }//end for n

  for(i=M->ns; i<ns; i++) statuces[i]='-';
  // add artificial sink state if necessary
  if(not has_sink) {
  	dfaAllocExceptions(0);
  	dfaStoreState(sink);
  }

  statuces[ns]='\0';
  result=dfaBuild(statuces);

  // dfaPrintVerbose(dfaMinimize(result));

  tmpM =dfaProject(dfaMinimize(result), (unsigned) len-1);
  //dfaPrintVerbose(tmpM);

  dfaFree(result);
  result = dfaMinimize(tmpM);
  dfaFree(tmpM);

  free(exeps);
  free(auxexeps);
  free(to_states);
  free(statuces);


  for(i=0; i<Mr->ns; i++){
    if(binOfOut[i]!=NULL) free(binOfOut[i]);
    if(toOfOut[i]!=NULL) free(toOfOut[i]);
  }


  free(binOfOut);
  free(toOfOut);

  free(numOfOut);
  free(numOfOutFinal);

  return dfaMinimize(result);

}//End dfa_insert_M_arbitrary

DFA * Automaton::dfa_insert_everywhere(DFA *M, DFA* Mr, int var, int *indices)
{
  DFA *result1 = NULL;
  DFA *result2 = NULL;
  DFA *result = NULL;
  DFA *tmp = NULL;

  tmp = DFAIntersect(Mr, dfaDot(var, indices));
  if(!check_emptiness(tmp, var, indices)){
    result = dfa_insert_M_dot(M, tmp, var, indices);
  }
  dfaFree(tmp);


  //tmp = DFAIntersect(Mr, dfaSigmaC1toC2(2, -1, var, indices));
  DFA_ptr dfa_sigma_c1_to_c2 = DFAMakeAcceptingAnyAfterLength(2,var);
  tmp = DFAIntersect(Mr, dfa_sigma_c1_to_c2);
  dfaFree(dfa_sigma_c1_to_c2);
  if(!check_emptiness(tmp, var, indices)){
    //replace rest rather than single character
    result2 = dfa_insert_M_arbitrary(M, tmp, var, indices);
    if(result){
     result1 = result;
     result = DFAUnion(result1, result2);
     dfaFree(result1);
     dfaFree(result2);
   }
   else result = result2;
  }
  dfaFree(tmp);
  return result;
} //END dfa_insert_everywhere

} /* namespace Theory */
} /* namespace Vlab */
