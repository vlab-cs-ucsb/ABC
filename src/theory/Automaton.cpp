/*
 * Automaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "Automaton.h"

namespace Vlab {
namespace Theory {

const int Automaton::VLOG_LEVEL = 9;

int Automaton::name_counter = 0;

unsigned long Automaton::next_id = 0;

std::unordered_map<int, int*> Automaton::bdd_variable_indices;

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
    dfaFree(dfa_);
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
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsAcceptingState(" << state_id << ") " << std::boolalpha << result;
  return result;
}
bool Automaton::IsInitialState(const int state_id) const {
  bool result = Automaton::DFAIsInitialState(this->dfa_, state_id);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsInitialState(" << state_id << ") " << std::boolalpha << result;
  return result;
}

bool Automaton::IsSinkState(const int state_id) const {
  bool result = Automaton::DFAIsSinkState(this->dfa_, state_id);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->IsSinkState(" << state_id << ") " << std::boolalpha << result;
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
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->GetInitialState()" << initial_state;
  return initial_state;
}

int Automaton::GetSinkState() const {
  int sink_state = Automaton::DFAGetSinkState(this->dfa_);
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->GetSinkState()" << sink_state;
  return sink_state;
}

Automaton_ptr Automaton::Complement() {
  DFA_ptr complement_dfa = Automaton::DFAComplement(this->dfa_);
  Automaton_ptr complement_auto = MakeAutomaton(complement_dfa, num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << complement_auto->id_ << " = [" << this->id_ << "]->Complement()";
  return complement_auto;
}

Automaton_ptr Automaton::Union(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}
	DFA_ptr union_dfa = Automaton::DFAUnion(this->dfa_, other_automaton->dfa_);
  Automaton_ptr union_auto = MakeAutomaton(union_dfa, num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << union_auto->id_ << " = [" << this->id_ << "]->Union(" << other_automaton->id_ << ")";
  return union_auto;
}

Automaton_ptr Automaton::Intersect(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}
	DFA_ptr intersect_dfa = Automaton::DFAIntersect(this->dfa_, other_automaton->dfa_);
  Automaton_ptr intersect_auto =  MakeAutomaton(intersect_dfa, num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << intersect_auto->id_ << " = [" << this->id_ << "]->Intersect(" << other_automaton->id_ << ")";
  return intersect_auto;
}

Automaton_ptr Automaton::Difference(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}
	DFA_ptr difference_dfa = Automaton::DFADifference(this->dfa_, other_automaton->dfa_);
  Automaton_ptr difference_auto = MakeAutomaton(difference_dfa, num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << difference_auto->id_ << " = [" << this->id_ << "]->Difference(" << other_automaton->id_ << ")";
  return difference_auto;
}

Automaton_ptr Automaton::Concat(Automaton_ptr other_automaton) {
	if(this->num_of_bdd_variables_ != other_automaton->num_of_bdd_variables_) {
		LOG(FATAL) << "number of variables does not match between both automaton!";
	}
	DFA_ptr concat_dfa = Automaton::DFAConcat(this->dfa_,other_automaton->dfa_,num_of_bdd_variables_);
  Automaton_ptr concat_auto = MakeAutomaton(concat_dfa,num_of_bdd_variables_);
  DVLOG(VLOG_LEVEL) << concat_auto->id_ << " = [" << this->id_ << "]->concat(" << other_automaton->id_ << ")";
  return concat_auto;


//	Automaton_ptr left_auto = this, right_auto = other_automaton;
//
//  if (left_auto->IsEmptyLanguage() or right_auto->IsEmptyLanguage()) {
//  	DFA_ptr phi_dfa = DFAMakePhi(num_of_bdd_variables_);
//    return MakeAutomaton(phi_dfa,num_of_bdd_variables_);
//  } else if (left_auto->IsOnlyAcceptingEmptyInput()) {
//    return right_auto->clone();
//  } else if (right_auto->IsOnlyAcceptingEmptyInput()) {
//    return left_auto->clone();
//  }
//
//  // TODO refactor handling empty string case
//  bool left_hand_side_has_emtpy_string = left_auto->IsInitialStateAccepting();
//  bool right_hand_side_has_empty_string = right_auto->IsInitialStateAccepting();
//
//  if (left_hand_side_has_emtpy_string or right_hand_side_has_empty_string) {
//  	DFA_ptr len_dfa = DFAMakeAcceptingAnyAfterLength(0,num_of_bdd_variables_);
//    auto any_string_other_than_empty = MakeAutomaton(len_dfa,num_of_bdd_variables_);
//    if (left_hand_side_has_emtpy_string) {
//      left_auto = left_auto->Intersect(any_string_other_than_empty);
//    }
//
//    if (right_hand_side_has_empty_string) {
//      right_auto = right_auto->Intersect(any_string_other_than_empty);
//    }
//    delete any_string_other_than_empty;
//  }
//
//  int var = left_auto->num_of_bdd_variables_;
//  int* indices = GetBddVariableIndices(var);
//  int tmp_num_of_variables,
//      state_id_shift_amount,
//      expected_num_of_states,
//      sink_state_left_auto,
//      sink_state_right_auto,
//      to_state = 0,
//      loc,
//      i = 0,
//      j = 0;
//
//  bool is_start_state_reachable;
//  paths state_paths = nullptr, pp = nullptr;
//  trace_descr tp = nullptr;
//
//  std::map<std::vector<char>*, int> exceptions_left_auto;
//  std::map<std::vector<char>*, int> exceptions_right_auto;
//  std::map<std::vector<char>*, int> exceptions_fix;
//  std::vector<char>* current_exception = nullptr;
//  char* statuses = nullptr;
//  tmp_num_of_variables = left_auto->num_of_bdd_variables_ + 1; // add one extra bit
//  state_id_shift_amount = left_auto->dfa_->ns;
//  expected_num_of_states = left_auto->dfa_->ns + right_auto->dfa_->ns;
//
//  is_start_state_reachable = TEMPisStartStateReachableFromAnAcceptingState(right_auto->dfa_);
//  if (not is_start_state_reachable) {
//    expected_num_of_states = expected_num_of_states  - 1; // if start state is reachable from an accepting state, it will be merge with accepting states of left hand side
//  }
//  // variable initializations
//  sink_state_left_auto = left_auto->GetSinkState();
//  sink_state_right_auto = right_auto->GetSinkState();
//
//  bool left_sink = true, right_sink = true;
//  int sink = sink_state_left_auto;
//
//  if(sink_state_left_auto < 0 && sink_state_right_auto < 0) {
//    left_sink = right_sink = false;
//    sink = expected_num_of_states;
//    expected_num_of_states++;
//  } else if(sink_state_left_auto < 0) {
//    left_sink = false;
//    sink = sink_state_right_auto + state_id_shift_amount;
//    if(not is_start_state_reachable) {
//      sink--;
//    }
//  } else if(sink_state_right_auto < 0) {
//    right_sink = false;
//  } else {
//    expected_num_of_states--;
//  }
//
//  statuses = new char[expected_num_of_states + 1];
//  int* concat_indices = GetBddVariableIndices(tmp_num_of_variables);
//
//  dfaSetup(expected_num_of_states, tmp_num_of_variables, concat_indices); //sink states are merged
//  state_paths = pp = make_paths(right_auto->dfa_->bddm, right_auto->dfa_->q[right_auto->dfa_->s]);
//  while (pp) {
//    if (!right_sink || pp->to != sink_state_right_auto ) {
//      to_state = pp->to + state_id_shift_amount;
//      // if there is a self loop keep it
//      if (pp->to == (unsigned)right_auto->dfa_->s ) {
//        to_state -= 2;
//      } else {
//        if (left_sink && right_sink && pp->to > (unsigned)sink_state_right_auto ) {
//          to_state--; //to new state, sink state will be eliminated and hence need -1
//        }
//        if ((not is_start_state_reachable) && pp->to > (unsigned)right_auto->dfa_->s) {
//          to_state--; // to new state, init state will be eliminated if init is not reachable
//        }
//      }
//
//      current_exception = new std::vector<char>();
//      for (j = 0; j < right_auto->num_of_bdd_variables_; j++) {
//        //the following for loop can be avoided if the indices are in order
//        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
//        if (tp) {
//          if (tp->value) {
//            current_exception->push_back('1');
//          }
//          else {
//            current_exception->push_back('0');
//          }
//        }
//        else {
//          current_exception->push_back('X');
//        }
//      }
//
//      current_exception->push_back('1'); // new path
//      current_exception->push_back('\0');
//      exceptions_right_auto[current_exception] = to_state;
//    }
//    current_exception = nullptr;
//    tp = nullptr;
//    pp = pp->next;
//  }
//
//  kill_paths(state_paths);
//  state_paths = pp = nullptr;
//
//  for (i = 0; i < left_auto->dfa_->ns; i++) {
//    state_paths = pp = make_paths(left_auto->dfa_->bddm, left_auto->dfa_->q[i]);
//    while (pp) {
//      if (left_sink && pp->to == (unsigned)sink_state_left_auto) {
//        pp = pp->next;
//        continue;
//      }
//      to_state = pp->to;
//      current_exception = new std::vector<char>();
//      for (j = 0; j < left_auto->num_of_bdd_variables_; j++) {
//        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
//        if (tp) {
//          if (tp->value) {
//            current_exception->push_back('1');
//          } else {
//            current_exception->push_back('0');
//          }
//        } else {
//          current_exception->push_back('X');
//        }
//      }
//
//      current_exception->push_back('0'); // add extra bit, '0' is used for the exceptions coming from left auto
//      current_exception->push_back('\0');
//      exceptions_left_auto[current_exception] = to_state;
//      tp = nullptr;
//      pp = pp->next;
//    }
//    current_exception = nullptr;
//    // generate concat automaton
//    if (left_auto->IsAcceptingState(i)) {
//      dfaAllocExceptions(exceptions_left_auto.size() + exceptions_right_auto.size());
//      for (auto it = exceptions_left_auto.begin(); it != exceptions_left_auto.end();) {
//        dfaStoreException(it->second, &*it->first->begin());
//        current_exception = it->first;
//        it = exceptions_left_auto.erase(it);
//        delete current_exception;
//      }
//      for (auto it = exceptions_right_auto.begin(); it != exceptions_right_auto.end();) {
//        dfaStoreException(it->second, &*it->first->begin());
//        current_exception = it->first;
//        it = exceptions_right_auto.erase(it);
//        delete current_exception;
//      }
//
//      dfaStoreState(sink);
//      if (right_auto->IsAcceptingState(0)) {
//        statuses[i]='+';
//      }
//      else {
//        statuses[i]='-';
//      }
//    } else {
//      dfaAllocExceptions(exceptions_left_auto.size());
//      for (auto it = exceptions_left_auto.begin(); it != exceptions_left_auto.end();) {
//        dfaStoreException(it->second, &*it->first->begin());
//        current_exception = it->first;
//        it = exceptions_left_auto.erase(it);
//        delete current_exception;
//      }
//      dfaStoreState(sink);
//      statuses[i] = '-';
//    }
//    current_exception = nullptr;
//    kill_paths(state_paths);
//    state_paths = pp = nullptr;
//  }
//
//  //  initflag is 1 iff init is reached by some state. In this case,
//  for (i = 0; i < right_auto->dfa_->ns; i++) {
//    if (i != sink_state_right_auto ) {
//      if ( i != right_auto->dfa_->s || is_start_state_reachable) {
//        state_paths = pp = make_paths(right_auto->dfa_->bddm, right_auto->dfa_->q[i]);
//        while (pp) {
//          if (!right_sink || pp->to != (unsigned)sink_state_right_auto) {
//            to_state = pp->to + state_id_shift_amount;
//
//            if ( right_sink && left_sink && pp->to > (unsigned)sink_state_right_auto) {
//              to_state--; //to new state, sink state will be eliminated and hence need -1
//            }
//
//            if ( (not is_start_state_reachable) && pp->to > (unsigned)right_auto->dfa_->s) {
//              to_state--; // to new state, init state will be eliminated if init is not reachable
//            }
//
//            current_exception = new std::vector<char>();
//            for (j = 0; j < var; j++) {
//              for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp =tp->next);
//              if (tp) {
//                if (tp->value){
//                  current_exception->push_back('1');
//                }
//                else {
//                  current_exception->push_back('0');
//                }
//              }
//              else {
//                current_exception->push_back('X');
//              }
//            }
//            current_exception->push_back('0'); // old value
//            current_exception->push_back('\0');
//            exceptions_fix[current_exception] = to_state;
//            tp = nullptr;
//            current_exception = nullptr;
//          }
//          pp = pp->next;
//        }
//
//        dfaAllocExceptions(exceptions_fix.size());
//        for (auto it = exceptions_fix.begin(); it != exceptions_fix.end();) {
//          dfaStoreException(it->second, &*it->first->begin());
//          current_exception = it->first;
//          it = exceptions_fix.erase(it);
//          delete current_exception;
//        }
//
//        dfaStoreState(sink);
//
//        loc = state_id_shift_amount + i;
//        if ( (not is_start_state_reachable) && i > right_auto->dfa_->s) {
//          loc--;
//        }
//        if (left_sink && right_sink && i > sink_state_right_auto) {
//          loc--;
//        }
//
//        if ( right_auto->IsAcceptingState(i)) {
//          statuses[loc]='+';
//        } else {
//          statuses[loc]='-';
//        }
//
//        kill_paths(state_paths);
//        state_paths = pp = nullptr;
//      }
//    } else if(!left_sink && right_sink) {
//      dfaAllocExceptions(0);
//      dfaStoreState(sink);
//      statuses[sink] = '-';
//    }
//  }
//
//  if(!right_sink && !left_sink) {
//    dfaAllocExceptions(0);
//    dfaStoreState(sink);
//    statuses[sink] = '-';
//  }
//
//  statuses[expected_num_of_states]='\0';
//
//  DFA_ptr concat_dfa = dfaBuild(statuses);
//  delete[] statuses; statuses = nullptr;
//  delete[] concat_indices; concat_indices = nullptr;
//  DFA_ptr tmp_dfa = dfaProject(concat_dfa, (unsigned) var);
//  dfaFree(concat_dfa);
//  concat_dfa = dfaMinimize(tmp_dfa);
//  dfaFree(tmp_dfa); tmp_dfa = nullptr;
//
//  auto concat_auto = MakeAutomaton(concat_dfa, num_of_bdd_variables_);
//
//  if (left_hand_side_has_emtpy_string) {
//    auto tmp_auto = concat_auto;
//    concat_auto = tmp_auto->Union(other_automaton);
//    delete tmp_auto;
//    delete left_auto; left_auto = nullptr;
//  }
//
//  if (right_hand_side_has_empty_string) {
//    auto tmp_auto = concat_auto;
//    concat_auto = tmp_auto->Union(this);
//    delete tmp_auto;
//    delete right_auto; right_auto = nullptr;
//  }
//
//  DVLOG(VLOG_LEVEL) << concat_auto->id_ << " = [" << this->id_ << "]->concat(" << other_automaton->id_ << ")";
//
//  return concat_auto;
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

bool Automaton::DFAIsMinimizedEmtpy(const DFA_ptr minimized_dfa) {
    return (minimized_dfa->ns == 1 && minimized_dfa->f[minimized_dfa->s] == -1)? true : false;
}

// TODO implement general is empty function
bool Automaton::DFAIsEmpty(const DFA_ptr dfa) {
  bool result = false;
  for (int s = 0; s < dfa->ns; ++s) {
    if (DFAIsAcceptingState(dfa, s)) {
      // check if the accepting state is reachable
      LOG(FATAL) << "Not implemented";
    }
  }
  return result;
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
  char *statuses = new char[number_of_states];
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

  DFA_ptr result_dfa = dfaBuild(statuses);
  delete[] statuses;
  return result_dfa;
}

DFA_ptr Automaton::DFAMakeAcceptingAnyAfterLength(const int length, const int number_of_bdd_variables) {
  CHECK(length >= 0);
  // 1 initial state
  const int number_of_states = length + 1;
  char *statuses = new char[number_of_states];
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

DFA_ptr Automaton::DFAConcat(const DFA_ptr dfa1, const DFA_ptr dfa2, const int number_of_bdd_variables) {
  if (DFAIsMinimizedEmtpy(dfa1) or DFAIsMinimizedEmtpy(dfa2)) {
    return DFAMakeEmpty(number_of_bdd_variables);
  } else if (DFAIsMinimizedOnlyAcceptingEmptyInput(dfa1)) {
    return dfaCopy(dfa2);
  } else if (DFAIsMinimizedOnlyAcceptingEmptyInput(dfa2)) {
    return dfaCopy(dfa1);
  }

  // TODO refactor handling empty string case
  bool left_hand_side_accepts_emtpy_input = DFAIsAcceptingState(dfa1, dfa1->s);
  bool right_hand_side_accepts_empty_input = DFAIsAcceptingState(dfa2, dfa2->s);

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

  std::map<std::vector<char>*, int> exceptions_left_auto;
  std::map<std::vector<char>*, int> exceptions_right_auto;
  std::map<std::vector<char>*, int> exceptions_fix;
  std::vector<char>* current_exception = nullptr;
  char* statuses = nullptr;
  tmp_num_of_variables = number_of_bdd_variables + 1; // add one extra bit
  state_id_shift_amount = left_dfa->ns;
  expected_num_of_states = left_dfa->ns + right_dfa->ns;

  is_start_state_reachable = TEMPisStartStateReachableFromAnAcceptingState(right_dfa);
  if (not is_start_state_reachable) {
    expected_num_of_states = expected_num_of_states  - 1; // if start state is reachable from an accepting state, it will be merge with accepting states of left hand side
  }
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
    if(not is_start_state_reachable) {
      sink--;
    }
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
      to_state = pp->to + state_id_shift_amount;
      // if there is a self loop keep it
      if (pp->to == (unsigned)right_dfa->s ) {
        to_state -= 2;
      } else {
        if (left_sink && right_sink && pp->to > (unsigned)sink_state_right_auto ) {
          to_state--; //to new state, sink state will be eliminated and hence need -1
        }
        if ((not is_start_state_reachable) && pp->to > (unsigned)right_dfa->s) {
          to_state--; // to new state, init state will be eliminated if init is not reachable
        }
      }

      current_exception = new std::vector<char>();
      for (j = 0; j < number_of_bdd_variables; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            current_exception->push_back('1');
          }
          else {
            current_exception->push_back('0');
          }
        }
        else {
          current_exception->push_back('X');
        }
      }

      current_exception->push_back('1'); // new path
      current_exception->push_back('\0');
      exceptions_right_auto[current_exception] = to_state;
    }
    current_exception = nullptr;
    tp = nullptr;
    pp = pp->next;
  }

  kill_paths(state_paths);
  state_paths = pp = nullptr;

  for (i = 0; i < dfa1->ns; i++) {
    state_paths = pp = make_paths(dfa1->bddm, dfa1->q[i]);
    while (pp) {
      if (left_sink && pp->to == (unsigned)sink_state_left_auto) {
        pp = pp->next;
        continue;
      }
      to_state = pp->to;
      current_exception = new std::vector<char>();
      for (j = 0; j < number_of_bdd_variables; j++) {
        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            current_exception->push_back('1');
          } else {
            current_exception->push_back('0');
          }
        } else {
          current_exception->push_back('X');
        }
      }

      current_exception->push_back('0'); // add extra bit, '0' is used for the exceptions coming from left auto
      current_exception->push_back('\0');
      exceptions_left_auto[current_exception] = to_state;
      tp = nullptr;
      pp = pp->next;
    }
    current_exception = nullptr;
    // generate concat automaton
    if (DFAIsAcceptingState(dfa1,i)) {
      dfaAllocExceptions(exceptions_left_auto.size() + exceptions_right_auto.size());
      for (auto it = exceptions_left_auto.begin(); it != exceptions_left_auto.end();) {
        dfaStoreException(it->second, &*it->first->begin());
        current_exception = it->first;
        it = exceptions_left_auto.erase(it);
        delete current_exception;
      }
      for (auto it = exceptions_right_auto.begin(); it != exceptions_right_auto.end();) {
        dfaStoreException(it->second, &*it->first->begin());
        current_exception = it->first;
        it = exceptions_right_auto.erase(it);
        delete current_exception;
      }

      dfaStoreState(sink);
      if (DFAIsAcceptingState(dfa2,0)) {
        statuses[i]='+';
      }
      else {
        statuses[i]='-';
      }
    } else {
      dfaAllocExceptions(exceptions_left_auto.size());
      for (auto it = exceptions_left_auto.begin(); it != exceptions_left_auto.end();) {
        dfaStoreException(it->second, &*it->first->begin());
        current_exception = it->first;
        it = exceptions_left_auto.erase(it);
        delete current_exception;
      }
      dfaStoreState(sink);
      statuses[i] = '-';
    }
    current_exception = nullptr;
    kill_paths(state_paths);
    state_paths = pp = nullptr;
  }

  //  initflag is 1 iff init is reached by some state. In this case,
  for (i = 0; i < dfa2->ns; i++) {
    if (i != sink_state_right_auto ) {
      if ( i != dfa2->s || is_start_state_reachable) {
        state_paths = pp = make_paths(dfa2->bddm, dfa2->q[i]);
        while (pp) {
          if (!right_sink || pp->to != (unsigned)sink_state_right_auto) {
            to_state = pp->to + state_id_shift_amount;

            if ( right_sink && left_sink && pp->to > (unsigned)sink_state_right_auto) {
              to_state--; //to new state, sink state will be eliminated and hence need -1
            }

            if ( (not is_start_state_reachable) && pp->to > (unsigned)dfa2->s) {
              to_state--; // to new state, init state will be eliminated if init is not reachable
            }

            current_exception = new std::vector<char>();
            for (j = 0; j < number_of_bdd_variables; j++) {
              for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp =tp->next);
              if (tp) {
                if (tp->value){
                  current_exception->push_back('1');
                }
                else {
                  current_exception->push_back('0');
                }
              }
              else {
                current_exception->push_back('X');
              }
            }
            current_exception->push_back('0'); // old value
            current_exception->push_back('\0');
            exceptions_fix[current_exception] = to_state;
            tp = nullptr;
            current_exception = nullptr;
          }
          pp = pp->next;
        }

        dfaAllocExceptions(exceptions_fix.size());
        for (auto it = exceptions_fix.begin(); it != exceptions_fix.end();) {
          dfaStoreException(it->second, &*it->first->begin());
          current_exception = it->first;
          it = exceptions_fix.erase(it);
          delete current_exception;
        }

        dfaStoreState(sink);

        loc = state_id_shift_amount + i;
        if ( (not is_start_state_reachable) && i > dfa2->s) {
          loc--;
        }
        if (left_sink && right_sink && i > sink_state_right_auto) {
          loc--;
        }

        if (DFAIsAcceptingState(dfa2,i)) {
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
  }

  if(!right_sink && !left_sink) {
    dfaAllocExceptions(0);
    dfaStoreState(sink);
    statuses[sink] = '-';
  }

  statuses[expected_num_of_states]='\0';

  DFA_ptr concat_dfa = dfaBuild(statuses);
  delete[] statuses; statuses = nullptr;
  delete[] concat_indices; concat_indices = nullptr;
  DFA_ptr tmp_dfa = dfaProject(concat_dfa, (unsigned) number_of_bdd_variables);
  dfaFree(concat_dfa);
  concat_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa); tmp_dfa = nullptr;

  //auto concat_auto = new StringAutomaton(concat_dfa, num_of_bdd_variables_);

//  if (left_hand_side_accepts_emtpy_input) {
//    auto tmp_auto = concat_auto;
//    concat_auto = tmp_auto->Union(other_auto);
//    delete tmp_auto;
//    delete left_auto; left_auto = nullptr;
//  }
//
//  if (right_hand_side_accepts_empty_input) {
//    auto tmp_auto = concat_auto;
//    concat_auto = tmp_auto->Union(this);
//    delete tmp_auto;
//    delete right_auto; right_auto = nullptr;
//  }

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

  //DVLOG(VLOG_LEVEL) << concat_auto->id_ << " = [" << this->id_ << "]->concat(" << other_auto->id_ << ")";

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
  count_matrix.insert(this->dfa_->ns, this->dfa_->ns) = 1; // allows us to count all lengths up to given bound
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
  Table *table = tableInit();

  /* remove all marks in a->bddm */
  bdd_prepare_apply1(this->dfa_->bddm);

  /* build table of tuples (idx,lo,hi) */
  for (int i = 0; i < this->dfa_->ns; i++) {
    _export(this->dfa_->bddm, this->dfa_->q[i], table);
  }

  /* renumber lo/hi pointers to new table ordering */
  for (unsigned i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx != -1) {
      table->elms[i].lo = bdd_mark(this->dfa_->bddm, table->elms[i].lo) - 1;
      table->elms[i].hi = bdd_mark(this->dfa_->bddm, table->elms[i].hi) - 1;
    }
  }

  out << "digraph MONA_DFA_BDD {\n"
          "  center = true;\n"
          "  size = \"100.5,70.5\"\n"
//      "  orientation = landscape;\n"
          "  node [shape=record];\n"
          "   s1 [shape=record,label=\"";

  for (int i = 0; i < this->dfa_->ns; i++) {
    out << "{" << this->dfa_->f[i] << "|<" << i << "> " << i << "}";
    if ((unsigned) (i + 1) < table->noelems) {
      out << "|";
    }
  }
  out << "\"];" << std::endl;

  out << "  node [shape = circle];";
  for (unsigned i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx != -1) {
      out << " " << i << " [label=\"" << table->elms[i].idx << "\"];";
    }
  }

  out << "\n  node [shape = box];";
  for (unsigned i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx == -1) {
      out << " " << i << " [label=\"" << table->elms[i].lo << "\"];";
    }
  }
  out << std::endl;

  for (int i = 0; i < this->dfa_->ns; i++) {
    out << " s1:" << i << " -> " << bdd_mark(this->dfa_->bddm, this->dfa_->q[i]) - 1 << " [style=bold];\n";
  }

  for (unsigned i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx != -1) {
      int lo = table->elms[i].lo;
      int hi = table->elms[i].hi;
      out << " " << i << " -> " << lo << " [style=dashed];\n";
      out << " " << i << " -> " << hi << " [style=filled];\n";
    }
  }
  out << "}" << std::endl;
  tableFree(table);
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

} /* namespace Theory */
} /* namespace Vlab */
