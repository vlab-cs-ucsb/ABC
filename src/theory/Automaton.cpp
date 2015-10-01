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

unsigned long Automaton::trace_id = 0;

const std::string Automaton::Name::NONE = "none";
const std::string Automaton::Name::BOOL = "BoolAutomaton";
const std::string Automaton::Name::INT = "IntAutomaton";
const std::string Automaton::Name::INTBOOl = "IntBoolAutomaton";
const std::string Automaton::Name::STRING = "StringAutomaton";

Automaton::Automaton(Automaton::Type type)
        : type(type), dfa(nullptr), num_of_variables(0), variable_indices(nullptr), id (Automaton::trace_id++) {
}

Automaton::Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables)
        : type(type), dfa(dfa), num_of_variables(num_of_variables), id (Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables);
}

Automaton::Automaton(const Automaton& other)
        : type(other.type), dfa(dfaCopy(other.dfa)), num_of_variables(other.num_of_variables), id (Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables);
}

Automaton::~Automaton() {
  dfaFree(dfa);
  dfa = nullptr;
  delete variable_indices;
  //  DVLOG(VLOG_LEVEL) << "delete " << " [" << this->id << "]";
}

//Automaton_ptr Automaton::clone() const {
//  return new Automaton(*this);
//}

std::string Automaton::str() const {
  switch (type) {
  case Automaton::Type::NONE:
    return Automaton::Name::NONE;
  case Automaton::Type::BOOL:
    return Automaton::Name::BOOL;
  case Automaton::Type::INT:
    return Automaton::Name::INT;
  case Automaton::Type::INTBOOl:
    return Automaton::Name::INTBOOl;
  case Automaton::Type::STRING:
    return Automaton::Name::STRING;
  default:
    LOG(FATAL)<< "Unknown automaton type!";
    return "";
  }
}

Automaton::Type Automaton::getType() const {
  return type;
}

/**
 * TODO Needs complete refactoring, has a lot of room for improvements
 * especially in libstranger function calls
 */
bool Automaton::checkEquivalence(Automaton_ptr other_auto) {
  DFA *M[4];
  int result, i;

  M[0] = dfaProduct(this->dfa, other_auto->dfa, dfaIMPL);
  M[1] = dfaProduct(other_auto->dfa, this->dfa, dfaIMPL);
  M[2] = dfa_intersect(M[0], M[1]);
  dfaFree(M[0]); M[0] = nullptr;
  dfaFree(M[1]); M[1] = nullptr;
  M[3] = dfa_negate(M[2], num_of_variables, variable_indices);
  result = check_emptiness(M[3], num_of_variables, variable_indices);
  dfaFree(M[2]); M[2] = nullptr;
  dfaFree(M[3]); M[3] = nullptr;

  return result;
}

/**
 * TODO implement this again independent of libstranger
 */
bool Automaton::isEmptyLanguage() {
  bool result;
  int i = check_emptiness(this->dfa, num_of_variables, variable_indices);
  result = (i == 1);
  DVLOG(VLOG_LEVEL) << "[" << this->id << "]->isEmptyLanguage? " << std::boolalpha << result;
  return result;
}

bool Automaton::isInitialStateAccepting() {
  return ((this->dfa->f[this->dfa->s]) == 1) ? true : false;
}

bool Automaton::isOnlyInitialStateAccepting() {
  if (not isInitialStateAccepting()) {
    return false;
  }

  for (int s = 0; s < this->dfa->ns; s++) {
    if (s != this->dfa->s and isAcceptingState(s)) {
      return false;
    } else if (hasNextStateFrom(s, this->dfa->s)) {
      return false;
    }
  }
  return true;
}

bool Automaton::isAcceptingSingleWord() {
  int sink_state = getSinkState(),
      curr_state = -1,
      num_of_accepting_paths = 0;
  std::stack<int> state_path;
  std::set<int>* next_states = nullptr;

  state_path.push(this->dfa->s);
  while (not state_path.empty()) {
    curr_state = state_path.top(); state_path.pop();
    if (this->isAcceptingState(curr_state)) {
      ++num_of_accepting_paths;
    }
    if (num_of_accepting_paths > 1) {
      return false;
    }
    next_states = this->getNextStates(curr_state);
    next_states->erase(sink_state);
    for (int next_state : *next_states) {
      state_path.push(next_state);
    }
    delete next_states; next_states = nullptr;
  }

  return (num_of_accepting_paths == 1);
}

std::ostream& operator<<(std::ostream& os, const Automaton& automaton) {
  return os << automaton.str();
}

DFA_ptr Automaton::makePhi(int num_of_variables, int* variable_indices) {
  DFA_ptr non_accepting_dfa = nullptr;
  std::array<char, 1> statuses { '-' };
  dfaSetup(1, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(0);
  non_accepting_dfa = dfaBuild(&*statuses.begin());
  return non_accepting_dfa;
}

int* Automaton::getIndices(int num_of_variables, int extra_num_of_variables) {
  int* indices = nullptr;
  int size = num_of_variables + extra_num_of_variables;

  indices = new int[size];
  for (int i = 0; i < size; i++) {
    indices[i] = i;
  }

  return indices;
}

unsigned* Automaton::getIndices(unsigned num_of_variables, unsigned extra_num_of_variables) {
  unsigned* indices = nullptr;
  unsigned size = num_of_variables + extra_num_of_variables;

  indices = new unsigned[size];
  for (unsigned i = 0; i < size; i++) {
    indices[i] = i;
  }

  return indices;
}

/**
 * That function replaces the getSharp1WithExtraBit and
 * getSharp0WithExtraBit.
 * @return binary representation of reserved word
 */
std::vector<char> Automaton::getReservedWord(char last_char, int length, bool extra_bit) {
  std::vector<char> reserved_word;

  int i;
  for (i = 0; i < length - 1; i++) {
    reserved_word.push_back('1');
  }
  if (extra_bit) {
    reserved_word.push_back('1');
  }
  reserved_word.push_back(last_char);
  reserved_word.push_back('\0');

  return reserved_word;
}

void Automaton::minimize() {
  DFA_ptr tmp = this->dfa;
  this->dfa = dfaMinimize(tmp);
  delete tmp;
  DVLOG(VLOG_LEVEL) << this->id << " = [" << this->id << "]->minimize()";
}

void Automaton::project(unsigned index) {
  DFA_ptr tmp = this->dfa;
  this->dfa = dfaProject(tmp, index);
  delete tmp;
  this->num_of_variables = index;
  delete this->variable_indices;
  this->variable_indices = getIndices(num_of_variables);
  DVLOG(VLOG_LEVEL) << this->id << " = [" << this->id << "]->project()";
}

bool Automaton::isSinkState(int state_id) {
  return (bdd_is_leaf(this->dfa->bddm, this->dfa->q[state_id])
      and bdd_leaf_value(this->dfa->bddm, this->dfa->q[state_id])
      and this->dfa->f[state_id] == -1);
}

bool Automaton::isAcceptingState(int state_id) {
  return (this->dfa->f[state_id] == 1);
}

/**
 * @returns sink state number if exists, -1 otherwise
 */
int Automaton::getSinkState() {
  for (int i = 0; i < this->dfa->ns; i++) {
    if (isSinkState(i)) {
      return i;
    }
  }
  return -1;
}

/**
 * @returns true if a start state is reachable from an accepting state, false otherwise
 */
bool Automaton::isStartStateReachable() {
  paths state_paths, pp;
  for (int i = 0; i < this->dfa->ns; i++) {
    if (isAcceptingState(i)) {
      state_paths = pp = make_paths(this->dfa->bddm, this->dfa->q[i]);
      while (pp) {
        if (pp->to == (unsigned)  this->dfa->s) {
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

bool Automaton::hasNextStateFrom(int state, int search) {
  unsigned p, l, r, index; // BDD traversal variables
  std::stack<unsigned> nodes;

  p = this->dfa->q[state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top(); nodes.pop();
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      if (l == (unsigned)search) {
        return true;
      }
    } else {
      nodes.push(l);
      nodes.push(r);
    }
  }
  return false;
}
/**
 * @return vector of states that are 1 walk away
 */
std::set<int>* Automaton::getNextStates(int state) {
  unsigned p, l, r, index; // BDD traversal variables
  std::set<int>* next_states = new std::set<int>();
  std::stack<unsigned> nodes;

  p = this->dfa->q[state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top(); nodes.pop();
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      next_states->insert(l);
    } else {
      nodes.push(l);
      nodes.push(r);
    }
  }
  return next_states;
}

} /* namespace Theory */
} /* namespace Vlab */
