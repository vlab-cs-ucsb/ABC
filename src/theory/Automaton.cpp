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

unsigned long Automaton::trace_id = 0;

const std::string Automaton::Name::NONE = "none";
const std::string Automaton::Name::BOOL = "BoolAutomaton";
const std::string Automaton::Name::UNARY = "UnaryAutomaton";
const std::string Automaton::Name::INT = "IntAutomaton";
const std::string Automaton::Name::STRING = "StringAutomaton";
const std::string Automaton::Name::BINARYINT = "BinaryIntAutomaton";

Automaton::Automaton(Automaton::Type type)
        : type(type), is_count_matrix_cached_{false}, dfa(nullptr), num_of_variables(0), variable_indices(nullptr), id(Automaton::trace_id++) {
}

Automaton::Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables)
        : type(type), is_count_matrix_cached_{false}, dfa(dfa), num_of_variables(num_of_variables), id(Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables, 1); // make indices one more to be safe
}

Automaton::Automaton(const Automaton& other)
        : type(other.type), is_count_matrix_cached_{false}, dfa(dfaCopy(other.dfa)), num_of_variables(other.num_of_variables), id(Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables, 1); // make indices one more to be safe
}

Automaton::~Automaton() {
  if (dfa) {
    dfaFree(dfa);
    dfa = nullptr;
  }
  delete[] variable_indices;
  variable_indices = nullptr;
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
  case Automaton::Type::UNARY:
    return Automaton::Name::UNARY;
  case Automaton::Type::INT:
    return Automaton::Name::INT;
  case Automaton::Type::STRING:
    return Automaton::Name::STRING;
  case Automaton::Type::BINARYINT:
    return Automaton::Name::BINARYINT;
  default:
    LOG(FATAL)<< "Unknown automaton type!";
    return "";
  }
}

Automaton::Type Automaton::getType() const {
  return type;
}

unsigned long Automaton::getId() {
  return id;
}

DFA_ptr Automaton::getDFA() {
  return dfa;
}

int Automaton::getNumberOfVariables() {
  return num_of_variables;
}

int* Automaton::getVariableIndices() {
  return variable_indices;
}

/**
 * TODO Needs complete refactoring, has a lot of room for improvements
 * especially in libstranger function calls
 */
bool Automaton::checkEquivalence(Automaton_ptr other_auto) {
  DFA_ptr temp1 = nullptr, temp2 = nullptr, temp3 = nullptr;
  bool result = false;


  temp1 = dfaProduct(this->dfa, other_auto->dfa, dfaIMPL);
  temp2 = dfaProduct(other_auto->dfa, this->dfa, dfaIMPL);
  temp3 = dfaProduct(temp1,temp2,dfaAND);
  dfaFree(temp1);
  dfaFree(temp2);

  dfaNegation(temp3);

  if (temp3->f[temp3->s] == 1) {
    dfaFree(temp3);
    return false;
  }

  if (temp3->ns == 1 && temp3->f[temp3->s] == -1) {
    dfaFree(temp3);
    return true;
  }

  char *satisfyingexample = nullptr;
  unsigned *indices = getIndices((unsigned)num_of_variables);

  satisfyingexample = dfaMakeExample(temp3, 1, num_of_variables, indices);

  result = (satisfyingexample == NULL) ? true : false;
  if(satisfyingexample != nullptr) {
    free(satisfyingexample);
  }
  dfaFree(temp3);
  delete[] indices;

  return result;
}

/**
 * Works for minimized automaton,
 * (For a non-minimized automaton need to check reachability of an accepting state)
 */
bool Automaton::isEmptyLanguage() {
  bool result = (dfa->ns == 1 && dfa->f[dfa->s] == -1)? true : false;
  DVLOG(VLOG_LEVEL) << "[" << this->id << "]->isEmptyLanguage? " << std::boolalpha << result;
  return result;
}

bool Automaton::isInitialStateAccepting() {
  return (this->dfa->f[this->dfa->s] == 1);
}

bool Automaton::isOnlyInitialStateAccepting() {
  if (not isInitialStateAccepting()) {
    return false;
  }

  for (int s = 0; s < this->dfa->ns; s++) {
    if (s != this->dfa->s and isAcceptingState(s)) {
      return false;
    } else if (hasNextState(s, this->dfa->s)) {
      return false;
    }
  }
  return true;
}

bool Automaton::isCyclic() {
  bool result = false;
  std::map<int, bool> is_discovered;
  std::map<int, bool> is_stack_member;
  int sink_state = getSinkState();
  is_discovered[sink_state] = true; // avoid sink state

  result = isCyclic(this->dfa->s, is_discovered, is_stack_member);
  DVLOG(VLOG_LEVEL) << "[" << this->id << "]->isCyclic() ? " << std::boolalpha << result;
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

boost::multiprecision::cpp_int Automaton::Count(int bound, bool count_less_than_or_equal_to_bound, bool count_reserved_words) {

  auto x = GetAdjacencyCountMatrix(count_reserved_words);
  if (count_less_than_or_equal_to_bound) {
    x[this->dfa->ns][this->dfa->ns] = 1;
  }

  int power = bound + 1; // matrix exponentiation is off by 1

  if (power == 1) {
    auto result = x[this->dfa->s][this->dfa->ns];
    DVLOG(VLOG_LEVEL) << "[" << this->id << "]->count(" << bound << ") : " << result;
    return result;
  }

  CountMatrix y (this->dfa->ns + 1, CountVector(this->dfa->ns + 1, 0));
  for (unsigned i = 0; i < y.size(); ++i) {
    y[i][i] = 1;
  }

  while (power > 1) {
    if (power % 2 == 0) {
      x = Util::Math::multiply_matrix(x, x);
      power = power / 2;
    } else {
      y = Util::Math::multiply_matrix(x, y);
      x = Util::Math::multiply_matrix(x, x);
      power = (power - 1) / 2;
    }
  }

  x = Util::Math::multiply_matrix(x, y);

  auto result = x[this->dfa->s][this->dfa->ns];
  DVLOG(VLOG_LEVEL) << "[" << this->id << "]->count(" << bound << ") : " << result;
  return result;
}

boost::multiprecision::cpp_int Automaton::SymbolicCount(int bound, bool count_less_than_or_equal_to_bound) {
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

  return boost::multiprecision::cpp_int (str_result);
}

boost::multiprecision::cpp_int Automaton::SymbolicCount(double bound, bool count_less_than_or_equal_to_bound) {
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
    if ((not is_stack_member[next_state]) and (not isSinkState(next_state)) and
            isStateReachableFrom(search_state, next_state, is_stack_member)) {
      return true;
    } else if (next_state == search_state) {
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
  for (int s = 0; s < this->dfa->ns; s++) {
    node = new GraphNode(s);
    if (s == 0) {
      graph->setStartNode(node);
    }

    if (this->isSinkState(s)) {
      graph->setSinkNode(node);
    } else if (this->isAcceptingState(s)) {
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
  unsigned sink_state = (unsigned) this->getSinkState();
  bool is_accepting_single_word = true;
  bool is_final_state = false;
  int bit_counter = 0;

  for (int s = 0; s < this->dfa->ns; s++) {
    is_final_state = isAcceptingState(s);
    p = this->dfa->q[s];
    nodes.push_back(p);
    bit_stack.push_back(0);
    while (not nodes.empty()) {
      p = nodes.back();
      nodes.pop_back();
      bit_counter = bit_stack.back();
      bit_stack.pop_back();
      LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
      if (index == BDD_LEAF_INDEX) {
        if (sink_state != l) {
          next_states[l]++;
          if (bit_counter != num_of_variables or (next_states[l] > 1) or (next_states.size() > 1) or is_final_state) {
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
  int sink_state = getSinkState();
  NextState start_state = std::make_pair(this->dfa->s, std::vector<bool>());
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

  if (this->isAcceptingState(state.first)) {
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
  return dfaMakeExample(this->dfa, 1, num_of_variables, getIndices((unsigned) num_of_variables));
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

std::vector<char> Automaton::getBinaryFormat(unsigned long number, int bit_length) {
  int index = bit_length;
  unsigned subject = number;
  std::vector<char> binary_str (bit_length + 1);
  binary_str[bit_length] = '\0';

  for (index--; index >= 0; index--) {
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

void Automaton::minimize() {
  DFA_ptr tmp = this->dfa;
  this->dfa = dfaMinimize(tmp);
  dfaFree(tmp);
  DVLOG(VLOG_LEVEL) << this->id << " = [" << this->id << "]->minimize()";
}

void Automaton::project(unsigned index) {
  DFA_ptr tmp = this->dfa;
  this->dfa = dfaProject(tmp, index);
  dfaFree(tmp);

  if (index < (unsigned)(this->num_of_variables - 1)) {
    int* indices_map = new int[this->num_of_variables];
    for (int i = 0, j = 0; i < this->num_of_variables; i++) {
      if ((unsigned)i != index) {
        indices_map[i] = j;
        j++;
      }
    }
    dfaReplaceIndices(this->dfa, indices_map);
    delete[] indices_map;
  }

  this->num_of_variables = this->num_of_variables - 1;

  delete this->variable_indices;
  this->variable_indices = getIndices(num_of_variables);
  DVLOG(VLOG_LEVEL) << this->id << " = [" << this->id << "]->project(" << index << ")";
}

bool Automaton::isStartState(int state_id) {
  return (this->dfa->s == state_id);
}

bool Automaton::isSinkState(int state_id) {
  return (bdd_is_leaf(this->dfa->bddm, this->dfa->q[state_id])
          and (bdd_leaf_value(this->dfa->bddm, this->dfa->q[state_id]) == (unsigned) state_id)
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

bool Automaton::hasIncomingTransition(int state) {
  for (int i = 0; i < this->dfa->ns; i++) {
    if (hasNextState(i, state)) {
      return true;
    }
  }
  return false;
}

/**
 * @returns true if a start state is reachable from an accepting state, false otherwise
 */
bool Automaton::isStartStateReachableFromAnAcceptingState() {
  paths state_paths, pp;
  for (int i = 0; i < this->dfa->ns; i++) {
    if (isAcceptingState(i)) {
      state_paths = pp = make_paths(this->dfa->bddm, this->dfa->q[i]);
      while (pp) {
        if (pp->to == (unsigned) this->dfa->s) {
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

bool Automaton::hasNextState(int state, int search) {
  unsigned p, l, r, index; // BDD traversal variables
  std::stack<unsigned> nodes;

  p = this->dfa->q[state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top();
    nodes.pop();
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      if (l == (unsigned) search) {
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
 * @return next state from the state by taking transition path (1 step away)
 */
int Automaton::getNextState(int state, std::vector<char>& exception) {
  int next_state = -1; // only for initialization
   unsigned p, l, r, index = 0; // BDD traversal variables

   CHECK_EQ(num_of_variables, exception.size());

   p = this->dfa->q[state];

   for (int i = 0; i < num_of_variables; i++) {
     LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
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
     LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
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

  p = this->dfa->q[state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top();
    nodes.pop();
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
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
  p = this->dfa->q[state];
  nodes.push_back(p);
  transition_stack.push_back(std::vector<bool>());
  while (not nodes.empty()) {
    p = nodes.back();
    nodes.pop_back();
    current_transition = transition_stack.back();
    transition_stack.pop_back();
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      if (visited[l]) {
        // avoid cycles
      } else {
        state = l;
        while (current_transition.size() < (unsigned) num_of_variables) {
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
  int sink_state = getSinkState();
  if (sink_state != this->dfa->s) {
    state_stack.push(std::make_pair(this->dfa->s, 0));
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

CountMatrix Automaton::GetAdjacencyCountMatrix(bool count_reserved_words) {
  if (is_count_matrix_cached_) {
    return count_matrix_;
  }

  CountMatrix count_matrix (this->dfa->ns + 1, CountVector(this->dfa->ns + 1, 0));

  unsigned left, right, index;
  for (int s = 0; s < this->dfa->ns; ++s) {
    // pair<sbdd_node_id, bdd_depth>
    Node current_bdd_node {dfa->q[s], 0}, left_node, right_node;
    std::stack<Node> bdd_node_stack;
    bdd_node_stack.push(current_bdd_node);
    while (not bdd_node_stack.empty()) {
      current_bdd_node = bdd_node_stack.top(); bdd_node_stack.pop();
      LOAD_lri(&dfa->bddm->node_table[current_bdd_node.first], left, right, index);
      if (index == BDD_LEAF_INDEX) {
        count_matrix[s][left] += static_cast<int>(std::pow(2, (num_of_variables - current_bdd_node.second)));
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
    if (isAcceptingState(s)) {
      count_matrix[s][this->dfa->ns] = 1;
    }
  }

/*
  // TODO use extra bit instead of reserved words, so that we do not need counting trick.
  if (count_reserved_words) {
    for (int s = 0; s < this->dfa->ns; ++s) {
      auto max_transition = std::max_element(count_matrix[s].begin(), count_matrix[s].end());
      *max_transition += 2; // add two reserved words
    }
  }
*/
  // make transitions to sink count 0
  int sink_state = this->getSinkState();
  if (sink_state > -1) {
    for (int s = 0; s < this->dfa->ns; ++s) {
      count_matrix[s][sink_state] = 0;
    }
  }

//  std::cout << std::endl;
//  for (auto& row : count_matrix) {
//    for (auto& col : row) {
//      std::cout << col << " ";
//    }
//    std::cout << std::endl;
//  }
  count_matrix_ = count_matrix;
  is_count_matrix_cached_ = true;
  return count_matrix;
}

AdjacencyList Automaton::getAdjacencyCountList(bool count_reserved_words) {
  int num_of_transitions;
  int leaf_count = 0;
  unsigned l, r, index;
  Node current_node, top, lo_node, hi_node, entry;
  std::stack<Node> node_stack;
  AdjacencyList adjacency_count_list(this->dfa->ns);
  std::vector<int> transition_count(dfa->ns, 0);
  std::vector<int> reachable_states(dfa->ns, 0);

  // process each state and run a dfs
  for (int i = 0; i < this->dfa->ns; i++) {
    // keep a list of reachable states for optimization purposes
    for (int j = 0; j < leaf_count; j++) {
      reachable_states[j] = 0;
    }

    leaf_count = 0;
    for (int j = 0; j < this->dfa->ns; j++) {
      transition_count[j] = 0;
    }

    LOAD_lri(&dfa->bddm->node_table[i], l, r, index);
    // keep track of t and id as pair<id,t> in stack
    current_node.second = 0;
    current_node.first = dfa->q[i];

    node_stack.push(current_node);

    while (not node_stack.empty()) {
      top = node_stack.top();
      node_stack.pop();
      LOAD_lri(&this->dfa->bddm->node_table[top.first], l, r, index);
      if (index == BDD_LEAF_INDEX) {
        num_of_transitions = std::pow(2, (num_of_variables - top.second));
        if (!transition_count[l]) {
          reachable_states[leaf_count] = l;
          leaf_count++;
        }
        transition_count[l] += num_of_transitions;
      } else {
        lo_node.first = l;
        lo_node.second = top.second + 1;
        hi_node.first = r;
        hi_node.second = top.second + 1;
        node_stack.push(lo_node);
        node_stack.push(hi_node);
      }
    }

    for (int j = 0; j < leaf_count; j++) {
      entry.first = i;
      entry.second = transition_count[reachable_states[j]];
      adjacency_count_list[reachable_states[j]].push_back(entry);
    }
  }

  if (count_reserved_words) {
    addReservedWordsToCount(adjacency_count_list);
  }

//  for (int i = 0; i < adjacency_count_list.size(); i++) {
//    std::cout << i << " : ";
//    for (int j = 0; j < adjacency_count_list[i].size(); j++) {
//      std::cout << "{" << adjacency_count_list[i][j].first << ", " << adjacency_count_list[i][j].second << "} ";
//    }
//    std::cout << std::endl;
//  }

  return adjacency_count_list;
}

/**
 * This is an unsound hack to count reserved words
 * To have sound count with reserved words, get rid of reserved words
 * by using extra-bit instead
 */
void Automaton::addReservedWordsToCount(AdjacencyList& adjaceny_count_list) {
  unsigned node_size = adjaceny_count_list.size();
  std::vector<int> max_transition_count(node_size);
  std::vector<int> max_transition_id(node_size);
  std::vector<int> max_transition_index(node_size);
  int sink_state = getSinkState();

  for (unsigned i = 0; i < node_size; i++) {
    max_transition_count[i] = -1;
  }

  for (unsigned i = 0; i < node_size; i++) {
    for (unsigned j = 0; j < adjaceny_count_list[i].size(); j++) {
      if (adjaceny_count_list[i][j].second > max_transition_count[adjaceny_count_list[i][j].first]) {
        max_transition_count[adjaceny_count_list[i][j].first] = adjaceny_count_list[i][j].second;
        max_transition_id[adjaceny_count_list[i][j].first] = i;
        max_transition_index[adjaceny_count_list[i][j].first] = j;
      }
    }
  }

  for (unsigned i = 0; i < node_size; i ++) {
    if (sink_state > -1 and i != (unsigned)sink_state) {
      adjaceny_count_list[max_transition_id[i]][max_transition_index[i]].second += 2;
    }
  }
  if (sink_state > -1) {
    adjaceny_count_list[sink_state] = std::vector<Node>(0);
  }
}

void Automaton::generateGFScript(int bound, std::ostream& out, bool count_less_than_or_equal_to_bound) {
  AdjacencyList adjacency_count_list = getAdjacencyCountList(true);
  unsigned node_size = adjacency_count_list.size();
  unsigned updated_node_size = node_size + 1;
  adjacency_count_list.resize(updated_node_size);

  Node artificial;

  // add a self-loop if we count up to bound (bound inclusive)
  if (count_less_than_or_equal_to_bound) {
    artificial.first = node_size;
    artificial.second = 1;
    adjacency_count_list[node_size].push_back(artificial);
  }

  for (int i = 0; (unsigned)i < node_size; i++) {
    if (isAcceptingState(i)) {
      artificial.first = i;
      artificial.second = 1;
      adjacency_count_list[node_size].push_back(artificial);
    }
  }

  out << "bound = " << bound + 2 << ";\n";
  out << "ID = IdentityMatrix[" << updated_node_size << "];\n\n";
  out << "A = SparseArray[ { ";
  std::string row_seperator = "";
  std::string col_seperator = "";
  int c = 0;
  for (auto& transitions : adjacency_count_list) {
    out << row_seperator;
    row_seperator = "";
    col_seperator = "";
    for(auto& node : transitions) {
      out << col_seperator;
      out << "{" << node.first + 1 << ", " << c + 1 << "} -> " << node.second;
      col_seperator = ", ";
      row_seperator = ", ";
    }
    c++;
  }
  out << "}];\n\n";
  out << "X = ID - A t;\n\n";
  out << "Xsubmatrix = X[[ {";
  std::string seperator = "";
  for(unsigned i = 1; i < updated_node_size; i++) {
    out << seperator << i;
    seperator = ",";
  }
  out << "},{";
  for(unsigned i = 1; i < updated_node_size - 1; i++){
    out << i << ",";
  }

  out << updated_node_size << "}";

  out << "]];\n";

  out << "b = CoefficientList[-Det[Xsubmatrix],t];\n";
  out << "c = CoefficientList[Det[X],t];\n";
  out << "maxLen = Max[Map[Length, {b,c}]]\n";
  out << "bPadLen = Max[0, maxLen - Length[b]];\n";
  out << "cPadLen = Max[0, maxLen - Length[c]];\n";
  out << "b = ArrayPad[b, {0, bPadLen}];\n";
  out << "c = ArrayPad[c, {0, cPadLen}];\n";
  out << "p = -c[[ Range[2,maxLen] ]] / c[[1]];\n";
  out << "a = Table[0,{maxLen}];\n";
  out << "a[[1]] = b[[1]]/c[[1]];\n";
  out << "For[ i = 2, i <= maxLen, i++, a[[i]] = (b[[i]] - Total[c[[2;;i]]*a[[i-1;;1;;-1]]]) / c[[1]] ];\n";
  out << "numPaths = LinearRecurrence[p,a,{bound,bound}][[1]];\n";
  out << "Print[N[numPaths]];";

  out << std::endl;
}

void Automaton::generateMatrixScript(int bound, std::ostream& out, bool count_less_than_or_equal_to_bound) {
  AdjacencyList adjacency_count_list = getAdjacencyCountList(true);
  unsigned node_size = adjacency_count_list.size();
  unsigned updated_node_size = node_size + 1;
  adjacency_count_list.resize(updated_node_size);

  Node artificial;

  // add a self-loop if we count up to bound (bound inclusive)
  if (count_less_than_or_equal_to_bound) {
    artificial.first = node_size;
    artificial.second = 1;
    adjacency_count_list[node_size].push_back(artificial);
  }

  for (int i = 0; (unsigned)i < node_size; i++) {
    if (isAcceptingState(i)) {
      artificial.first = i;
      artificial.second = 1;
      adjacency_count_list[node_size].push_back(artificial);
    }
  }

  out << "A = SparseArray[{";
  std::string row_seperator = "";
  std::string col_seperator = "";
  int c = 0;
  for (auto& transitions : adjacency_count_list) {
    out << row_seperator;
    row_seperator = "";
    col_seperator = "";
    for(auto& node : transitions) {
      out << col_seperator;
      out << "{" << node.first + 1 << ", " << c + 1 << "} -> " << node.second;
      col_seperator = ", ";
      row_seperator = ", ";
    }
    c++;
  }
  out << "}];\n";
  // state indexes are off by one
  out << "numPaths = MatrixPower[A, " << bound + 2 << "][[" << this->dfa->s + 1 << ", " << this->dfa->ns + 1 << "]];\n";
  out << "Print[N[numPaths]];";
  out << std::endl;
}

/**
 * Adds artificial source and final state
 * Prepares for model counting
 */
void Automaton::preProcessAdjacencyList(AdjacencyList& adjaceny_count_list) {
  unsigned node_size = adjaceny_count_list.size();
  unsigned updated_node_size = node_size + 2;
  std::map<int, bool> is_useful_state;
  adjaceny_count_list.resize(updated_node_size);

  Node artificial;
  artificial.first = node_size;
  artificial.second = 1;

  adjaceny_count_list[this->dfa->s].push_back(artificial);
  adjaceny_count_list[node_size].push_back(artificial);

  for (int i = 0; (unsigned)i < node_size; i++) {
    if (isAcceptingState(i)) {
      artificial.first = i;
      artificial.second = 1;
      adjaceny_count_list[node_size + 1].push_back(artificial);
    }
  }

  is_useful_state[node_size + 1] = true;

  for ( unsigned i = 0; i < updated_node_size; i++) {
    unsigned j = 0;
    for (auto& adjacency : adjaceny_count_list) {
      for (auto& node : adjacency) {
        is_useful_state[node.first] |= is_useful_state[j];
      }
    }
    j++;
  }

  AdjacencyList new_list(updated_node_size);
  for (unsigned i = 0; i < updated_node_size; i++) {
    if (is_useful_state[i]) {
      for (unsigned j = 0; j < adjaceny_count_list[i].size(); j++) {
        if (is_useful_state[adjaceny_count_list[i][j].first]) {
          new_list[i].push_back(adjaceny_count_list[i][j]);
        }
      }
    }
  }

  adjaceny_count_list.clear();
  adjaceny_count_list = new_list;
}





void Automaton::toDotAscii(bool print_sink, std::ostream& out) {
  paths state_paths, pp;
  trace_descr tp;

  int i, j, k, l, size, maxexp, sink;
  pCharPair *buffer; //array of charpairs references
  char *character;
  pCharPair **toTrans; //array for all states, each entry is an array of charpair references
  int *toTransIndecies;
  char** ranges;

  print_sink = print_sink || (dfa->ns == 1 and dfa->f[0] == -1);
  sink = find_sink(dfa);

  out << "digraph MONA_DFA {\n"
          " rankdir = LR;\n "
          " center = true;\n"
          " size = \"700.5,1000.5\";\n"
          " edge [fontname = Courier];\n"
          " node [height = .5, width = .5];\n"
          " node [shape = doublecircle];";

  for (i = 0; i < dfa->ns; i++) {
    if (dfa->f[i] == 1) {
      out << " " << i << ";";
    }
  }

  out << "\n node [shape = circle];";

  for (i = 0; i < dfa->ns; i++) {
    if (dfa->f[i] == -1) {
      if (i != sink || print_sink) {
        out << " " << i << ";";
      }
    }
  }

  out << "\n node [shape = box];";

  for (i = 0; i < dfa->ns; i++) {
    if (dfa->f[i] == 0) {
      out << " " << i << ";";
    }
  }

  out << "\n init [shape = plaintext, label = \"\"];\n" << " init -> " << dfa->s << ";\n";

  maxexp = 1 << num_of_variables;
  //TODO convert into c++ style memory management
  buffer = (pCharPair*) malloc(sizeof(pCharPair) * maxexp); //max no of chars from Si to Sj = 2^num_of_variables
  character = (char*) malloc((num_of_variables + 1) * sizeof(char));
  toTrans = (pCharPair**) malloc(sizeof(pCharPair*) * dfa->ns); //need this to gather all edges out to state Sj from Si
  for (i = 0; i < dfa->ns; i++) {
    toTrans[i] = (pCharPair*) malloc(maxexp * sizeof(pCharPair));
  }
  toTransIndecies = (int*) malloc(dfa->ns * sizeof(int)); //for a state Si, how many edges out to each state Sj

  for (i = 0; i < dfa->ns; i++) {
    //get transitions out from state i
    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);

    //init buffer
    for (j = 0; j < dfa->ns; j++) {
      toTransIndecies[j] = 0;
    }

    for (j = 0; j < maxexp; j++) {
      for (k = 0; k < dfa->ns; k++) {
        toTrans[k][j] = 0;
      }
      buffer[j] = 0;
    }

    //gather transitions out from state i
    //for each transition pp out from state i
    while (pp) {
      if (pp->to == (unsigned) sink && not print_sink) {
        pp = pp->next;
        continue;
      }
      //get mona character on transition pp
      for (j = 0; j < num_of_variables; j++) {
        for (tp = pp->trace; tp && (tp->index != (unsigned) variable_indices[j]); tp = tp->next)
          ;

        if (tp) {
          if (tp->value)
            character[j] = '1';
          else
            character[j] = '0';
        } else
          character[j] = 'X';
      }
      character[j] = '\0';
      if (num_of_variables == 8) {
        //break mona character into ranges of ascii chars (example: "0XXX000X" -> [\s-!], [0-1], [@-A], [P-Q])
        size = 0;
        getTransitionChars(character, num_of_variables, buffer, &size);
        //get current index
        k = toTransIndecies[pp->to];
        //print ranges
        for (l = 0; l < size; l++) {
          toTrans[pp->to][k++] = buffer[l];
          buffer[l] = 0;    //do not free just detach
        }
        toTransIndecies[pp->to] = k;
      } else {
//        k = toTransIndecies[pp->to];
//        toTrans[pp->to][k] = (char*) malloc(sizeof(char) * (strlen(character) + 1));
//        strcpy(toTrans[pp->to][k], character);
//        toTransIndecies[pp->to] = k + 1;
      }
      pp = pp->next;
    }

    //print transitions out of state i
    for (j = 0; j < dfa->ns; j++) {
      size = toTransIndecies[j];
      if (size == 0 || (sink == j && not print_sink)) {
        continue;
      }
      ranges = mergeCharRanges(toTrans[j], &size);
      //print edge from i to j
      out << " " << i << " -> " << j << " [label=\"";
      bool print_label = (j != sink || print_sink);
      l = 0;    //to help breaking into new line
      //for each trans k on char/range from i to j
      for (k = 0; k < size; k++) {
        //print char/range
        if (print_label) {
          out << " " << ranges[k];
        }
        l += strlen(ranges[k]);
        if (l > 18) {
          if (print_label) {
            out << "\\n";
          }
          l = 0;
        } else if (k < (size - 1)) {
          if (print_label) {
            out << ",";
          }
        }
        free(ranges[k]);
      }      //for
      out << "\"];\n";
      if (size > 0)
        free(ranges);
    }
    //for each state free charRange
    //merge with loop above for better performance
    for (j = 0; j < dfa->ns; j++) {
      if (j == sink && not print_sink) {
        continue;
      }
      size = toTransIndecies[j];
      for (k = 0; k < size; k++) {
        free(toTrans[j][k]);
      }
    }

    kill_paths(state_paths);
  }    //end for each state

  free(character);
  free(buffer);
  for (i = 0; i < dfa->ns; i++) {
    free(toTrans[i]);
  }
  free(toTrans);
  free(toTransIndecies);

  out << "}" << std::endl;
}

void Automaton::toDot(std::ostream& out, bool print_sink) {
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, l;
  char **buffer;
  int *used, *allocated;
  unsigned* offsets = getIndices((unsigned) num_of_variables);
  int no_free_vars = num_of_variables;
  DFA_ptr a = this->dfa;
  int sink = getSinkState();

  print_sink = print_sink || (dfa->ns == 1 and dfa->f[0] == -1);

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
        for (tp = pp->trace; tp && (tp->index != offsets[j]); tp = tp->next)
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
  delete[] offsets;

  out << "}" << std::endl;
}

void Automaton::toBDD(std::ostream& out) {
  Table *table = tableInit();

  /* remove all marks in a->bddm */
  bdd_prepare_apply1(this->dfa->bddm);

  /* build table of tuples (idx,lo,hi) */
  for (int i = 0; i < this->dfa->ns; i++) {
    __export(this->dfa->bddm, this->dfa->q[i], table);
  }

  /* renumber lo/hi pointers to new table ordering */
  for (unsigned i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx != -1) {
      table->elms[i].lo = bdd_mark(this->dfa->bddm, table->elms[i].lo) - 1;
      table->elms[i].hi = bdd_mark(this->dfa->bddm, table->elms[i].hi) - 1;
    }
  }

  out << "digraph MONA_DFA_BDD {\n"
          "  center = true;\n"
          "  size = \"100.5,70.5\"\n"
//      "  orientation = landscape;\n"
          "  node [shape=record];\n"
          "   s1 [shape=record,label=\"";

  for (int i = 0; i < this->dfa->ns; i++) {
    out << "{" << this->dfa->f[i] << "|<" << i << "> " << i << "}";
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

  for (int i = 0; i < this->dfa->ns; i++) {
    out << " s1:" << i << " -> " << bdd_mark(this->dfa->bddm, this->dfa->q[i]) - 1 << " [style=bold];\n";
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
  char **names = new char*[this->num_of_variables];
  char *orders = new char[this->num_of_variables];
  std::string name = "a";
  for (int i = 0; i < this->num_of_variables; i++) {
    orders[i] = i;
    names[0] = &*name.begin();
  }

  dfaExport(this->dfa, file_name_ptr, this->num_of_variables, names, orders);
}

DFA_ptr Automaton::importDFA(std::string file_name) {
  char **names = new char*[this->num_of_variables];
  int ** orders = new int*[this->num_of_variables];
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
  if (Automaton::Type::INT == type or Automaton::Type::STRING == type) {
    if (force_mona_format) {
      toDot(outfile, print_sink);
    } else {
      toDotAscii(print_sink, outfile);
    }
  } else {
    toDot(outfile, print_sink);
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
  assert(strlen(transitions) == var);
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
    assert(s != NULL);
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
  assert(asciiVal != NULL);
  char* charName[] = {"NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS ", "HT ", "LF ", "VT ", "FF ", "CR ", "SO ", "SI ", "DLE",
      "DC1", "DC2", "CD3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM ", "SUB", "ESC", "FS ", "GS ", "RS ", "US "};
  if (c < 32){
    strcpy(asciiVal, charName[(int)c]);
    return;
  }
  else if (c > 126){
    charToAsciiDigits(c, asciiVal);
    assert(strlen(asciiVal) == 3);
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
    assert(strlen(range) <= 3);
    return;
  }

  char* char1 = (char*)(malloc ((4) * (sizeof(char))));
  char* char2 = (char*)(malloc ((4) * (sizeof(char))));
  //[firstChar-lastChar]
  range[i++] = '[';

  //put first char in range
  charToAscii(char1, firstChar);
  assert(strlen(char1) <= 3);
  strncpy(range+i, char1, strlen(char1));
  i += strlen(char1);
  range[i++] = '-';
  //put second char in range
  charToAscii(char2, lastChar);
  assert(strlen(char2) <= 3);
  strncpy(range+i, char2, strlen(char2));
  i += strlen(char2);

  range[i++] = ']';

  range[i] = '\0';
  assert(strlen(range) <= 9);

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

} /* namespace Theory */
} /* namespace Vlab */
