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
        : type_(type), is_count_matrix_cached_{false}, dfa_(nullptr), num_of_variables_(0), variable_indices_(nullptr), id_(Automaton::trace_id++) {
}

Automaton::Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables)
        : type_(type), is_count_matrix_cached_{false}, dfa_(dfa), num_of_variables_(num_of_variables), id_(Automaton::trace_id++) {
  variable_indices_ = getIndices(num_of_variables, 1); // make indices one more to be safe
}

Automaton::Automaton(const Automaton& other)
        : type_(other.type_), is_count_matrix_cached_{false}, dfa_(nullptr), num_of_variables_(other.num_of_variables_), id_(Automaton::trace_id++) {
          if (other.dfa_) {
            dfa_ = dfaCopy(other.dfa_);
          }
          variable_indices_ = getIndices(num_of_variables_, 1); // make indices one more to be safe
}

Automaton::~Automaton() {
  if (dfa_) {
    dfaFree(dfa_);
    dfa_ = nullptr;
  }
  delete[] variable_indices_;
  variable_indices_ = nullptr;
  //  DVLOG(VLOG_LEVEL) << "delete " << " [" << this->id << "]";
}

//Automaton_ptr Automaton::clone() const {
//  return new Automaton(*this);
//}

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

int Automaton::getNumberOfVariables() {
  return num_of_variables_;
}

int* Automaton::getVariableIndices() {
  return variable_indices_;
}

/**
 * TODO write test cases
 */
bool Automaton::IsEqual(Automaton_ptr other_auto) {

  auto impl_1 = dfaProduct(this->dfa_, other_auto->dfa_, dfaIMPL);
  auto impl_2 = dfaProduct(other_auto->dfa_, this->dfa_, dfaIMPL);
  auto result_dfa = dfaProduct(impl_1,impl_2,dfaAND);
  dfaFree(impl_1);
  dfaFree(impl_2);

  dfaNegation(result_dfa);

  auto minimized_dfa = dfaMinimize(result_dfa);
  dfaFree(result_dfa);

  bool is_empty_language = (minimized_dfa->ns == 1 && minimized_dfa->f[minimized_dfa->s] == -1)? true : false;
  dfaFree(minimized_dfa);

  return is_empty_language;
}

/**
 * Works for minimized automaton,
 * (For a non-minimized automaton need to check reachability of an accepting state)
 */
bool Automaton::isEmptyLanguage() {
  bool result = (dfa_->ns == 1 && dfa_->f[dfa_->s] == -1)? true : false;
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->isEmptyLanguage? " << std::boolalpha << result;
  return result;
}

bool Automaton::is_initial_state_accepting() {
  return is_accepting_state(this->dfa_->s);
}

bool Automaton::isOnlyInitialStateAccepting() {
  if (not is_initial_state_accepting()) {
    return false;
  }

  for (int s = 0; s < this->dfa_->ns; s++) {
    if (s != this->dfa_->s and is_accepting_state(s)) {
      return false;
    } else if (hasNextState(s, this->dfa_->s)) {
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

/**
 * Counting by vector products
 */
BigInteger Automaton::Count(const int bound, const bool count_less_than_or_equal_to_bound) {

  Eigen::SparseMatrix<BigInteger> x = GetCountMatrix();
  if (count_less_than_or_equal_to_bound) {
    x.insert(this->dfa_->ns, this->dfa_->ns) = 1;
  }

  if (bound == 0) {
    BigInteger result = x.coeff(this->dfa_->s, this->dfa_->ns);
    DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->count(" << bound << ") : " << result;
    return result;
  }

  // exponentiation is off by 1 because of artificial accepting state

  int power = bound + 1;

  // try to get cached vector
  Eigen::SparseVector<BigInteger> v (this->dfa_->ns + 1);
  std::cout << "b: " << bound << " cache b: " << bound_and_initializer_vector_.first << std::endl;
  if (power > bound_and_initializer_vector_.first) {
    power = power - bound_and_initializer_vector_.first;
    v = std::move(bound_and_initializer_vector_.second);
  } else {
    v = x.innerVector(this->dfa_->ns);
  }

  while (power > 1) {
    v = x * v;
    --power;
  }

  bound_and_initializer_vector_ = std::make_pair(bound, v);
  BigInteger result = v.coeff(this->dfa_->s);
  result.backend().limbs();
  DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->count(" << bound << ") : " << result;
  return result;
}

/**
 * Counting with matrix exponentiation by successive squaring
 */
BigInteger Automaton::CountByMatrixMultiplication(int bound, bool count_less_than_or_equal_to_bound) {

  Eigen::SparseMatrix<BigInteger> x = GetCountMatrix();
  if (count_less_than_or_equal_to_bound) {
    x.insert(this->dfa_->ns, this->dfa_->ns) = 1;
  }

  if (bound == 0) {
    BigInteger result = x.coeff(this->dfa_->s, this->dfa_->ns);
    DVLOG(VLOG_LEVEL) << "[" << this->id_ << "]->count(" << bound << ") : " << result;
    return result;
  }

  // matrix exponentiation is off by 1 because of artificial accepting state
  int power = bound + 1;

  Eigen::SparseMatrix<BigInteger> y;
  bool has_odds = false;

  while (power > 1) {
    if (power % 2 == 0) {
      power = power / 2;
    } else {
      power = (power - 1) / 2;
      if (has_odds) {
        y = x * y;
      } else {
        y = x;
        has_odds = true;
      }
    }
    x = x * x;
  }

  if (has_odds) {
    x = x * y;
  }

  BigInteger result = x.coeff(this->dfa_->s, this->dfa_->ns);
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
    } else if ((not is_stack_member[next_state]) and (not isSinkState(next_state)) and
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

    if (this->isSinkState(s)) {
      graph->setSinkNode(node);
    } else if (this->is_accepting_state(s)) {
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

  for (int s = 0; s < this->dfa_->ns; s++) {
    is_final_state = is_accepting_state(s);
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
          if (bit_counter != num_of_variables_ or (next_states[l] > 1) or (next_states.size() > 1) or is_final_state) {
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

  if (this->is_accepting_state(state.first)) {
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
  return dfaMakeExample(this->dfa_, 1, num_of_variables_, getIndices((unsigned) num_of_variables_));
}

std::ostream& operator<<(std::ostream& os, const Automaton& automaton) {
  return os << automaton.str();
}

/**
 * If variable indices is nullptr, default indices are created
 */
DFA_ptr Automaton::DfaMakePhi(int num_of_variables, int* variable_indices) {
  if (variable_indices == nullptr) {
    variable_indices = getIndices(num_of_variables);
  }
  char statuses[1] {'-'};
  dfaSetup(1, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(0);
  delete[] variable_indices;
  auto non_accepting_dfa = dfaBuild(statuses);
  return non_accepting_dfa;
}

DFA_ptr Automaton::DfaMakeAny(int num_of_variables, int* variable_indices) {
  if (variable_indices == nullptr) {
    variable_indices = getIndices(num_of_variables);
  }
  char statuses[1] {'+'};
  dfaSetup(1, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(0);
  delete[] variable_indices;
  auto non_accepting_dfa = dfaBuild(statuses);
  return non_accepting_dfa;
}

DFA_ptr Automaton::DfaMakeAnyButNotEmpty(int num_of_variables, int* variable_indices) {
  if (variable_indices == nullptr) {
    variable_indices = getIndices(num_of_variables);
  }
  char statuses[2] { '-', '+' };
  dfaSetup(2, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  delete[] variable_indices;
  auto any_dfa = dfaBuild(statuses);
  return any_dfa;
}

DFA_ptr Automaton::DfaIntersect(DFA_ptr dfa1, DFA_ptr dfa2) {
  auto intersect_dfa = dfaProduct(dfa1, dfa2, dfaAND);
  auto minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
  return minimized_dfa;
}

DFA_ptr Automaton::DfaUnion(DFA_ptr dfa1, DFA_ptr dfa2) {
  auto union_dfa = dfaProduct(dfa1, dfa2, dfaOR);
  auto minimized_dfa = dfaMinimize(union_dfa);
  dfaFree(union_dfa);
  return minimized_dfa;
}

DFA_ptr Automaton::DFAProjectAway(int index, DFA_ptr dfa) {
  auto result_dfa = dfaProject(dfa, (unsigned)index);
  auto tmp_dfa = result_dfa;
  result_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);
  return result_dfa;
}

DFA_ptr Automaton::DFAProjectTo(int index, int num_of_variables, DFA_ptr dfa) {
  auto result_dfa = dfaCopy(dfa);
  for (int i = 0 ; i < num_of_variables; ++i) {
    if (i != index) {
      auto tmp_dfa = result_dfa;
      result_dfa = Automaton::DFAProjectAway(i, tmp_dfa);
      dfaFree(tmp_dfa);
    }
  }

  int* indices_map = getIndices(num_of_variables);
  indices_map[index] = 0;
  indices_map[0] = index;
  dfaReplaceIndices(result_dfa, indices_map);
  delete[] indices_map;
  return result_dfa;
}

DFA_ptr Automaton::DfaL1ToL2(int start, int end, int num_of_variables, int *variable_indices) {
  int i, number_of_states;
  char *statuses;
  DFA *result=nullptr;
  if(variable_indices == nullptr) {
    variable_indices = getIndices(num_of_variables);
  }
  if (start <= -1 && end <= -1) {
    result = Automaton::DfaMakePhi(num_of_variables, variable_indices);
    delete[] variable_indices;
    return result;
  }
  if ( start <= -1 ) {
    start = 0; // -1 means no lower bound, zero is the minimum lower bound
  }
  if(end <= -1) { //accept everything after l1 steps
    number_of_states = start + 2; // add one sink state
    statuses = new char[number_of_states+1];
    dfaSetup(number_of_states, num_of_variables, variable_indices);

    //the 0 to start - 1 states(unaccepted)
    for( i = 0; i < start; i++){
      dfaAllocExceptions(0);
      dfaStoreState(i + 1);
      statuses[i] = '-';
    }
    // the start state
    dfaAllocExceptions(0);
    dfaStoreState(i);     // i == start
    statuses[i] = '+';    // i == start
    i++;
  } else {
    CHECK( end >= start);
    number_of_states = end + 2; // add one sink state
    statuses = new char[number_of_states+1];
    dfaSetup(number_of_states, num_of_variables, variable_indices);

    //the start to end states(accepted)
    for( i = 0; i <= end; i++){
      dfaAllocExceptions(0);
      dfaStoreState(i + 1);
      if(i >= start) {
        statuses[i] = '+';
      } else {
        statuses[i] = '-';
      }
    }
  }

  //the sink state
  dfaAllocExceptions(0);
  dfaStoreState(number_of_states - 1);  // sink state
  statuses[number_of_states - 1] = '-';   // i == end + 1 == number_of_states - 1
  statuses[number_of_states] = '\0';    // number_of_states == end + 2

  result=dfaBuild(statuses);
  delete[] statuses;
  delete[] variable_indices;
  if(start == 0) result->f[result->s] = 1;
  DFA *tmp = dfaMinimize(result);
  dfaFree(result);
  return tmp;
}

int* Automaton::getIndices(int num_of_variables, int extra_num_of_variables) {
  int size = num_of_variables + extra_num_of_variables;
  int* indices = new int[size];
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

std::string Automaton::getBinaryString(unsigned long number, int bit_length) {
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

void Automaton::minimize() {
  DFA_ptr tmp = this->dfa_;
  this->dfa_ = dfaMinimize(tmp);
  dfaFree(tmp);
  DVLOG(VLOG_LEVEL) << this->id_ << " = [" << this->id_ << "]->minimize()";
}

void Automaton::project(unsigned index) {
  DFA_ptr tmp = this->dfa_;
  this->dfa_ = dfaProject(tmp, index);
  dfaFree(tmp);

  if (index < (unsigned)(this->num_of_variables_ - 1)) {
    int* indices_map = new int[this->num_of_variables_];
    for (int i = 0, j = 0; i < this->num_of_variables_; i++) {
      if ((unsigned)i != index) {
        indices_map[i] = j;
        j++;
      }
    }
    dfaReplaceIndices(this->dfa_, indices_map);
    delete[] indices_map;
  }

  this->num_of_variables_ = this->num_of_variables_ - 1;

  delete this->variable_indices_;
  this->variable_indices_ = getIndices(num_of_variables_);
  DVLOG(VLOG_LEVEL) << this->id_ << " = [" << this->id_ << "]->project(" << index << ")";
}

bool Automaton::isStartState(int state_id) {
  return (this->dfa_->s == state_id);
}

bool Automaton::isSinkState(int state_id) {
  return (bdd_is_leaf(this->dfa_->bddm, this->dfa_->q[state_id])
          and (bdd_leaf_value(this->dfa_->bddm, this->dfa_->q[state_id]) == (unsigned) state_id)
          and this->dfa_->f[state_id] == -1);
}

bool Automaton::is_accepting_state(int state_id) {
  return (this->dfa_->f[state_id] == 1);
}

/**
 * @returns sink state number if exists, -1 otherwise
 */
int Automaton::getSinkState() {
  for (int i = 0; i < this->dfa_->ns; i++) {
    if (isSinkState(i)) {
      return i;
    }
  }

  return -1;
}

bool Automaton::hasIncomingTransition(int state) {
  for (int i = 0; i < this->dfa_->ns; i++) {
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
  for (int i = 0; i < this->dfa_->ns; i++) {
    if (is_accepting_state(i)) {
      state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[i]);
      while (pp) {
        if (pp->to == (unsigned) this->dfa_->s) {
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

  p = this->dfa_->q[state];
  nodes.push(p);
  while (not nodes.empty()) {
    p = nodes.top();
    nodes.pop();
    LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
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

   CHECK_EQ(num_of_variables_, exception.size());

   p = this->dfa_->q[state];

   for (int i = 0; i < num_of_variables_; i++) {
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
        while (current_transition.size() < (unsigned) num_of_variables_) {
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

Eigen::SparseMatrix<BigInteger> Automaton::GetCountMatrix() {
  if (is_count_matrix_cached_) {
    return count_matrix_;
  }

  std::vector<Eigen::Triplet<BigInteger>> entries;
  const int sink_state = getSinkState();
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
            const int exponent = num_of_variables_ - current_bdd_node.second;
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
      if (is_accepting_state(s)) {
        entries.push_back(Eigen::Triplet<BigInteger>(s, this->dfa_->ns, BigInteger(1)));
      }
    }
  }
  Eigen::SparseMatrix<BigInteger> count_matrix (this->dfa_->ns + 1, this->dfa_->ns + 1);
  count_matrix.setFromTriplets(entries.begin(), entries.end());
  count_matrix.makeCompressed();
  count_matrix_ = std::move(count_matrix);
  bound_and_initializer_vector_ = std::make_pair(0, Eigen::SparseVector<BigInteger> (this->dfa_->ns + 1));
  bound_and_initializer_vector_.second = count_matrix_.innerVector(this->dfa_->ns);
  is_count_matrix_cached_ = true;
  return count_matrix_;
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
 * TODO Reimplement
 *
 */
void Automaton::toDotAscii(bool print_sink, std::ostream& out) {

  print_sink = print_sink || (dfa_->ns == 1 and dfa_->f[0] == -1);
  int sink_state = getSinkState();

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
//  for (int i = 0; i < dfa->ns; i++) {
//    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
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
  unsigned* offsets = getIndices((unsigned) num_of_variables_);
  int no_free_vars = num_of_variables_;
  DFA_ptr a = this->dfa_;
  int sink = getSinkState();

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
  char **names = new char*[this->num_of_variables_];
  char *orders = new char[this->num_of_variables_];
  std::string name = "a";
  for (int i = 0; i < this->num_of_variables_; i++) {
    orders[i] = i;
    names[0] = &*name.begin();
  }

  dfaExport(this->dfa_, nullptr, this->num_of_variables_, names, orders);
}

DFA_ptr Automaton::importDFA(std::string file_name) {
  char **names = new char*[this->num_of_variables_];
  int ** orders = new int*[this->num_of_variables_];
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
