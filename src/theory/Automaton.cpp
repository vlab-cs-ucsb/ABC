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
const std::string Automaton::Name::INT = "IntAutomaton";
const std::string Automaton::Name::INTBOOl = "IntBoolAutomaton";
const std::string Automaton::Name::STRING = "StringAutomaton";

Automaton::Automaton(Automaton::Type type)
        : type(type), dfa(nullptr), num_of_variables(0), variable_indices(nullptr), id (Automaton::trace_id++) {
}

Automaton::Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables)
        : type(type), dfa(dfa), num_of_variables(num_of_variables), id (Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables, 1); // make indices one more to be safe
}

Automaton::Automaton(const Automaton& other)
        : type(other.type), dfa(dfaCopy(other.dfa)), num_of_variables(other.num_of_variables), id (Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables, 1); // make indices one more to be safe
}

Automaton::~Automaton() {
  if (dfa) {
    dfaFree(dfa);
    dfa = nullptr;
  }
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

unsigned long Automaton::getId() {
  return id;
}

DFA_ptr Automaton::getDFA() {
  return dfa;
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
    } else if (hasNextState(s, this->dfa->s)) {
      return false;
    }
  }
  return true;
}

bool Automaton::isCyclic() {

  bool is_cyclic = false;
  Graph_ptr graph = toGraph();
  is_cyclic = graph->isCyclic();
  delete graph;
  return is_cyclic;
}

/**
 * @returns graph representation of automaton
 */
Graph_ptr Automaton::toGraph() {
  Graph_ptr graph = new Graph();
  std::set<int>* states = nullptr;
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
    states = this->getNextStates(node->getID());
    for (int id : *states) {
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
  unsigned sink_state = (unsigned)this->getSinkState();
  bool is_accepting_single_word = true;
  bool is_final_state = false;
  int bit_counter = 0;

  for (int s = 0; s < this->dfa->ns; s++) {
    is_final_state = isAcceptingState(s);
    p = this->dfa->q[s];
    nodes.push_back(p);
    bit_stack.push_back(0);
    while (not nodes.empty()) {
      p = nodes.back(); nodes.pop_back();
      bit_counter = bit_stack.back(); bit_stack.pop_back();
      LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
      if (index == BDD_LEAF_INDEX) {
        if ( sink_state != l) {
          next_states[l]++;
          if ( bit_counter != num_of_variables  or (next_states[l] > 1) or (next_states.size() > 1) or is_final_state) {
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

std::string Automaton::getAnAcceptingWord() {
  char* result = isSingleton(this->dfa, num_of_variables, variable_indices);
  return std::string(result);
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
  dfaFree(tmp);
  DVLOG(VLOG_LEVEL) << this->id << " = [" << this->id << "]->minimize()";
}

void Automaton::project(unsigned index) {
  DFA_ptr tmp = this->dfa;
  this->dfa = dfaProject(tmp, index);
  dfaFree(tmp);
  this->num_of_variables = index;
  delete this->variable_indices;
  this->variable_indices = getIndices(num_of_variables);
  DVLOG(VLOG_LEVEL) << this->id << " = [" << this->id << "]->project()";
}

bool Automaton::isSinkState(int state_id) {
  return (bdd_is_leaf(this->dfa->bddm, this->dfa->q[state_id])
      and (bdd_leaf_value(this->dfa->bddm, this->dfa->q[state_id]) == (unsigned)state_id)
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

bool Automaton::hasNextState(int state, int search) {
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

AdjacencyList Automaton::getAdjacencyCountList() {
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
    for(int j = 0; j < leaf_count; j++) {
      reachable_states[j] = 0;
    }

    leaf_count = 0;
    for(int j = 0; j < this->dfa->ns; j++){
      transition_count[j]=0;
    }

    LOAD_lri(&dfa->bddm->node_table[i], l, r, index);
    // keep track of t and id as pair<id,t> in stack
    current_node.second = 0;
    current_node.first = dfa->q[i];

    node_stack.push(current_node);

    while(!node_stack.empty()) {
      top = node_stack.top();
      node_stack.pop();
      LOAD_lri(&this->dfa->bddm->node_table[top.first], l, r, index);
      if(index == BDD_LEAF_INDEX) {
        num_of_transitions = std::pow(2, (num_of_variables-top.second));
        if(!transition_count[l]) {
          reachable_states[leaf_count] = l;
          leaf_count++;
        }
        transition_count[l] += num_of_transitions;
      }
      else {
        lo_node.first = l;
        lo_node.second = top.second + 1;
        hi_node.first = r;
        hi_node.second = top.second + 1;
        node_stack.push(lo_node);
        node_stack.push(hi_node);
      }
    }

    for(int j = 0; j < leaf_count; j++){
      entry.first = i;
      entry.second = transition_count[reachable_states[j]];
      adjacency_count_list[reachable_states[j]].push_back(entry);
    }
  }

  return adjacency_count_list;
}

/**
 * TODO Refactor lib functions
 *  - find_sink
 *  - ....
 */
void Automaton::toDotAscii(bool print_sink, std::ostream& out) {
  paths state_paths, pp;
  trace_descr tp;

  int i, j, k, l, size, maxexp, sink;
  pCharPair *buffer;//array of charpairs references
  char *character;
  pCharPair **toTrans;//array for all states, each entry is an array of charpair references
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

  out << "\n init [shape = plaintext, label = \"\"];\n" <<
      " init -> " << dfa->s << ";\n";

  maxexp = 1 << num_of_variables;
  //TODO convert into c++ style memory management
  buffer = (pCharPair*) malloc(sizeof(pCharPair) * maxexp); //max no of chars from Si to Sj = 2^num_of_variables
  character = (char*) malloc(( num_of_variables+1) * sizeof(char));
  toTrans = (pCharPair**) malloc(sizeof(pCharPair*) * dfa->ns);//need this to gather all edges out to state Sj from Si
  for (i = 0; i < dfa->ns; i++) {
    toTrans[i] = (pCharPair*) malloc(maxexp * sizeof(pCharPair));
  }
  toTransIndecies = (int*) malloc(dfa->ns * sizeof(int));//for a state Si, how many edges out to each state Sj


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
      if (pp->to == (unsigned)sink && not print_sink){
        pp = pp->next;
        continue;
      }
      //get mona character on transition pp
      for (j = 0; j < num_of_variables; j++) {
        for (tp = pp->trace; tp && (tp->index != (unsigned)variable_indices[j]); tp = tp->next);

        if (tp) {
          if (tp->value)
            character[j] = '1';
          else
            character[j] = '0';
        } else
          character[j] = 'X';
      }
      character[j] = '\0';
      if (num_of_variables == 8){
        //break mona character into ranges of ascii chars (example: "0XXX000X" -> [\s-!], [0-1], [@-A], [P-Q])
        size = 0;
        getTransitionChars(character, num_of_variables, buffer, &size);
        //get current index
        k = toTransIndecies[pp->to];
        //print ranges
        for (l = 0; l < size; l++) {
          toTrans[pp->to][k++] = buffer[l];
          buffer[l] = 0;//do not free just detach
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
      l = 0;//to help breaking into new line
      //for each trans k on char/range from i to j
      for (k = 0; k < size; k++) {
        //print char/range
        if (print_label) {
          out << " " << ranges[k];
        }
        l += strlen(ranges[k]);
        if (l > 18){
          if (print_label) {
            out << "\\n";
          }
          l = 0;
        }
        else if (k < (size - 1)) {
          if (print_label) {
            out << ",";
          }
        }
        free(ranges[k]);
      }//for
      out << "\"];\n";
      if (size > 0)
        free(ranges);
    }
    //for each state free charRange
    //merge with loop above for better performance
    for (j = 0; j < dfa->ns; j++){
      if (j == sink && not print_sink) {
        continue;
      }
      size = toTransIndecies[j];
      for (k = 0; k < size; k++) {
        free(toTrans[j][k]);
      }
    }

    kill_paths(state_paths);
  }//end for each state

  free(character);
  free(buffer);
  for (i = 0; i < dfa->ns; i++){
    free(toTrans[i]);
  }
  free(toTrans);
  free(toTransIndecies);

  out << "}" << std::endl;
}



// TODO will be merge into one toDot function with above
void Automaton::toDot() {
  dfaPrintGraphviz(this->dfa, num_of_variables, getIndices((unsigned)num_of_variables));
}

void Automaton::printBDD(std::ostream& out) {
//  LOG(FATAL) << "implement me, fix headers";
  Table *table = tableInit();
  int sink = getSinkState();

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
    if ( (unsigned)(i+1) < table->noelems) {
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

int Automaton::inspectAuto(bool print_sink) {
  std::stringstream file_name;
  file_name << "./output/inspect_auto_" << name_counter++ << ".dot";
  std::string file = file_name.str();
  std::ofstream outfile(file.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file_name << std::endl;
    exit(2);
  }
  toDotAscii(print_sink, outfile);
  std::string dot_cmd("xdot " + file + " &");
  return std::system(dot_cmd.c_str());
}

} /* namespace Theory */
} /* namespace Vlab */
