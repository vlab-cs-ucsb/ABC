/*
 * Automaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_AUTOMATON_H_
#define THEORY_AUTOMATON_H_

#include <string>
#include <sstream>
#include <iostream>
#include <fstream>
#include <array>
#include <vector>
#include <map>
#include <unordered_map>
#include <set>
#include <stack>
#include <queue>
#include <cmath>
#include <functional>

#include <glog/logging.h>
//#include <mona/config.h>
//#include <mona/mem.h>
//#include <mona/bdd.h>
//#include <mona/bdd_external.h>
//#include <mona/bdd_dump.h>
//#include <mona/dfa.h>
#include <stranger/stranger.h>
#include <stranger/stranger_lib_internal.h>
#include "options/Theory.h"
#include "utils/RegularExpression.h"
#include "utils/Cmd.h"
#include "Graph.h"
#include "DAGraph.h"
#include "SemilinearSet.h"

namespace Vlab {
namespace Theory {

class Automaton;
typedef Automaton* Automaton_ptr;
typedef DFA* DFA_ptr;

typedef std::pair<int ,int> Node; // pair.first = node id, pair.second node data
typedef std::vector<Node> NodeVector;
typedef std::vector<NodeVector> AdjacencyList;
typedef std::pair<int, std::vector<bool>> NextState;

class Automaton {
public:
  enum class Type
    : int {
      NONE = 0, BOOL, UNARY, INT, INTBOOl, BINARYINT, STRING
  };

  Automaton(Automaton::Type type);
  Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables);
  Automaton(const Automaton&);
  virtual ~Automaton();
  virtual Automaton_ptr clone() const = 0;

  virtual std::string str() const;
  virtual Automaton::Type getType() const;
  unsigned long getId();
  DFA_ptr getDFA();
  int getNumberOfVariables();
  int* getVariableIndices();

  class Name {
  public:
    static const std::string NONE;
    static const std::string BOOL;
    static const std::string UNARY;
    static const std::string INT;
    static const std::string INTBOOl;
    static const std::string STRING;
    static const std::string BINARYINT;
  };

  bool checkEquivalence(Automaton_ptr other_auto);
  bool isEmptyLanguage();
  bool isInitialStateAccepting();
  bool isOnlyInitialStateAccepting();
  bool isCyclic();
  bool isInCycle(int state);
  bool isStateReachableFrom(int search_state, int from_state);
  virtual std::string count(int bound, bool count_less_than_or_equal_to_bound = true);

  Graph_ptr toGraph();

  void toDotAscii(bool print_sink = false, std::ostream& out = std::cout);
  // TODO merge toDot methods into one with options
  void toDot(std::ostream& out = std::cout, bool print_sink = false);
  void toBDD(std::ostream& out = std::cout);
  void exportDfa(std::string file_name);
  DFA_ptr importDFA(std::string file_name);
  int inspectAuto(bool print_sink = false, bool force_mona_format = false);
  int inspectBDD();

  friend std::ostream& operator<<(std::ostream& os, const Automaton& automaton);
protected:
  static DFA_ptr makePhi(int num_of_variables, int* variable_indices);

  bool isAcceptingSingleWord();
  // TODO update it to work for non-accepting inputs
  std::vector<bool>* getAnAcceptingWord(std::function<bool(unsigned& index)> next_node_heuristic = nullptr);


  static int* getIndices(int num_of_variables, int extra_num_of_variables = 0);
  static unsigned* getIndices(unsigned num_of_variables, unsigned extra_num_of_variables = 0);
  static char* binaryFormat(unsigned long n, int bit_length);
  static std::vector<char> getBinaryFormat(unsigned n, int bit_length);
  static std::vector<char> getReservedWord(char last_char, int length, bool extra_bit = false);
  void minimize();
  void project(unsigned index);

  bool isStartState(int state_id);
  bool isSinkState(int state_id);
  bool isAcceptingState(int state_id);
  int getSinkState();
  bool hasIncomingTransition(int state);
  bool isStartStateReachableFromAnAcceptingState();
  bool hasNextState(int state, int search);
  int getNextState(int state, std::vector<char>& exception);
  std::set<int>* getNextStates(int state);
  std::vector<NextState> getNextStatesOrdered(int state, std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
  bool getAnAcceptingWord(NextState& state, std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
  AdjacencyList getAdjacencyCountList(bool count_reserved_words = true);
  void addReservedWordsToCount(AdjacencyList& adjaceny_count_list);
  void generateGFScript(int bound, std::ostream& out = std::cout, bool count_less_than_or_equal_to_bound = true);
  void generateMatrixScript(int bound, std::ostream& out = std::cout, bool count_less_than_or_equal_to_bound = true);
  void preProcessAdjacencyList(AdjacencyList& adjaceny_count_list);


  bool isCyclic(int state, std::map<int, bool>& is_discovered, std::map<int, bool>& is_stack_member);
  bool isStateReachableFrom(int search_state, int from_state, std::map<int, bool>& is_stack_member);

  const Automaton::Type type;
  DFA_ptr dfa;
  int num_of_variables;
  int* variable_indices;
  unsigned long id;
  static unsigned long trace_id;
private:
  char* getAnExample(bool accepting=true); // MONA version
  static int name_counter;
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_AUTOMATON_H_ */
