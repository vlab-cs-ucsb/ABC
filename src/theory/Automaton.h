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
#include <set>
#include <stack>
#include <queue>

#include <glog/logging.h>
//#include <mona/config.h>
//#include <mona/mem.h>
//#include <mona/bdd.h>
//#include <mona/bdd_external.h>
//#include <mona/bdd_dump.h>
//#include <mona/dfa.h>
#include <stranger.h>
#include <stranger_lib_internal.h>
#include "../utils/RegularExpression.h"
#include "Graph.h"
#include "DAGraph.h"


#include "utils.h"

namespace Vlab {
namespace Theory {

class Automaton;
typedef Automaton* Automaton_ptr;
typedef DFA* DFA_ptr;

class Automaton {
public:
  enum class Type
    : int {
      NONE = 0, BOOL, INT, INTBOOl, STRING
  };

  Automaton(Automaton::Type type);
  Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables);
  Automaton(const Automaton&);
  virtual ~Automaton();
  virtual Automaton_ptr clone() const = 0;

  virtual std::string str() const;
  virtual Automaton::Type getType() const;

  class Name {
  public:
    static const std::string NONE;
    static const std::string BOOL;
    static const std::string INT;
    static const std::string INTBOOl;
    static const std::string STRING;
  };

  bool checkEquivalence(Automaton_ptr other_auto);
  bool isEmptyLanguage();
  bool isInitialStateAccepting();
  bool isOnlyInitialStateAccepting();
  bool isCyclic();

  Graph_ptr toGraph();

  friend std::ostream& operator<<(std::ostream& os, const Automaton& automaton);

protected:
  static DFA_ptr makePhi(int num_of_variables, int* variable_indices);

  bool isAcceptingSingleWord();
  // TODO refactor to work for general case
  std::string getAnAcceptingWord();

  static int* getIndices(int num_of_variables, int extra_num_of_variables = 0);
  static unsigned* getIndices(unsigned num_of_variables, unsigned extra_num_of_variables = 0);

  static std::vector<char> getReservedWord(char last_char, int length, bool extra_bit = false);
  void minimize();
  void project(unsigned num_of_variables);

  bool isSinkState(int state_id);
  bool isAcceptingState(int state_id);
  int getSinkState();
  bool isStartStateReachable();
  bool hasNextStateFrom(int state, int search);
  std::set<int>* getNextStates(int state);

  const Automaton::Type type;
  DFA_ptr dfa;
  int num_of_variables;
  int* variable_indices;
  unsigned long id;
  static unsigned long trace_id;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_AUTOMATON_H_ */
