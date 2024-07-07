/*
 * Automaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_AUTOMATON_H_
#define THEORY_AUTOMATON_H_

#include <algorithm>
#include <array>
#include <random>
#include <ctime>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <iostream>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>
#include <queue>

#include <glog/logging.h>
#include <mona/bdd.h>
#include <mona/bdd_external.h>
#include <mona/dfa.h>
#include <mona/mem.h>

#include "../utils/Cmd.h"
#include "../utils/Math.h"
#include "../utils/RegularExpression.h"
#include "../boost/multiprecision/cpp_int.hpp"
#include "../Eigen/SparseCore"
#include "Graph.h"
#include "GraphNode.h"
#include "options/Theory.h"
#include "SymbolicCounter.h"
#include "Formula.h"

namespace Vlab {
namespace Theory {

class Automaton;
using Automaton_ptr = Automaton*;
using DFA_ptr = DFA*;

using Node = std::pair<int ,int>; // pair.first = node id, pair.second node data
using BigInteger = boost::multiprecision::cpp_int;
using NextState = std::pair<int, std::vector<bool>>;

// for toDotAscii from libstranger
typedef struct CharPair_ {
	unsigned char first;
	unsigned char last;
} CharPair, *pCharPair;

struct int_type{
		int value;
		struct int_type	*next;
};

struct int_list_type{
		int count;
		struct	int_type	*head;
		struct	int_type	*tail;
};

class Automaton {
public:
  enum class Type
    : int {
      NONE = 0, BOOL, UNARY, INT, BINARYINT, STRING, MULTITRACK
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
  int get_number_of_bdd_variables();

  /**
   * Checks if an automaton accepts nothing
   * @return
   */
  bool IsEmptyLanguage() const;

  /**
   * Checks if only the initial state is accepting and any input is rejected
   * @return
   */
  bool IsOnlyAcceptingEmptyInput() const;

  /**
   * Checks if initial state is an accepting state
   * @return
   */
  bool IsInitialStateAccepting() const;

  /**
   * Checks if the given state is an accepting state
   * @param state_id
   * @return
   */
  bool IsAcceptingState(const int state_id) const;

  /**
   * Checks if the given state is the initial state
   * @param state_id
   * @return
   */
  bool IsInitialState(const int state_id) const;

  /**
   * Checks if the given state is a sink state
   * @param state_id
   * @return
   */
  bool IsSinkState(const int state_id) const;

  /**
   * Checks if there is a one direct transtion from a given state to a given state
   * @param from_state
   * @param to_state
   * @return
   */
  bool IsOneStepAway(const int from_state, const int to_state) const;

  /**
   * Checks if the current automaton accepts the same language with the other automaton
   * @param other_auto
   * @return
   */
  bool IsEqual(const Automaton_ptr other_automaton) const;

  /**
   * Gets the initial state id
   * @return
   */
  int GetInitialState() const;

  /**
   * Gets the sink state
   * @return
   */
  int GetSinkState() const;

  /**
   * Generates a specific type of automaton that wraps dfa instance
   * @param dfa
   * @param number_of_variables
   * @return
   */
  virtual Automaton_ptr MakeAutomaton(DFA_ptr dfa, Formula_ptr formula, const int number_of_variables) = 0;

  /**
   * Complements an automaton
   * @return
   */
  virtual Automaton_ptr Complement();

  /**
   * Generates an automaton that is the result of union product of the two automata
   * @param other_automaton
   * @return
   */
  virtual Automaton_ptr Union(Automaton_ptr other_automaton);

  /**
   * Generates an automaton that is the result of intersection product of the two automata
   * @param other_automaton
   * @return
   */
  virtual Automaton_ptr Intersect(Automaton_ptr other_automaton);

  /**
   * Generates an automaton that accept strings accepted by the current automaton but not by the other automaton
   * @param other_automaton
   * @return
   */
  virtual Automaton_ptr Difference(Automaton_ptr other_automaton);

  /**
   * TODO Fix empty string bug that happens in case (concat /.{0,1}/ /{1,1}/)
   * Generates an automaton that is the concatenation of the current automaton with the other automaton
   * @param other_automaton
   * @return
   */
  virtual Automaton_ptr Concat(Automaton_ptr other_automaton);

  bool isCyclic();
  bool isInCycle(int state);
  bool isStateReachableFrom(int search_state, int from_state);
  BigInteger Count(const unsigned long bound);
  BigInteger CountByMatrixMultiplication(const unsigned long bound);
  virtual BigInteger SymbolicCount(int bound, bool count_less_than_or_equal_to_bound = true);
  virtual BigInteger SymbolicCount(double bound, bool count_less_than_or_equal_to_bound = true);
  virtual std::map<std::string,std::vector<std::string>> GetModelsWithinBound(int num_models, int bound);
  SymbolicCounter GetSymbolicCounter();
  static void SetCountBoundExact(bool value);

  class Name {
  public:
    static const std::string NONE;
    static const std::string BOOL;
    static const std::string UNARY;
    static const std::string INT;
    static const std::string STRING;
    static const std::string BINARYINT;
  };

  Graph_ptr toGraph();

  void toDotAscii(bool print_sink = false, std::ostream& out = std::cout);
  // TODO merge toDot methods into one with options
  void ToDot(std::ostream& out = std::cout, bool print_sink = false);
  void toBDD(std::ostream& out = std::cout);
  void exportDfa(std::string file_name);
  DFA_ptr importDFA(std::string file_name);
  int inspectAuto(bool print_sink = false, bool force_mona_format = false);
  int inspectBDD();

  Util::RegularExpression_ptr DFAToRE();


  friend std::ostream& operator<<(std::ostream& os, const Automaton& automaton);

  static void CleanUp();

protected:

  /**
   * Checks if a minimized dfa accepts nothing
   * @param dfa
   * @return
   */
  static bool DFAIsMinimizedEmtpy(const DFA_ptr minimized_dfa);

  /**
   * Checks if a dfa accepts nothing
   * @param dfa
   * @return
   */
  static bool DFAIsEmpty(const DFA_ptr dfa);

  /**
   * Checks if a minimzed dfa only accepts the initial state without any input
   * @param minimized_dfa
   * @return
   */
  static bool DFAIsMinimizedOnlyAcceptingEmptyInput(const DFA_ptr minimized_dfa);

  /**
   * Checks if a state is an accepting state in a given dfa
   * @param state_id
   * @return
   */
  static bool DFAIsAcceptingState(const DFA_ptr dfa, const int state_id);

  /**
   * Checks if a state is the initial state in a given dfa
   * @param dfa
   * @param state_id
   * @return
   */
  static bool DFAIsInitialState(const DFA_ptr dfa, const int state_id);

  /**
   * Checks if a state is a sink state in a given dfa
   * @param dfa
   * @param state_id
   * @return
   */
  static bool DFAIsSinkState(const DFA_ptr dfa, const int state_id);

  /**
   * Checks if a given dfa has a transition from a given state to a given state
   * @param dfa
   * @param from_state
   * @param to_state
   * @return
   */
  static bool DFAIsOneStepAway(const DFA_ptr dfa, const int from_state, const int to_state);

  /**
   * Checks if the given two dfas accepts the same language
   * @param dfa1
   * @param dfa2
   * @return
   */
  static bool DFAIsEqual(const DFA_ptr dfa1, const DFA_ptr dfa2);

  /**
   * Gets the initial state of the given dfa
   * @param dfa
   * @return
   */
  static int DFAGetInitialState(const DFA_ptr dfa);

  /**
   * Gets the sinks of the given dfa
   * @param dfa
   * @return sink state or -1 if not exists
   */
  static int DFAGetSinkState(const DFA_ptr dfa);

  /**
   * Generates a dfa that accepts nothing
   * @param number_of_bdd_variables
   * @return
   */
  static DFA_ptr DFAMakePhi(const int number_of_bdd_variables);

  /**
   * Generates a dfa that accepts any input
   * @param number_of_bdd_variables
   * @return
   */
  static DFA_ptr DFAMakeAny(const int number_of_bdd_variables);

  /**
   * Generates a dfa that accepts any input except one
   * @param number_of_bdd_variables
   * @return
   */
  static DFA_ptr DFAMakeAnyButNotEmpty(const int number_of_bdd_variables);

  /**
   * Generates a dfa that has an accepting initial state without any loop
   * @param number_of_bdd_variables
   * @return
   */
  static DFA_ptr DFAMakeEmpty(const int number_of_bdd_variables);

  /**
   * Generates a dfa that accepts strings that are not accepted by the given dfa
   * @param
   * @return
   */
  static DFA_ptr DFAComplement(const DFA_ptr dfa);

  /**
   * Generates a dfa with the union of the two given dfas
   * @param dfa1
   * @param dfa2
   * @return
   */
  static DFA_ptr DFAUnion(const DFA_ptr dfa1, const DFA_ptr dfa2);

  /**
   * Generates a dfa with the intersection of the two given dfas
   * @param dfa1
   * @param dfa2
   * @return
   */
  static DFA_ptr DFAIntersect(const DFA_ptr dfa1, const DFA_ptr dfa2);

  /**
   * Generates a dfa that accepts strings that are accepted by dfa1 but not by dfa2
   * @param dfa1
   * @param dfa2
   * @return
   */
  static DFA_ptr DFADifference(const DFA_ptr dfa1, DFA_ptr dfa2);

  /**
   * Generates a dfa where the bdd variable in the given index of the given dfa projected away
   * @returns a minimized dfa
   */
  static DFA_ptr DFAProjectAway(const DFA_ptr dfa, const int index);

  /**
	 * Generates a dfa where the bdd variables in the given indicies of the given dfa projected away
	 * @returns a minimized dfa
	 */
	static DFA_ptr DFAProjectAway(const DFA_ptr dfa, std::vector<int> map, const std::vector<int> indices);

  /**
   * Generates a dfa where the bdd variable in the given index of the given dfa projected away and the index mapping is done again
   * @param dfa
   * @param number_of_bdd_variables
   * @param indices
   * @return
   */
  static DFA_ptr DFAProjectAwayAndReMap(const DFA_ptr dfa, const int number_of_bdd_variables, const int index);

  /**
   * Generates a dfa by projecting all bits except one away
   * @param dfa
   * @param number_of_bdd_variables
   * @param index
   * @return
   */
  static DFA_ptr DFAProjectTo(const DFA_ptr dfa, const int number_of_bdd_variables, const int index);

  /**
	 * Generates a dfa by projecting all bits except those in indices away
	 * @param dfa
	 * @param number_of_bdd_variables
	 * @param indices
	 * @return
	 */
	static DFA_ptr DFAProjectTo(const DFA_ptr dfa, const int number_of_bdd_variables, const std::vector<int> indices);

  /**
   * Generates a dfa that accepts any input that has length between start and end inclusive
   * @param start
   * @param end
   * @param number_of_bdd_variables
   * @return
   */
  static DFA_ptr DFAMakeAcceptingAnyWithInRange(const int start, const int end, const int number_of_bdd_variables);

  /**
   * Generates a dfa that accepts any input after reading the given number of inputs
   * @param start
   * @param number_of_bdd_variables
   * @return
   */
  static DFA_ptr DFAMakeAcceptingAnyAfterLength(const int length, const int number_of_bdd_variables);

  /**
   * Gets set of transitions between two states
   * @param dfa
   * @param from
   * @param to
   * @param num_of_variables
   * @return
   */
  static std::set<std::string> DFAGetTransitionsFromTo(DFA_ptr dfa, const int from, const int to, const int num_of_variables);

  /**
	 * Generates a dfa that accepts that accepts the concatenated language of dfa1 and dfa2
	 * @param dfa1
	 * @param dfa2
	 * @param number_of_bdd_variables
	 * @return
	 */
  static DFA_ptr DFAConcat(const DFA_ptr dfa1, const DFA_ptr dfa2, const int number_of_bdd_variables);

  bool isAcceptingSingleWord();
  // TODO update it to work for non-accepting inputs
  std::vector<bool>* getAnAcceptingWord(std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
  std::vector<bool>* getAnAcceptingWordRandom(std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
  static std::vector<char> decodeException(std::vector<char>& exception);
  static std::vector<std::string> ExpandException(std::string exception);
  virtual void add_print_label(std::ostream& out);

  /**
   * Uses a cache for bdd variable indices.
   * We use a fixed ordering in all automata we generate
   * @param number_of_bdd_variables
   * @return
   */
  static int* GetBddVariableIndices(const int number_of_bdd_variables);

  /**
   * Creates bdd variable indices
   * @param number_of_bdd_variables
   * @return bdd variable indices in a fixed order
   */
  static int* CreateBddVariableIndices(const int number_of_bdd_variables);

  // TODO remove vector<char> version of binary format and use string version below
  static std::vector<char> GetBinaryFormat(unsigned long n, int bit_length);
  static std::vector<char> GetReversedBinaryFormat(unsigned long n, int bit_length);

  static std::string GetBinaryStringMSB(unsigned long n, int bit_length);

  // TODO return string instead of vector<char>
  static std::vector<char> getReservedWord(char last_char, int length, bool extra_bit = false);
  void Minimize();
  void ProjectAway(unsigned index);

  bool hasIncomingTransition(int state);
  // todo will remove temp function
  static bool TEMPisStartStateReachableFromAnAcceptingState(DFA_ptr dfa);

  std::vector<std::pair<int,std::vector<char>>> GetNextTransitions(int state);
  int getNextState(int state, std::vector<char>& exception);
  std::set<int> getNextStates(int state);
  std::vector<NextState> getNextStatesOrdered(int state, std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
  std::set<int> getStatesReachableBy(int walk);
  std::set<int> getStatesReachableBy(int min_walk, int max_walk);
  bool getAnAcceptingWord(NextState& state, std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
  

  virtual void SetSymbolicCounter();
  virtual void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& mm);
  void generateGFScript(int bound, std::ostream& out = std::cout, bool count_less_than_or_equal_to_bound = true);
  void generateMatrixScript(int bound, std::ostream& out = std::cout, bool count_less_than_or_equal_to_bound = true);


  bool isCyclic(int state, std::map<int, bool>& is_discovered, std::map<int, bool>& is_stack_member);
  bool isStateReachableFrom(int search_state, int from_state, std::map<int, bool>& is_stack_member);

  /*
   * Operations from LIBSTRANGER
   */
  void getTransitionCharsHelper(pCharPair result[], char* transitions, int* indexInResult, int currentBit, int var);
  void getTransitionChars(char* transitions, int var, pCharPair result[], int* pSize);
  char** mergeCharRanges(pCharPair charRanges[], int* p_size);
  void charToAsciiDigits(unsigned char ci, char s[]);
  void charToAscii(char* asciiVal, unsigned char c);
  void fillOutCharRange(char* range, char firstChar, char lastChar);
  static char* bintostr(unsigned long, int k);
  unsigned char strtobin(char* binChar, int var);
  static int find_sink(DFA_ptr dfa);

  virtual Formula_ptr GetFormula() = 0;






  /*
   * Operations for ToLower/ToUpper/PreToLower/PreToUpper
   * TODO: currently stranger code, refactor
   */

  static void getUpperCaseCharsHelper(char** result, char* transitions, int* indexInResult, int currentBit, int var, char* prev);
  static void getLowerUpperCaseCharsPrePostHelper(char** result, char* transitions, int* indexInResult, int currentBit, int var, char* prev, boolean lowerCase, boolean preImage);
  /**
   * returns same chars in transitions unless char is capital in which case it is converted into small
   * or visa versa
   * examples:
   * A=01000001 -> a=[011000011]
   * {@, A, B, C ,D, E, F, G}=01000XXX -> {@, a, b, c, d, e, f, g}=[010000000, 011000011, 0110001X1, 011001XX1]
   * extrabit will be used. 0 for original letters, 1 for new small letters (converted from capital) to differentiate from original small chars
   */
  static void getLowerUpperCaseCharsPrePost(char* transitions, int var, char** result, int* pSize, boolean lowerCase, boolean preImage);
  /**
   * This functions models any function that changes all capital letters in a string to small ones (for example strtolower in php)
   * M: dfa to process
   * var: number of bits per character(for ASCII it is 8 bits)
   * indices: the indices
   * output: return D such that L(D) = { W_1S_1W_2S2..W_nS_n | W_1C_1W_2C2..W_nC_n element_of L(M) && W_i element_of Sigma* && S_i, C_i element_of Sigma && S_i = LowerCase(C_i)}
   */
  static DFA* dfaPrePostToLowerUpperCaseHelper(DFA* M, int var, int* oldIndices, boolean lowerCase, boolean preImage);

  static DFA* dfaToLowerCase(DFA* M, int var, int* indices);
  static DFA* dfaToUpperCase(DFA* M, int var, int* indices);
  static DFA* dfaPreToLowerCase(DFA* M, int var, int* indices);
  static DFA* dfaPreToUpperCase(DFA* M, int var, int* indices);


  /*
   * Operations for replace
   * TODO: currently stranger code, refactor
   */

  static DFA_ptr DFAExtendExtrabit(DFA_ptr M, int var);

  static bool check_emptiness_minimized(DFA *M);
  static int check_emptiness(DFA_ptr M1, int var, int* indices);
  static int check_intersection(DFA_ptr M1, DFA_ptr M2, int var, int* indices);
  static int check_equivalence(DFA_ptr M1, DFA_ptr M2, int var, int* indices);
  static char *getSharp1(int k);
  static char *getSharp0(int k);
  static char *getSharp1WithExtraBit(int k);
  static char *getSharp0WithExtraBit(int k);
  static char * getArbitraryStringWithExtraBit(int k);

  static DFA * dfaAllStringASCIIExceptReserveWords(int var, int *indices);
  static DFA_ptr dfaSharpStringWithExtraBit(int var, int *indices);
  static DFA_ptr dfa_star_M_star(DFA_ptr M, int var, int *indices);

  static DFA_ptr dfa_general_replace_extrabit(DFA* M1, DFA* M2, DFA* M3, int var, int* indices);
  static DFA_ptr dfa_replace_step1_duplicate(DFA *M, int var, int *indices);
  static DFA_ptr dfa_replace_step2_match_compliment(DFA *M, int var, int *indices);
  static DFA *dfa_replace_step3_general_replace(DFA *M, DFA* Mr, int var, int *indices);

  static DFA *dfa_replace_delete(DFA *M, int var, int *oldindices);
  static DFA *dfa_replace_M_dot(DFA *M, DFA* Mr, int var, int *oldindices);
  static DFA *dfa_replace_M_arbitrary(DFA *M, DFA *Mr, int var, int *oldindices);

  static struct int_list_type **get_match_exclude_self(DFA *M, int var, int *indices);
  static int exist_sharp1_path(DFA *M, int start, int var);
  static int* allocateAscIIIndexWithExtraBit(int length);
  static struct int_list_type *reachable_closure(DFA *M, int start, int var,int *indices);

  // list stuff
  static struct int_list_type * enqueue(struct int_list_type *list, int value);
  static int dequeue(struct int_list_type *list);
  static void free_ilt(struct int_list_type *list);
  static struct int_type *new_it(int i);
  static struct int_list_type *new_ilt();
  static struct int_list_type *add_data(struct int_list_type *list, struct int_type *data);
  static int check_value(struct int_list_type *list, int value);

  static int get_maxcount(struct int_list_type **pairs, int size);
  static int get_hsig(int i);
  static void set_bitvalue(char *bit, int length, int value);
  static int* allocateArbitraryIndex(int length);
  static DFA *dfaDot(int var, int *indices);

  static int count_accepted_chars(DFA* M);
  static void set_accepted_chars(DFA* M,char** apath, int numchars, int var, int* indices);
  static struct int_list_type **get_match(DFA *M, int var, int *indices);
  static int get_number_of_sharp1_state(struct int_list_type **pairs, int size);
  static void initial_out_info(DFA* M, int* num, int* final, char*** bin, int** to, int var, int aux, int* indices);
  static DFA* dfa_pre_replace_str(DFA* M1, DFA* M2, char *str, int var, int* indices);
  static DFA *dfa_construct_string(char *reg, int var, int *indices);
  //static char *bintostr(unsigned long n, int k);
  static DFA *dfa_insert_M_dot(DFA *M, DFA* Mr, int var, int *indices);
  static DFA *dfa_insert_M_arbitrary(DFA *M, DFA *Mr, int var, int *indices);
  static DFA *dfa_insert_everywhere(DFA *M, DFA* Mr, int var, int *indices);

  static unsigned long next_id;

  /**
   * Bdd variable indices cache used in MONA dfa manipulation
   */
  static std::unordered_map<int, int*> bdd_variable_indices;

  /**
   * Automaton id used for debuggin purposes
   */
  unsigned long id_;
  static int next_state;

  const Automaton::Type type_; // TODO remove type


  bool is_counter_cached_;

  /**
   * Number of bdd variables used in MONA representation
   */
  int num_of_bdd_variables_;

  /**
   * Mona dfa pointer
   */
  DFA_ptr dfa_;

  /**
   * Model counter function
   */
  SymbolicCounter counter_;

  static bool count_bound_exact_;
private:
  char* getAnExample(bool accepting=true); // MONA version
  // for debugging
  static int name_counter;
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_AUTOMATON_H_ */
