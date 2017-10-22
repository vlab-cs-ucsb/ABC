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

#include <glog/logging.h>
#include <mona/bdd.h>
#include <mona/bdd_external.h>
#include <mona/dfa.h>
#include <mona/mem.h>

#include "../utils/Cmd.h"
#include "../utils/Math.h"
#include "../boost/multiprecision/cpp_int.hpp"
#include "../Eigen/SparseCore"
#include "Graph.h"
#include "GraphNode.h"
#include "libs/MONALib.h"
#include "options/Theory.h"
#include "SymbolicCounter.h"

namespace Vlab
{
  namespace Theory
  {

    class Automaton;
    using Automaton_ptr = Automaton*;

    using Node = std::pair<int ,int>;
    // pair.first = node id, pair.second node data
    using BigInteger = boost::multiprecision::cpp_int;
    using NextState = std::pair<int, std::vector<bool>>;

// for toDotAscii from libstranger
    typedef struct CharPair_
    {
        unsigned char first;
        unsigned char last;
    } CharPair, *pCharPair;

    class Automaton
    {
       public:

        /**
         * Use this class to build an automaton.
         */
        class Builder;

        /**
         * Default constructor.
         */
        Automaton();

        /**
         * Constructs an automaton given the dfa and the number of variables.
         * @param dfa
         * @param num_of_variables
         */
        Automaton(Libs::MONALib::DFA_ptr dfa, int number_of_variables);

        /**
         * Copy constructor.
         * @param
         */
        Automaton(const Automaton&);

        /**
         * Destructor.
         */
        virtual ~Automaton();

        /**
         * Generates a clone copy of the current automaton.
         * @return
         */
        virtual Automaton_ptr Clone() const = 0;

        /**
         * Prints the actual type and the details of the automaton.
         * @return
         */
        virtual std::string Str() const;

        /**
         * Gets the id of the automaton.
         * Id is used for debugging and logging purposes.
         */
        unsigned long GetId() const;

        /**
         * Gets underlaying dfa representation. Currently we only use MONA dfa.
         * @return
         */
        Libs::MONALib::DFA_ptr GetDFA() const;

        /**
         * Gets number of states.
         * @return
         */
        int GetNumberOfStates() const;

        /**
         * Gets number of bdd variables used in the current automaton representation.
         * @return
         */
        int GetNumberOfBddVariables() const;

        /**
         * Gets the initial state id.
         * @return
         */
        int GetInitialState() const;

        /**
         * Gets the sink state.
         * @return
         */
        int GetSinkState() const;

        /**
         * Checks if an automaton accepts nothing.
         * @return
         */
        bool IsEmptyLanguage() const;

        /**
         * Checks if only the initial state is accepting and any input is rejected.
         * @return
         */
        bool IsOnlyAcceptingEmptyInput() const;

        /**
         * Checks if the given state is an accepting state.
         * @param state_id
         * @return
         */
        bool IsAcceptingState(const int state_id) const;

        /**
         * Checks if the given state is the initial state.
         * @param state_id
         * @return
         */
        bool IsInitialState(const int state_id) const;

        /**
         * Checks if the given state is a sink state.
         * @param state_id
         * @return
         */
        bool IsSinkState(const int state_id) const;

        /**
         * Checks if initial state is an accepting state.
         * @return
         */
        bool IsInitialStateAccepting() const;

        /**
         * Checks if there is a one direct transtion from a given state to a given state.
         * @param from_state
         * @param to_state
         * @return
         */
        bool IsOneStepAway(const int from_state, const int to_state) const;

        /**
         * Checks if the current automaton accepts the same language with the other automaton.
         * @param other_auto
         * @return
         */
        bool IsEqual(const Automaton_ptr other_automaton) const;

        /**
         * Generates a specific type of automaton that wraps dfa instance.
         * @param dfa
         * @param number_of_variables
         * @return
         */
        virtual Automaton_ptr MakeAutomaton(Libs::MONALib::DFA_ptr dfa, const int number_of_variables) const = 0;

        /**
         * Complements an automaton
         * @return
         */
        virtual Automaton_ptr Complement() const;

        /**
         * Generates an automaton that is the result of union product of the two automata.
         * @param other_automaton
         * @return
         */
        virtual Automaton_ptr Union(Automaton_ptr other_automaton) const;

        /**
         * Generates an automaton that is the result of intersection product of the two automata.
         * @param other_automaton
         * @return
         */
        virtual Automaton_ptr Intersect(Automaton_ptr other_automaton) const;

        /**
         * Generates an automaton that accept strings accepted by the current automaton but not by the other automaton.
         * @param other_automaton
         * @return
         */
        virtual Automaton_ptr Difference(Automaton_ptr other_automaton) const;

        /**
         * TODO Fix empty string bug that happens in case (concat /.{0,1}/ /{1,1}/)
         * Generates an automaton that is the concatenation of the current automaton with the other automaton.
         * @param other_automaton
         * @return
         */
        virtual Automaton_ptr Concat(Automaton_ptr other_automaton) const;

        /**
         * Generates an automaton that accepts suffixes of the strings accepted by the current automaton.
         * @return
         */
        virtual Automaton_ptr Suffixes() const;

        /**
         * TODO fix comment
         * Generates an automaton that accepts suffixes of the strings accepted by the current automaton and starts at the indices between start and end.
         * @param start
         * @param end
         * @return
         */
        virtual Automaton_ptr SuffixesFromTo(const int from_index, const int end_index) const;

        /**
         * Generates an automaton that accepts suffixes of the strings accepted by the current automaton and starts at the given index.
         * @param index
         * @return
         */
        virtual Automaton_ptr SuffixesAtIndex(const int index) const;

        /**
         * Generates an automaton that accepts suffixes of the strings accepted by the current automaton and starts at the indices after/at the given index.
         * @param start
         * @return
         */
        virtual Automaton_ptr SuffixesFromIndex(const int index) const;

        /**
         * Generates an automaton that accepts prefixes of the strings accepted by the current automaton.
         * @return
         */
        virtual Automaton_ptr Prefixes() const;

        /**
         * Generates an automaton that accepts prefixes of the strings accepted by the current automaton and starts at the indices before/at the given index.
         * @param end
         * @return
         */
        virtual Automaton_ptr PrefixesUntilIndex(const int index) const;

        /**
         * Generates an automaton that accepts prefixes of the strings accepted by the current automaton and starts at the given index.
         * @param index
         * @return
         */
        virtual Automaton_ptr PrefixesAtIndex(const int index) const;

        /**
         * Generates an automaton that accepts substrings of the strings accepted by the current automaton.
         * @return
         */
        virtual Automaton_ptr SubStrings() const;

        bool isCyclic();
        bool isInCycle(int state);
        bool isStateReachableFrom(int search_state, int from_state);
        BigInteger Count(const unsigned long bound);
        BigInteger CountByMatrixMultiplication(const unsigned long bound);
        virtual BigInteger SymbolicCount(int bound, bool count_less_than_or_equal_to_bound = true);
        virtual BigInteger SymbolicCount(double bound, bool count_less_than_or_equal_to_bound = true);
        SymbolicCounter GetSymbolicCounter();

        Graph_ptr toGraph();

        void toDotAscii(bool print_sink = false, std::ostream& out = std::cout);
        // TODO merge toDot methods into one with options
        void ToDot(std::ostream& out = std::cout, bool print_sink = false);
        void toBDD(std::ostream& out = std::cout);
        void exportDfa(std::string file_name);
        Libs::MONALib::DFA_ptr importDFA(std::string file_name);
        int inspectAuto(bool print_sink = false, bool force_mona_format = false);
        int inspectBDD();

        friend std::ostream& operator<<(std::ostream& os, const Automaton& automaton);

       protected:

        bool isAcceptingSingleWord();
        // TODO update it to work for non-accepting inputs
        std::vector<bool>* getAnAcceptingWord(std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
        std::vector<char> decodeException(std::vector<char>& exception);
        virtual void add_print_label(std::ostream& out);

        /**
         * Returns binary representation of number n with a bit string with the given bit length
         * @param n
         * @param bit_length
         * @return
         */
        static std::string GetBinaryStringMSB(unsigned long n, int bit_length);

        // TODO remove vector<char> version of binary format and use string version below
        static std::vector<char> GetBinaryFormat(unsigned long n, int bit_length);
        static std::vector<char> GetReversedBinaryFormat(unsigned long n, int bit_length);

        // TODO return string instead of vector<char>
        static std::vector<char> getReservedWord(char last_char, int length, bool extra_bit = false);

        /**
         * Minimizes the automaton
         */
        void Minimize();

        /**
         * Projects away the bdd variable at given index
         * @param index
         */
        void ProjectAway(const int index);

        /**
         * Projects away the bdd variable at given index and re assigns the index nummbers
         * @param index
         */
        void ProjectAwayAndReMap(const int index);

        /**
         * Gets the set of states that are reachable from start state at most in the given amount of steps.
         * @param walk
         * @return
         */
        std::unordered_set<int> GetStatesReachableBy(int walk) const;

        /**
         * Gets the set of states that are reachable from start state by a number of step that is between the given amount of steps.
         * @param min_walk
         * @param max_walk
         * @return
         */
        std::unordered_set<int> GetStatesReachableBy(int min_walk, int max_walk) const;

        /**
         * Gets the set of next states from the given state.
         * @param state
         * @return
         */
        std::unordered_set<int> GetNextStates(const int state) const;

        bool hasIncomingTransition(int state);

        // baki left here, move useful functions to above, and move DFA functions to another class
        int getNextState(int state, std::vector<char>& exception);
        std::vector<NextState> getNextStatesOrdered(int state,
                                                    std::function<bool(unsigned& index)> next_node_heuristic = nullptr);
        bool getAnAcceptingWord(NextState& state, std::map<int, bool>& is_stack_member, std::vector<bool>& path,
                                std::function<bool(unsigned& index)> next_node_heuristic = nullptr);

        virtual void SetSymbolicCounter();
        virtual void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& mm);
        void generateGFScript(int bound, std::ostream& out = std::cout, bool count_less_than_or_equal_to_bound = true);
        void generateMatrixScript(int bound, std::ostream& out = std::cout, bool count_less_than_or_equal_to_bound =
                                      true);

        bool isCyclic(int state, std::map<int, bool>& is_discovered, std::map<int, bool>& is_stack_member);
        bool isStateReachableFrom(int search_state, int from_state, std::map<int, bool>& is_stack_member);

        /*
         * Operations from LIBSTRANGER
         */
        void getTransitionCharsHelper(pCharPair result[], char* transitions, int* indexInResult, int currentBit,
                                      int var);
        void getTransitionChars(char* transitions, int var, pCharPair result[], int* pSize);
        char** mergeCharRanges(pCharPair charRanges[], int* p_size);
        void charToAsciiDigits(unsigned char ci, char s[]);
        void charToAscii(char* asciiVal, unsigned char c);
        void fillOutCharRange(char* range, char firstChar, char lastChar);
        char* bintostr(unsigned long, int k);
        unsigned char strtobin(char* binChar, int var);
        static int find_sink(Libs::MONALib::DFA_ptr dfa);

        /**
         * Next id.
         */
        static unsigned long next_id;

        /**
         * Temporary file name counter.
         */
        static unsigned long name_counter;

        /**
         * A boolean indicating whether or not model counter is already computed and cached.
         */
        bool is_counter_cached_;

        /**
         * Number of bdd variables used in MONA representation.
         */
        int num_of_bdd_variables_;

        /**
         * Automaton id used for debugging purposes.
         */
        unsigned long id_;

        /**
         * Mona dfa pointer.
         */
        Libs::MONALib::DFA_ptr dfa_;

        /**
         * Model counter function.
         */
        SymbolicCounter counter_;
       private:
        char* getAnExample(bool accepting = true);  // MONA version

        /**
         * Log level for the instances of this class.
         */
        static const int VLOG_LEVEL;
    };

    class Automaton::Builder {
       public:

        /**
         * Initializes a new instances of the Builder class.
         */
        Builder();

        /**
         * Destructor.
         */
        virtual ~Builder();

        /**
         * Builds an instance of the automaton class.
         * @return
         */
        virtual Automaton_ptr Build();
       protected:

    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_AUTOMATON_H_ */
