/*
 * MONALib.h
 *
 *  Created on: Oct 5, 2017
 *      Author: baki
 */

#ifndef SRC_THEORY_LIBS_MONALIB_H_
#define SRC_THEORY_LIBS_MONALIB_H_

#include <algorithm>
#include <array>
#include <cmath>
#include <cstdlib>
#include <cstring>
#include <iostream>
#include <iterator>
#include <set>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <glog/logging.h>
#include <mona/bdd.h>
#include <mona/bdd_external.h>
#include <mona/dfa.h>
#include <mona/mem.h>

namespace Vlab
{
  namespace Theory
  {
    namespace Libs
    {
      class MONALib
      {
         public:
          using DFA_ptr = DFA*;

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
           * Generates a dfa where the bdd variable in the given index of the given dfa projected away and the index mapping is done again
           * @param dfa
           * @param number_of_bdd_variables
           * @param index
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
           * Generates a dfa that accepts any input that has length between start and end inclusive
           * @param start
           * @param end
           * @param number_of_bdd_variables
           * @return
           */
          static DFA_ptr DFAMakeAcceptingAnyWithInRange(const int start, const int end, const int number_of_bdd_variables);

          /**
           * Generates a dfa that accepts any input after reading the given number of inputs.
           * @param start
           * @param number_of_bdd_variables
           * @return
           */
          static DFA_ptr DFAMakeAcceptingAnyAfterLength(const int length, const int number_of_bdd_variables);

          /**
           * Gets outgoing transitions and target states from the given state.
           * Excludes the transition that goes into a sink state.
           * @param dfa
           * @param from
           * @param number_of_variables
           * @param extra_bits appends bits to the read transitions
           * @return
           */
          static std::unordered_map<std::string, int> DFAGetTransitionsFrom(const DFA_ptr dfa, const int from, const int number_of_bdd_variables, std::string extra_bits = "");

          /**
           * Gets set of transitions between two states.
           * @param dfa
           * @param from
           * @param to
           * @param number_of_variables
           * @param extra_bits appends bits to the read transitions
           * @return
           */
          static std::unordered_set<std::string> DFAGetTransitionsFromTo(const DFA_ptr dfa, const int from, const int to, const int number_of_variables, std::string extra_bits = "");

          /**
           * Gets the next states from the given state.
           * @param dfa
           * @param from
           * @return
           */
          static std::unordered_set<int> DFAGetNextStates(const DFA_ptr dfa, const int from);

          /**
           * Generates a dfa that accepts the concatenated language of dfa1 and dfa2.
           * @param dfa1
           * @param dfa2
           * @param number_of_bdd_variables
           * @return
           */
          static DFA_ptr DFAConcat(const DFA_ptr dfa1, const DFA_ptr dfa2, const int number_of_bdd_variables);

          // todo will remove temp function
          static bool TEMPisStartStateReachableFromAnAcceptingState(DFA_ptr dfa);

         private:

          /**
           * Bdd variable indices cache used in MONA dfa manipulation
           */
          static std::unordered_map<int, int*> bdd_variable_indices;

      };

    } /* namespace Libs */
  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_LIBS_MONALIB_H_ */
