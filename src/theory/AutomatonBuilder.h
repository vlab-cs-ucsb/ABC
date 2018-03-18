/*
 * AutomatonBuilder.h
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#ifndef SRC_THEORY_AUTOMATONBUILDER_H_
#define SRC_THEORY_AUTOMATONBUILDER_H_

#include "Automaton.h"

namespace Vlab
{
  namespace Theory
  {
    class Automaton::Builder
    {
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
         * Sets the number of states.
         * @param number_of_states
         * @return
         */
        virtual Builder& SetNumberOfStates(const int number_of_states);

        /**
         * Sets the number of bdd variables.
         * @param number_of_bdd_variables
         * @return
         */
        virtual Builder& SetNumberOfBddVariables(const int number_of_bdd_variables);

        /**
         * Sets the given state as accepting state.
         * @param state
         * @return
         */
        virtual Builder& SetAcceptingState(const int state);

        /**
         * Sets a transition from source to given target.
         * @param source
         * @param transition is bdd transition string, e.g.; 1XX means 100,101, 110,111 where there are three BDD variables.
         * @param target
         * @return
         */
        virtual Builder& SetTransition(const int source, const std::string transition, const int target);

        /**
         * Sets the dfa.
         * @param dfa
         * @return
         */
        virtual Builder& SetDfa(const Libs::MONALib::DFA_ptr dfa);

        /**
         * Setups a non accepting automaton.
         * @return
         */
        virtual Builder& RejectAll();

        /**
         * Setups an automaton that accepts all inputs.
         * @return
         */
        virtual Builder& AcceptAll();

        /**
         * Setups an automaton that accepts any input except empty input.
         * @return
         */
        virtual Builder& AcceptAllExceptEmptyInput();

        /**
         * Builds an instance of the automaton class.
         * @return
         */
        virtual Automaton_ptr Build();
       protected:

        /**
         * Builds underlying DFA.
         */
        virtual void BuildDFA();

        /**
         * Number of states.
         */
        int number_of_states_;

        /**
         * Number of bdd variables.
         */
        int number_of_bdd_variables_;

        /**
         * Mona dfa pointer.
         */
        Libs::MONALib::DFA_ptr dfa_;

        /**
         * Accepting or non accepting mark for each state as '0' or '1'.
         */
        std::string statuses_;

        /**
         * State to state transition map.
         */
        std::vector<std::unordered_map<std::string, int>> transitions_;
    };
  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_AUTOMATONBUILDER_H_ */
