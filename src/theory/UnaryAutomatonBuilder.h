/*
 * UnaryAutomatonBuilder.h
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#ifndef SRC_THEORY_UNARYAUTOMATONBUILDER_H_
#define SRC_THEORY_UNARYAUTOMATONBUILDER_H_

#include "UnaryAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    class UnaryAutomaton::Builder : public Automaton::Builder
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
        virtual Builder& SetNumberOfStates(const int number_of_states) override;

        /**
         * Sets the number of bdd variables.
         * @param number_of_bdd_variables
         * @return
         */
        virtual Builder& SetNumberOfBddVariables(const int number_of_bdd_variables) override;

        /**
         * Sets the given state as accepting state.
         * @param state
         * @return
         */
        virtual Builder& SetAcceptingState(const int state) override;

        /**
         * Sets a transition from source to given target.
         * @param source
         * @param transition is bdd transition string, e.g.; 1XX means 100,101, 110,111 where there are three BDD variables.
         * @param target
         * @return
         */
        virtual Builder& SetTransition(const int source, const std::string transition, const int target) override;

        /**
         * Sets the dfa.
         * @param dfa
         * @return
         */
        virtual Builder& SetDfa(const Libs::MONALib::DFA_ptr dfa) override;

        /**
         * Sets the unary symbol char.
         * @param c
         * @return
         */
        Builder& SetUnaryChar(const char c);

        /**
         * Sets semilinear set.
         * @param semilinear_set
         * @return
         */
        Builder& SetSemilinearSet(const SemilinearSet_ptr semilinear_set);

        /**
         * Builds an instance of the UnaryAutomaton class.
         * @return
         */
        virtual UnaryAutomaton_ptr Build() override;
       protected:

        /**
         * Unary symbol.
         */
        char unary_char_;

        /**
         * Semilinear set.
         */
        SemilinearSet_ptr semilinear_set_;
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_UNARYAUTOMATONBUILDER_H_ */
