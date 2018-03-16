/*
 * IntegerAutomatonBuilder.h
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#ifndef SRC_THEORY_INTEGERAUTOMATONBUILDER_H_
#define SRC_THEORY_INTEGERAUTOMATONBUILDER_H_

#include "IntegerAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    class IntegerAutomaton::Builder : public Automaton::Builder
    {
       public:

        /**
         * Initializes a new instance of the Builder class.
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
        virtual Builder& SetAcceptingState(int state) override;

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
         * TODO tmp solution for binary int automaton formula
         * @param formula
         * @return
         */
        Builder& SetFormula(ArithmeticFormula_ptr formula);

        /**
         * Generates an automaton that accepts all integers.
         * @return
         */
        Builder& AcceptAllIntegers();

        /**
         * Builds an instance of the IntegerAutomaton class.
         * @return
         */
        virtual IntegerAutomaton_ptr Build() override;

       protected:

        /**
         * TODO tmp
         * Arithmetic formula
         */
        ArithmeticFormula_ptr formula_
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_INTEGERAUTOMATONBUILDER_H_ */
