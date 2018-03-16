/*
 * IntegerAutomatonBuilder.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#include "AutomatonBuilder.h"
#include "IntegerAutomatonBuilder.h"

namespace Vlab
{
  namespace Theory
  {

    IntegerAutomaton::Builder::Builder()
        : Automaton::Builder(),
          formula_ {nullptr}
    {
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetNumberOfStates(const int number_of_states)
    {
      return Automaton::Builder::SetNumberOfStates(number_of_states);
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetNumberOfBddVariables(const int number_of_bdd_variables)
    {
      return Automaton::Builder::SetNumberOfBddVariables(number_of_bdd_variables);
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetAcceptingState(int state)
    {
      return Automaton::Builder::SetAcceptingState(state);
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetTransition(const int source, const std::string transition,
                                                                        const int target)
    {
      return Automaton::Builder::SetTransition(source, transition, target);
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetDfa(const Libs::MONALib::DFA_ptr dfa)
    {
      return Automaton::Builder::SetDfa(dfa);
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetFormula(ArithmeticFormula_ptr formula)
    {
      this->formula_ = formula->clone();
      this->number_of_bdd_variables_ = formula->get_number_of_variables();
      return *this;
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::AcceptAllIntegers()
    {
      return Automaton::Builder::AcceptAllExceptEmptyInput();
    }

    IntegerAutomaton_ptr IntegerAutomaton::Builder::Build()
    {
      if (dfa_ and formula_)
      {
        IntegerAutomaton_ptr automaton = new IntegerAutomaton(dfa_, formula_);
        dfa_ = nullptr;
        formula_ = nullptr;

        DVLOG(VLOG_LEVEL) << *automaton << " = IntegerAutomaton::Builder::Build()";
        return automaton;
      }

      LOG(FATAL)<< "IntegerAutomaton cannot be constructed. Make sure minimum required fields are set in order.";
      return nullptr;
    }

  } /* namespace Theory */
} /* namespace Vlab */
