/*
 * NaturalNumberAutomatonBuilder.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#include "AutomatonBuilder.h"
#include "NaturalNumberAutomatonBuilder.h"

namespace Vlab
{
  namespace Theory
  {

    NaturalNumberAutomaton::Builder::Builder()
        : Automaton::Builder()
    {
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetNumberOfStates(const int number_of_states)
    {
      return Automaton::Builder::SetNumberOfStates(number_of_states);
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetNumberOfBddVariables(const int number_of_bdd_variables)
    {
      return Automaton::Builder::SetNumberOfBddVariables(number_of_bdd_variables);
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetAcceptingState(int state)
    {
      return Automaton::Builder::SetAcceptingState(state);
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetTransition(const int source, const std::string transition,
                                                                        const int target)
    {
      return Automaton::Builder::SetTransition(source, transition, target);
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetDfa(const Libs::MONALib::DFA_ptr dfa)
    {
      return Automaton::Builder::SetDfa(dfa);
    }

    UnaryAutomaton_ptr UnaryAutomaton::Builder::Build()
    {
      if (dfa_)
      {
        NaturalNumberAutomaton_ptr automaton = new NaturalNumberAutomaton(dfa_, number_of_bdd_variables_);
        dfa_ = nullptr;

        DVLOG(VLOG_LEVEL) << *automaton << " = NaturalNumberAutomaton::Builder::Build()";
        return automaton;
      }

      LOG(FATAL)<< "Automaton cannot be constructed. Make sure minimum required fields are set in order.";
      return nullptr;
    }

  } /* namespace Theory */
} /* namespace Vlab */
