/*
 * AutomatonBuilder.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#include "AutomatonBuilder.h"

namespace Vlab
{
  namespace Theory
  {

    Automaton::Builder::Builder()
        : number_of_states_ { 0 },
          number_of_bdd_variables_ { 0 },
          dfa_ { nullptr }
    {

    }

    Automaton::Builder::~Builder()
    {
      // do not free the dfa as it is used in the automaton constructed.
    }

    Automaton::Builder& Automaton::Builder::SetNumberOfStates(const int number_of_states)
    {
      this->number_of_states_ = number_of_states;
      transitions_.resize(number_of_states);
      statuses_.resize(number_of_states, '-');
      return *this;
    }

    Automaton::Builder& Automaton::Builder::SetNumberOfBddVariables(const int number_of_bdd_variables)
    {
      this->number_of_bdd_variables_ = number_of_bdd_variables;
      return *this;
    }

    Automaton::Builder& Automaton::Builder::SetAcceptingState(const int state)
    {
      this->statuses_[state] = '+';
      return *this;
    }

    Automaton::Builder& Automaton::Builder::SetTransition(const int source, const std::string transition,
                                                          const int target)
    {
      CHECK_EQ(number_of_bdd_variables_, transition.length());
      this->transitions_[source][transition] = target;
      return *this;
    }

    Automaton::Builder& Automaton::Builder::SetDfa(const Libs::MONALib::DFA_ptr dfa)
    {
      this->dfa_ = dfa;
      return *this;
    }

    Automaton_ptr Automaton::Builder::Build()
    {

      if (dfa_)
      {
        Automaton_ptr automaton = new Automaton(dfa_, number_of_bdd_variables_);
        dfa_ = nullptr;

        return automaton;
      }

      LOG(FATAL)<< "DFA is not constructed.";
      return nullptr;
    }

  } /* namespace Theory */
} /* namespace Vlab */
