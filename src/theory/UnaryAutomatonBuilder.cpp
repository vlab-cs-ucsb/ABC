/*
 * UnaryAutomatonBuilder.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#include "AutomatonBuilder.h"
#include "UnaryAutomatonBuilder.h"

namespace Vlab
{
  namespace Theory
  {

    UnaryAutomaton::Builder::Builder()
        : Automaton::Builder(),
          unary_char_ { '1' },
          semilinear_set_ { nullptr }
    {

    }

    UnaryAutomaton::Builder::~Builder()
    {
      delete semilinear_set_;
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetNumberOfStates(const int number_of_states)
    {
      return Automaton::Builder::SetNumberOfStates(number_of_states);
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetNumberOfBddVariables(const int number_of_bdd_variables)
    {
      return Automaton::Builder::SetNumberOfBddVariables(number_of_bdd_variables);
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetAcceptingState(const int state)
    {
      return Automaton::Builder::SetAcceptingState(state);
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetTransition(const int source, const std::string transition,
                                                                    const int target)
    {
      return Automaton::Builder::SetTransition(source, transition, target);
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetDfa(const Libs::MONALib::DFA_ptr dfa)
    {
      return Automaton::Builder::SetDfa(dfa);
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetUnaryChar(const char c)
    {
      this->unary_char_ = c;
      return *this;
    }

    UnaryAutomaton::Builder& UnaryAutomaton::Builder::SetSemilinearSet(const SemilinearSet_ptr semilinear_set)
    {
      this->semilinear_set_ = semilinear_set;
      return *this;
    }

    UnaryAutomaton_ptr UnaryAutomaton::Builder::Build()
    {
      if (semilinear_set_ and semilinear_set_->is_empty_set())
      {
        DVLOG(VLOG_LEVEL) << *semilinear_set_;
        dfa_ = Libs::MONALib::DFAMakePhi(number_of_bdd_variables_);
      }
      else if (semilinear_set_)
      {
        DVLOG(VLOG_LEVEL) << *semilinear_set_;
        const int cycle_head = semilinear_set_->get_cycle_head();
        const int period = semilinear_set_->get_period();

        number_of_states_ = cycle_head + semilinear_set_->get_period() + 1;
        if (semilinear_set_->has_only_constants())
        {
          number_of_states_ = semilinear_set_->get_constants().back() + 2;
          semilinear_set_->get_periodic_constants().clear();
        }

        int sink_state = number_of_states_ - 1;
        int* indices = Libs::MONALib::GetBddVariableIndices(number_of_bdd_variables_);
        std::string transition(number_of_bdd_variables_, unary_char_);
        std::string statuses(number_of_states_, '-');

        dfaSetup(number_of_states_, number_of_bdd_variables_, indices);
        for (int s = 0; s < number_of_states_ - 2; ++s)
        {
          dfaAllocExceptions(1);
          dfaStoreException(s + 1, const_cast<char*>(transition.data()));
          dfaStoreState(sink_state);
        }

        // Handle last state
        if (semilinear_set_->has_only_constants())
        {
          dfaAllocExceptions(0);
          dfaStoreState(sink_state);
        }
        else
        {
          dfaAllocExceptions(1);
          dfaStoreException(cycle_head, const_cast<char*>(transition.data()));
          dfaStoreState(sink_state);
        }

        dfaAllocExceptions(0);
        dfaStoreState(sink_state);

        for (auto c : semilinear_set_->get_constants())
        {
          CHECK_GE(c, 0);
          statuses[c] = '+';
        }

        for (auto r : semilinear_set_->get_periodic_constants())
        {
          statuses[cycle_head + r] = '+';
        }

        dfa_ = dfaBuild(const_cast<char*>(statuses.data()));
        if (not semilinear_set_->has_only_constants())
        {
          auto tmp_dfa = dfa_;
          dfa_ = dfaMinimize(tmp_dfa);
          dfaFree(tmp_dfa);
        }
      }

      if (dfa_)
      {
        UnaryAutomaton_ptr automaton = new UnaryAutomaton(dfa_, number_of_bdd_variables_);
        dfa_ = nullptr;

        DVLOG(VLOG_LEVEL) << *automaton << " = UnaryAutomaton::Builder::Build()";
        return automaton;
      }

      LOG(FATAL)<< "UnaryAutomaton cannot be constructed. Make sure minimum required fields are set in order.";
      return nullptr;
    }

  } /* namespace Theory */
} /* namespace Vlab */
