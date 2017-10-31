/*
 * BoolAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "BoolAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    const int BoolAutomaton::VLOG_LEVEL = 9;

    BoolAutomaton::BoolAutomaton(DFA_ptr dfa, int number_of_bdd_variables)
        : Automaton(dfa, number_of_bdd_variables)
    {
    }

    BoolAutomaton::BoolAutomaton(const BoolAutomaton& other)
        : Automaton(other)
    {
    }

    BoolAutomaton::~BoolAutomaton()
    {
    }

    BoolAutomaton_ptr BoolAutomaton::Clone() const
    {
      return new BoolAutomaton(*this);
    }

    std::string BoolAutomaton::Str() const
    {
      return "BoolAutomaton";
    }

    BoolAutomaton_ptr BoolAutomaton::MakeAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_variables) const
    {
      return new BoolAutomaton(dfa, number_of_variables);
    }

  } /* namespace Theory */
} /* namespace Vlab */
