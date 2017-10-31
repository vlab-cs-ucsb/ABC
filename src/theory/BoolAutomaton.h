/*
 * BoolAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_BOOLAUTOMATON_H_
#define THEORY_BOOLAUTOMATON_H_

#include <array>

#include "Automaton.h"

namespace Vlab
{
  namespace Theory
  {

    class BoolAutomaton;
    typedef BoolAutomaton* BoolAutomaton_ptr;
    typedef DFA* DFA_ptr;

    class BoolAutomaton : public Automaton
    {
       public:
        BoolAutomaton(DFA_ptr dfa);
        BoolAutomaton(DFA_ptr dfa, int number_of_bdd_variables);
        BoolAutomaton(const BoolAutomaton&);
        virtual ~BoolAutomaton();

        virtual BoolAutomaton_ptr Clone() const override;

        /**
         * Prints the actual type and the details of the automaton.
         * @return
         */
        virtual std::string Str() const override;

        /**
         * Generates a bool automaton that wraps the dfa.
         * @param dfa
         * @param number_of_variables
         * @return
         */
        virtual BoolAutomaton_ptr MakeAutomaton(const DFA_ptr dfa, const int number_of_variables) const override;

       protected:
       private:
        static const int VLOG_LEVEL;
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BOOLAUTOMATON_H_ */
