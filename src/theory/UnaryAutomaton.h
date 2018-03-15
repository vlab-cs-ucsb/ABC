/*\\
 * UnaryAutomaton.h
 *
 *  Created on: Nov 5, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_UNARYAUTOMATON_H_
#define THEORY_UNARYAUTOMATON_H_

#include <iostream>
#include <iterator>
#include <map>
#include <string>
#include <queue>
#include <vector>

#include <glog/logging.h>

#include "ArithmeticFormula.h"
#include "Automaton.h"
#include "libs/MONALib.h"
#include "SemilinearSet.h"

namespace Vlab
{
  namespace Theory
  {

    class UnaryAutomaton;
    using UnaryAutomaton_ptr = UnaryAutomaton*;

    class IntAutomaton;
    using IntAutomaton_ptr = IntAutomaton*;

    class IntegerAutomaton;
    using IntegerAutomaton_ptr = IntegerAutomaton*;

    class StringAutomaton;
    using StringAutomaton_ptr = StringAutomaton*;

    class UnaryAutomaton : public Automaton
    {
       public:

        /**
         * Unary automaton builder.
         */
        class Builder;

        /**
         * Constructs a unary automaton given the unary dfa.
         * @param dfa
         * @param number_of_bdd_variables
         */
        UnaryAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_bdd_variables);

        /**
         * Copy constructor.
         * @param
         */
        UnaryAutomaton(const UnaryAutomaton&);

        /**
         * Destructor.
         */
        virtual ~UnaryAutomaton();

        /**
         * Generates a clone copy of the current automaton.
         * @return
         */
        virtual UnaryAutomaton_ptr Clone() const override;

        /**
         * Generates a unary automaton that wraps the dfa instance.
         * @param dfa
         * @param number_of_variables
         * @return
         */
        virtual UnaryAutomaton_ptr MakeAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_variables) const
            override;

        /**
         * Prints the actual type and the details of the automaton.
         * @return
         */
        virtual std::string Str() const override;

        SemilinearSet_ptr GetSemilinearSet();
        IntAutomaton_ptr ConvertToIntAutomaton(int number_of_variables, bool add_minus_one = false);
        IntegerAutomaton_ptr ConvertToIntegerAutomaton(std::string var_name, ArithmeticFormula_ptr formula, bool add_minus_one = false);
        StringAutomaton_ptr ConvertToStringAutomaton();

       protected:
        void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) override;

       private:
        static const int VLOG_LEVEL;
    };
  } /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_UNARYAUTOMATON_H_ */
