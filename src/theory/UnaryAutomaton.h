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
    typedef UnaryAutomaton* UnaryAutomaton_ptr;

    class IntAutomaton;
    using IntAutomaton_ptr = IntAutomaton*;

    class BinaryIntAutomaton;
    using BinaryIntAutomaton_ptr = BinaryIntAutomaton*;

    class StringAutomaton;
    using StringAutomaton_ptr = StringAutomaton*;

    class UnaryAutomaton : public Automaton
    {
       public:

        /**
         * Use this class to build an automaton.
         */
        class Builder;

        /**
         * Constructs a unary automaton given the unary dfa.
         * @param dfa
         */
        UnaryAutomaton(Libs::MONALib::DFA_ptr dfa);

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
        virtual UnaryAutomaton_ptr Clone() const;

        /**
         * Generates a unary automaton that wraps dfa instance.
         * @param dfa
         * @param number_of_variables
         * @return
         */
        virtual UnaryAutomaton_ptr MakeAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_variables) const
            override;

        // TODO move to builder class
        static UnaryAutomaton_ptr MakePhi();
        static UnaryAutomaton_ptr MakeAutomaton(SemilinearSet_ptr semilinear_set);

        SemilinearSet_ptr getSemilinearSet();
        IntAutomaton_ptr toIntAutomaton(int number_of_variables, bool add_minus_one = false);
        BinaryIntAutomaton_ptr toBinaryIntAutomaton(std::string var_name, ArithmeticFormula_ptr formula,
                                                    bool add_minus_one = false);
        StringAutomaton_ptr toStringAutomaton();

       protected:
        void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) override;

       private:
        static const int VLOG_LEVEL;
    };

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
         * Builds an instance of the automaton class.
         * @return
         */
        virtual UnaryAutomaton_ptr Build() override;
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_UNARYAUTOMATON_H_ */
