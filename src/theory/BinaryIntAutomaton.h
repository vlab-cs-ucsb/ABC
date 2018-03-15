/*
 * IntegerAutomaton.h
 *
 *  Created on: Oct 16, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_BINARYINTAUTOMATON_H_
#define THEORY_BINARYINTAUTOMATON_H_

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <map>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <glog/logging.h>
#include <mona/bdd.h>
#include <mona/dfa.h>

#include "../utils/Cmd.h"
#include "../utils/List.h"
#include "ArithmeticFormula.h"
#include "Automaton.h"
#include "BinaryState.h"
#include "options/Theory.h"
#include "SemilinearSet.h"
#include "UnaryAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    class IntegerAutomaton;
    using IntegerAutomaton_ptr = IntegerAutomaton*;

    class IntegerAutomaton : public Automaton
    {
       public:

        /**
         * Binary encoded integer automaton builder
         */
        class Builder;

        /**
         * Constructs a binary encoded integer automaton given binary encoded dfa.
         * @param
         * @param num_of_variables
         * @param is_natural_number
         */
        IntegerAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_bdd_variables, const bool is_natural_number);

        /**
         * Constructs a binary encoded integer automaton given a binary encoded dfa and an arithmetic formula.
         * @param dfa
         * @param formula
         * @param is_natural_number
         */
        IntegerAutomaton(const Libs::MONALib::DFA_ptr dfa, const ArithmeticFormula_ptr formula, const bool is_natural_number);

        /**
         * Copy constructor.
         * @param
         */
        IntegerAutomaton(const IntegerAutomaton&);

        /**
         * Destructor.
         */
        virtual ~IntegerAutomaton();

        /**
         * Generates a clone copy of the current automaton.
         * @return
         */
        virtual IntegerAutomaton_ptr Clone() const override;

        /**
         * Generates a binary automaton that wraps the given dfa instance.
         * TODO need a parameter to specifiy integer or natural numbers; will separate into two classes.
         * @param dfa
         * @param number_of_variables
         * @return
         */
        virtual IntegerAutomaton_ptr MakeAutomaton(Libs::MONALib::DFA_ptr dfa, const int number_of_variables) const override;

        /**
         * Prints the actual type and the details of the automaton.
         * @return
         */
        virtual std::string Str() const override;

        static IntegerAutomaton_ptr MakePhi(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeAnyInt(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeAutomaton(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeAutomaton(int value, std::string var_name, ArithmeticFormula_ptr formula,
                                                    bool add_leading_zeros = false);
        static IntegerAutomaton_ptr MakeAutomaton(SemilinearSet_ptr semilinear_set, std::string var_name,
                                                    ArithmeticFormula_ptr formula, bool add_leading_zeros = false);

        ArithmeticFormula_ptr get_formula();
        void set_formula(ArithmeticFormula_ptr formula);
        bool is_natural_number();
        bool HasNegative1();
        IntegerAutomaton_ptr Complement();
        IntegerAutomaton_ptr Intersect(IntegerAutomaton_ptr);
        IntegerAutomaton_ptr Union(IntegerAutomaton_ptr);
        IntegerAutomaton_ptr Difference(IntegerAutomaton_ptr);
        IntegerAutomaton_ptr Exists(std::string var_name);
        IntegerAutomaton_ptr GetBinaryAutomatonFor(std::string var_name);
        IntegerAutomaton_ptr GetPositiveValuesFor(std::string var_name);
        IntegerAutomaton_ptr GetNegativeValuesFor(std::string var_name);
        IntegerAutomaton_ptr TrimLeadingZeros();
        IntegerAutomaton_ptr AddLeadingZeros();
        SemilinearSet_ptr GetSemilinearSet();
        UnaryAutomaton_ptr ToUnaryAutomaton();

        std::map<std::string, int> GetAnAcceptingIntForEachVar();

        BigInteger SymbolicCount(double bound, bool count_less_than_or_equal_to_bound = false) override;

       protected:
        IntegerAutomaton(ArithmeticFormula_ptr formula);
        static IntegerAutomaton_ptr MakeIntGraterThanOrEqualToZero(std::vector<int> indexes, int number_of_variables);
        static IntegerAutomaton_ptr MakeEquality(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeIntEquality(ArithmeticFormula_ptr);
        static IntegerAutomaton_ptr MakeNaturalNumberEquality(ArithmeticFormula_ptr);
        static IntegerAutomaton_ptr MakeLessThan(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeIntLessThan(ArithmeticFormula_ptr);
        static IntegerAutomaton_ptr MakeNaturalNumberLessThan(ArithmeticFormula_ptr);
        static IntegerAutomaton_ptr MakeLessThanOrEqual(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeGreaterThan(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeGreaterThanOrEqual(ArithmeticFormula_ptr, bool is_natural_number);
        static IntegerAutomaton_ptr MakeTrimHelperAuto(int var_index, int number_of_variables);
        static void ComputeBinaryStates(std::vector<BinaryState_ptr>& binary_states, SemilinearSet_ptr semilinear_set);
        static void AddBinaryState(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants);
        static int AddBinaryState(std::vector<BinaryState_ptr>& binary_states, int C, int R, BinaryState::Type t, int v,
                                  int b);
        static bool is_accepting_binary_state(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set);

        void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) override;

        bool GetCycleStatus(std::map<int, bool>& cycle_status);
        void GetCycleStatus(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
                            std::map<int, bool>& is_stack_member, std::map<int, bool>& cycle_status, int& time);
//  bool getConstants(std::vector<int>& constants);
//  bool getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
//          std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::vector<int>& constants, int& time);
        void GetConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants);
        void GetConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path,
                          std::vector<int>& constants);
        void GetBaseConstants(std::vector<int>& constants, unsigned max_number_of_bit_limit = 15);
        void GetBaseConstants(int state, unsigned char *is_visited, std::vector<bool>& path,
                              std::vector<int>& constants, unsigned max_number_of_bit_limit);
        //  void getBaseConstants2(std::vector<int>& constants);
        //  void getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants);

        void add_print_label(std::ostream& out) override;
        struct StateIndices
        {
            // r suffixes are for the rejecting clone
            int i, ir;  // state index
            int s, sr;  // status: 0 not yet processed, 1 to be expanded, 2 done
            StateIndices()
                : i { -1 },
                  ir { -1 },
                  s { 0 },
                  sr { 0 }
            {
            }
        };

        bool is_natural_number_;
        ArithmeticFormula_ptr formula_;
       private:
        static const int VLOG_LEVEL;
    };

    class IntegerAutomaton::Builder : public Automaton::Builder
    {
       public:

        /**
         * Initializes a new instance of the Builder class.
         */
        Builder();

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
         * Destructor.
         */
        virtual ~Builder();

        /**
         * Builds an instance of the IntegerAutomaton class.
         * @return
         */
        virtual IntegerAutomaton_ptr Build() override;
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYINTAUTOMATON_H_ */
