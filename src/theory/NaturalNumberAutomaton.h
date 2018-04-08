/*
 * NaturalNumberAutomaton.h
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#ifndef SRC_THEORY_NATURALNUMBERAUTOMATON_H_
#define SRC_THEORY_NATURALNUMBERAUTOMATON_H_

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

    class NaturalNumberAutomaton;
    using NaturalNumberAutomaton_ptr = NaturalNumberAutomaton*;

    class NaturalNumberAutomaton : public Automaton
    {
       public:

        /**
         * Binary encoded natural number automaton builder
         */
        class Builder : public Automaton::Builder
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
             * Sets the given state as sink state.
             * @param state
             * @return
             */
            virtual Builder& SetSinkState(const int state) override;

            /**
             * Sets the given state as accepting state.
             * @param state
             * @return
             */
            virtual Builder& SetAcceptingState(const int state) override;

            /**
             * Sets the number of bdd variables.
             * @param number_of_bdd_variables
             * @return
             */
            virtual Builder& SetNumberOfBddVariables(const int number_of_bdd_variables) override;

            /**
             * Sets a transition from source to given target.
             * @param source
             * @param transition is bdd transition string, e.g.; 1XX means 100,101, 110,111 where there are three BDD variables.
             * @param target
             * @return
             */
            virtual Builder& SetTransition(const int source, const std::string& transition, const int target) override;

            /**
             * Sets transitions from a source state.
             * @param source
             * @param transitions
             * @return
             */
            virtual Builder& SetTransitions(const int source, const std::unordered_map<std::string, int>& transitions) override;

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
             * Sets the track of the given variable to the given integer constant.
             * @param variable_name
             * @param value
             * @return
             */
            Builder& SetValue(const std::string variable_name, const int value);

            /**
             * Sets the track of the given variable to the value(s) defined by the given semilinear set.
             * @param variable_name
             * @param semilinear_set
             * @return
             */
            Builder& SetValue(const std::string variable_name, const SemilinearSet_ptr semilinear_set);

            /**
             * Generates an automaton that accepts all natural numbers.
             * @return
             */
            Builder& AcceptAllNaturalNumbers();

            /**
             * Builds an instance of the IntegerAutomaton class.
             * @return
             */
            virtual IntegerAutomaton_ptr Build() override;

           protected:

            /**
             * Reinitializes members to avoid holder larger memory.
             */
            virtual void ResetBuilder() override;

            /**
             * Builds binary encoded integer DFA.
             */
            virtual void BuildDFA() override;

            /**
             * Builds an equality or disequality DFA.
             */
            void BuildEqualityDFA();

            /**
             * Builds an inequality DFA.
             */
            void BuildInEqualityDFA();

            /**
             * Builds a dfa using the constant values map.
             */
            void BuildConstantsDFA();

            /**
             * Builds a dfa using the semilinear sets map.
             */
            void BuildSemilinearSetsDFA();

            /**
             * Builds a dfa for the given variable with the given semilinear set.
             * @param
             * @param semilinear_set
             * @return
             */
            Libs::MONALib::DFA_ptr BuildSemilinearSetDFA(const std::string variable_name, const SemilinearSet_ptr semilinear_set);

            /**
             * TODO try to improve usage
             * Arithmetic formula
             */
            ArithmeticFormula_ptr formula_;

            /**
             * Constant values set for variables in the formula
             */
            std::unordered_map<std::string, int> values_as_constants_;

            /**
             * TODO try to improve usage
             * Semilinear sets defined for variables in the formula.
             */
            std::unordered_map<std::string, SemilinearSet_ptr> values_as_semilinear_set_;
        };

        /**
         * Constructs a binary encoded natural number automaton given binary encoded dfa.
         * @param
         * @param num_of_variables
         */
        NaturalNumberAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_bdd_variables);

        /**
         * Constructs a binary encoded integer automaton given a binary encoded dfa and an arithmetic formula.
         * @param dfa
         * @param formula
         */
        NaturalNumberAutomaton(const Libs::MONALib::DFA_ptr dfa, const ArithmeticFormula_ptr formula);

        /**
         * Copy constructor.
         * @param
         */
        NaturalNumberAutomaton(const NaturalNumberAutomaton&);

        /**
         * Destructor.
         */
        virtual ~NaturalNumberAutomaton();

        /**
         * Generates a clone copy of the current automaton.
         * @return
         */
        virtual NaturalNumberAutomaton_ptr Clone() const override;

        /**
         * Generates an NaturalNumberAutomatonBuilder.
         * @return
         */
        virtual Builder& DynamicBuilder() const override;

        /**
         * Generates a binary automaton that wraps the given dfa instance.
         * @param dfa
         * @param number_of_variables
         * @return
         */
        virtual IntegerAutomaton_ptr MakeAutomaton(Libs::MONALib::DFA_ptr dfa, const int number_of_variables) const
            override;

        /**
         * Prints the actual type and the details of the automaton.
         * @return
         */
        virtual std::string Str() const override;

        /**
         * Gets the formula.
         * @return
         */
        ArithmeticFormula_ptr GetFormula() const;

        /**
         * Checks if the automaton accepts -1.
         * -1 is used a special value for negative numbers for the unary domain.
         * For example to handle s.indexof = -1.
         * -1 is represented with a bool variable along with the dfa.
         * @return
         */
        bool IsAcceptingNegativeOne() const;

        /**
         * Complements the automaton.
         * Makes sure that initial state never accepts after the complement.
         * @return
         */
        void Complement() override;


        /**
         * Projects onto the variable.
         * TODO make project onto method available for all automaton.
         * @param var_name
         * @return
         */
        IntegerAutomaton_ptr GetBinaryAutomatonFor(std::string var_name);

        /**
         * TODO improve coding here, based on test cases
         * @return
         */
        IntegerAutomaton_ptr TrimLeadingZeros();

        SemilinearSet_ptr GetSemilinearSet();

        UnaryAutomaton_ptr ToUnaryAutomaton();

        std::map<std::string, int> GetAnAcceptingIntForEachVar();

        BigInteger SymbolicCount(double bound, bool count_less_than_or_equal_to_bound = false) override;

       protected:
        static NaturalNumberAutomaton_ptr MakeIntGraterThanOrEqualToZero(std::vector<int> indexes, int number_of_variables);
        static NaturalNumberAutomaton_ptr MakeTrimHelperAuto(int var_index, int number_of_variables);
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

        ArithmeticFormula_ptr formula_;
       private:
        static const int VLOG_LEVEL;
    };

  } /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_NATURALNUMBERAUTOMATON_H_ */
