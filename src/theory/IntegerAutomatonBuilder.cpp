/*
 * IntegerAutomatonBuilder.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#include "IntegerAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    IntegerAutomaton::Builder::Builder()
        : Automaton::Builder(),
          formula_ { nullptr }
    {
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetNumberOfStates(const int number_of_states)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetNumberOfStates(number_of_states));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetSinkState(const int state)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetSinkState(state));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetAcceptingState(const int state)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetAcceptingState(state));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetNumberOfBddVariables(const int number_of_bdd_variables)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetNumberOfBddVariables(number_of_bdd_variables));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetTransition(const int source, const std::string& transition,
                                                                        const int target)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetTransition(source, transition, target));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetTransitions(const int source, const std::unordered_map<std::string, int>& transitions)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetTransitions(source, transitions));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetDfa(const Libs::MONALib::DFA_ptr dfa)
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::SetDfa(dfa));
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetFormula(ArithmeticFormula_ptr formula)
    {
      this->formula_ = formula;
      this->number_of_bdd_variables_ = formula->get_number_of_variables();
      return *this;
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetValue(const std::string variable_name, const int value)
    {
      this->values_as_constants_[variable_name] = value;
      return *this;
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::SetValue(const std::string variable_name, const SemilinearSet_ptr semilinear_set)
    {
      this->values_as_semilinear_set_[variable_name] = semilinear_set;
      return *this;
    }

    IntegerAutomaton::Builder& IntegerAutomaton::Builder::AcceptAllIntegers()
    {
      return static_cast<IntegerAutomaton::Builder&>(Automaton::Builder::AcceptAllExceptEmptyInput());
    }

    IntegerAutomaton_ptr IntegerAutomaton::Builder::Build()
    {
      if (formula_ == nullptr)
      {
        LOG(FATAL)<< "Please set a formula to construct IntegerAutomaton. ";
        return nullptr;
      }

      if (dfa_ == nullptr)
      {
        this->BuildDFA();
      }

      if (dfa_ and formula_)
      {
        IntegerAutomaton_ptr automaton = new IntegerAutomaton(dfa_, formula_);
        this->ResetBuilder();
        DVLOG(VLOG_LEVEL) << *automaton << " = IntegerAutomaton::Builder::Build()";
        return automaton;
      }

      LOG(FATAL)<< "IntegerAutomaton cannot be constructed. Make sure minimum required fields are set in order.";
      return nullptr;
    }

    void IntegerAutomaton::Builder::ResetBuilder()
    {
      this->Automaton::Builder::ResetBuilder();
      this->formula_ = nullptr;
      this->values_as_constants_ = std::unordered_map<std::string, int>();
      this->values_as_semilinear_set_ = std::unordered_map<std::string, SemilinearSet_ptr>();
    }

    void IntegerAutomaton::Builder::BuildDFA()
    {
      // TODO add an option to to call and return base bulder
//      this->Automaton::Builder::BuildDFA();
      switch (formula_->get_type())
      {
        case ArithmeticFormula::Type::EQ:
        case ArithmeticFormula::Type::NOTEQ: {
          this->BuildEqualityDFA();
          break;
        }
        case ArithmeticFormula::Type::GT:
        case ArithmeticFormula::Type::GE:
        case ArithmeticFormula::Type::LE: {
          auto tmp_formula = formula_;
          this->formula_ = formula_->ToLessThanEquivalentFormula();
          this->BuildInEqualityDFA();
          delete formula_;
          this->formula_ = tmp_formula;
          break;
        }
        case ArithmeticFormula::Type::LT: {
          this->BuildInEqualityDFA();
          break;
        }
        case ArithmeticFormula::Type::VAR: {
          this->AcceptAllIntegers();
          break;
        }
        default:
          LOG(FATAL)<< "Equation type is not specified, please set type for input formula: " << *formula_;
          break;
        }
      }

    void IntegerAutomaton::Builder::BuildEqualityDFA()
    {
      if (not formula_->Simplify())
      {
        this->Automaton::Builder::RejectAll();
        return;
      }

      auto coefficient_info = formula_->GetCoefficientInfo();
      const int constant = coefficient_info.constant_;
      const int min = coefficient_info.minimum_sum_of_coefficients_;
      const int max = coefficient_info.maximum_sum_of_coefficients_;
      const std::vector<int>& coefficients = coefficient_info.coefficients_;
      const int total_number_of_variables = coefficients.size();
      const int active_number_of_variables = total_number_of_variables - coefficient_info.number_of_zero_coefficients_;
      const int number_of_states = 2 * (max - min + 2);
      const int sink_state = number_of_states - 2;
      const int shifted_initial_state = number_of_states - 1;

      unsigned max_states_allowed = 0x80000000;
      unsigned mona_check = 8 * number_of_states;
      CHECK_LE(mona_check, max_states_allowed); // MONA bug/limit, infinite loops
      CHECK_LT(active_number_of_variables, 64); // avoid overflow below

      const unsigned long number_of_transitions = 1 << active_number_of_variables;

      // populated and used if initial state is in cycle and accepting.
      std::map<std::string, int> transitions_from_initial_state;

      std::map<int, StateIndices> carry_map;  // maps carries to state indices
      carry_map[constant].sr = 1;
      carry_map[constant].i = -1;
      carry_map[constant].ir = 0;

      const bool is_equality = (ArithmeticFormula::Type::EQ == formula_->get_type());
      const bool needs_shift_state = (not is_equality);
      bool is_initial_state_shifted = false;

      int next_index = 0;
      int next_label = constant;
      int current_state = 0;

      Libs::MONALib::DFASetup(number_of_states, total_number_of_variables);
      while (next_label < max + 1)
      {
        //there is a state to expand (excuding sink)
        if (carry_map[next_label].i == current_state)
        {
          carry_map[next_label].s = 2;
        }
        else
        {
          carry_map[next_label].sr = 2;
        }

        // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
        Libs::MONALib::DFASetNumberOfExceptionalTransitions(number_of_transitions / 2);

        int result;
        int target;

        for (unsigned long j = 0; j < number_of_transitions; ++j)
        {
          result = next_label + formula_->CountOnes(j);
          if (not (result & 1))
          {
            std::string binary_string = Automaton::GetBinaryStringLSB(j, active_number_of_variables);
            std::string current_exception(total_number_of_variables, 'X');
            current_exception.push_back('\0');
            for (int i = 0, k = 0; i < total_number_of_variables; ++i)
            {
              if (coefficients[i] != 0)
              {
                current_exception[i] = binary_string[k];
                ++k;
              }
            }

            target = result / 2;
            int to_state;
            if (target == next_label)
            {
              if (carry_map[target].s == 0)
              {
                carry_map[target].s = 1;
                ++next_index;
                carry_map[target].i = next_index;
              }

              to_state = carry_map[target].i;
            }
            else
            {
              if (carry_map[target].sr == 0)
              {
                carry_map[target].sr = 1;
                ++next_index;
                carry_map[target].ir = next_index;
              }

              to_state = carry_map[target].ir;
            }

            if (needs_shift_state)
            {
              if (to_state == 0)
              {
                to_state = shifted_initial_state;
                is_initial_state_shifted = true;
              }
              if (current_state == 0)
              {  // save transition for shifted initial start
                transitions_from_initial_state[current_exception] = to_state;
              }
            }

            Libs::MONALib::DFASetExceptionalTransition(current_exception, to_state);
          }
        }

        Libs::MONALib::DFASetTargetForRemaningTransitions(sink_state);

        ++current_state;

        //find next state to expand
        for (next_label = min;
            (next_label <= max) and (carry_map[next_label].i != current_state)
                and (carry_map[next_label].ir != current_state); ++next_label)
        {
        }
      }

      for (; current_state < number_of_states; ++current_state)
      {
        if (is_initial_state_shifted and current_state == shifted_initial_state)
        {
          Libs::MONALib::DFASetNumberOfExceptionalTransitions(transitions_from_initial_state.size());
          for (auto& el : transitions_from_initial_state)
          {
            Libs::MONALib::DFASetExceptionalTransition(el.first, el.second);
          }
        }
        else
        {
          Libs::MONALib::DFASetNumberOfExceptionalTransitions(0);
        }

        Libs::MONALib::DFASetTargetForRemaningTransitions(sink_state);
      }

      //define accepting and rejecting states
      const char initial_status = is_equality ? '-' : '+';
      const char target_status = is_equality ? '+' : '-';

      //define accepting and rejecting states
      std::string statuses(number_of_states, initial_status);
      // initial state in a binary encoded integer automaton should reject all the time.
      statuses[0] = '-';

      for (next_label = min; next_label <= max; ++next_label)
      {
        if (carry_map[next_label].s == 2)
        {
          if (carry_map[next_label].i == 0 and is_initial_state_shifted)
          {
            statuses[shifted_initial_state] = target_status;
          }
          else
          {
            statuses[carry_map[next_label].i] = target_status;
          }
        }
      }

      CHECK_EQ('-', statuses[0]);
      this->dfa_ = Libs::MONALib::DFABuildAndMinimize(statuses);
    }

    void IntegerAutomaton::Builder::BuildInEqualityDFA()
    {
      formula_->Simplify();

      auto coefficient_info = formula_->GetCoefficientInfo();
      const int constant = coefficient_info.constant_;
      const int min = coefficient_info.minimum_sum_of_coefficients_;
      const int max = coefficient_info.maximum_sum_of_coefficients_;
      const std::vector<int>& coefficients = coefficient_info.coefficients_;
      const int total_number_of_variables = coefficients.size();
      const int active_number_of_variables = total_number_of_variables - coefficient_info.number_of_zero_coefficients_;
      const int number_of_states = 2 * (max - min + 2);
      const int sink_state = number_of_states - 2;
      const int shifted_initial_state = number_of_states - 1;

      unsigned max_states_allowed = 0x80000000;
      unsigned mona_check = 8 * number_of_states;
      CHECK_LE(mona_check, max_states_allowed); // MONA bug/limit, infinite loops
      CHECK_LT(active_number_of_variables, 64); // avoid overflow below

      const unsigned long number_of_transitions = 1 << active_number_of_variables;

      std::map<int, StateIndices> carry_map;  // maps carries to state indices
      carry_map[constant].sr = 1;
      carry_map[constant].i = -1;
      carry_map[constant].ir = 0;

      int next_index = 0;
      int next_label = constant;
      int current_state = 0;

      Libs::MONALib::DFASetup(number_of_states, total_number_of_variables);
      while (next_label < max + 1)
      {  //there is a state to expand (excuding sink)
        if (carry_map[next_label].i == current_state)
        {
          carry_map[next_label].s = 2;
        }
        else
        {
          carry_map[next_label].sr = 2;
        }

        // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
        Libs::MONALib::DFASetNumberOfExceptionalTransitions(number_of_transitions);

        int result;
        int target;
        int write1;
        int label1;
        int label2;

        for (unsigned long j = 0; j < number_of_transitions; ++j)
        {
          int ones = formula_->CountOnes(j);

          result = next_label + ones;
          target = (result >= 0) ? (result / 2) : (result - 1) / 2;
          write1 = result & 1;
          label1 = next_label;
          label2 = target;

          while (label1 != label2)
          {
            label1 = label2;
            result = label1 + ones;
            label2 = (result >= 0) ? (result / 2) : ( result - 1) / 2;
            write1 = result & 1;
          }

          std::string binary_string = Automaton::GetBinaryStringLSB(j, active_number_of_variables);
          std::string current_exception(total_number_of_variables, 'X');
          current_exception.push_back('\0');
          for (int i = 0, k = 0; i < total_number_of_variables; i++)
          {
            if (coefficients[i] != 0)
            {
              current_exception[i] = binary_string[k];
              ++k;
            }
          }

          if (write1)
          {
            if (carry_map[target].s == 0)
            {
              carry_map[target].s = 1;
              next_index++;
              carry_map[target].i = next_index;
            }

            Libs::MONALib::DFASetExceptionalTransition(current_exception, carry_map[target].i);
          }
          else
          {
            if (carry_map[target].sr == 0)
            {
              carry_map[target].sr = 1;
              next_index++;
              carry_map[target].ir = next_index;
            }

            Libs::MONALib::DFASetExceptionalTransition(current_exception, carry_map[target].ir);
          }
        }

        Libs::MONALib::DFASetTargetForRemaningTransitions(current_state);
        ++current_state;

        //find next state to expand
        for (next_label = min;
            (next_label <= max) and (carry_map[next_label].i != current_state)
                and (carry_map[next_label].ir != current_state);
            ++next_label)
        {
        }

      }

      for (; current_state < number_of_states; ++current_state)
      {
        Libs::MONALib::DFASetNumberOfExceptionalTransitions(0);
        Libs::MONALib::DFASetTargetForRemaningTransitions(current_state);
      }

      //define accepting and rejecting states
      std::string statuses(number_of_states, '-');

      for (next_label = min; next_label <= max; ++next_label)
      {
        if (carry_map[next_label].s == 2)
        {
          statuses[carry_map[next_label].i] = '+';
        }
      }

      CHECK_EQ('-', statuses[0]);
      this->dfa_ = Libs::MONALib::DFABuildAndMinimize(statuses);
    }

  } /* namespace Theory */
} /* namespace Vlab */
