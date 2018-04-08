/*
 * NaturalNumberAutomatonBuilder.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */


#include "NaturalNumberAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    NaturalNumberAutomaton::Builder::Builder()
        : Automaton::Builder(),
          formula_ {nullptr}
    {
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetNumberOfStates(const int number_of_states)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetNumberOfStates(number_of_states));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetSinkState(const int state)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetSinkState(state));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetAcceptingState(const int state)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetAcceptingState(state));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetNumberOfBddVariables(const int number_of_bdd_variables)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetNumberOfBddVariables(
                                                                                                 number_of_bdd_variables));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetTransition(const int source, const std::string& transition,
                                                                        const int target)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetTransition(source, transition, target));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetTransitions(
        const int source, const std::unordered_map<std::string, int>& transitions)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetTransitions(source, transitions));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetDfa(const Libs::MONALib::DFA_ptr dfa)
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::SetDfa(dfa));
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetFormula(ArithmeticFormula_ptr formula)
    {
      this->formula_ = formula;
      this->number_of_bdd_variables_ = formula->get_number_of_variables();
      return *this;
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetValue(const std::string variable_name, const int value)
    {
      this->values_as_constants_[variable_name] = value;
      return *this;
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::SetValue(const std::string variable_name,
                                                                   const SemilinearSet_ptr semilinear_set)
    {
      this->values_as_semilinear_set_[variable_name] = semilinear_set;
      return *this;
    }

    NaturalNumberAutomaton::Builder& NaturalNumberAutomaton::Builder::AcceptAllNaturalNumbers()
    {
      return static_cast<NaturalNumberAutomaton::Builder&>(Automaton::Builder::AcceptAllExceptEmptyInput());
    }

    NaturalNumberAutomaton_ptr NaturalNumberAutomaton::Builder::Build()
    {
      if (formula_ == nullptr)
      {
        LOG(FATAL)<< "Please set a formula to construct NaturalNumberAutomaton. ";
        return nullptr;
      }

      if (dfa_ == nullptr)
      {
        this->BuildDFA();
      }

      if (dfa_ and formula_)
      {
        NaturalNumberAutomaton_ptr automaton = new NaturalNumberAutomaton(dfa_, formula_);
        this->ResetBuilder();
        DVLOG(VLOG_LEVEL) << *automaton << " = NaturalNumberAutomaton::Builder::Build()";
        return automaton;
      }

      LOG(FATAL)<< "NaturalNumberAutomaton cannot be constructed. Make sure minimum required fields are set in order.";
      return nullptr;
    }

    void NaturalNumberAutomaton::Builder::ResetBuilder()
    {
      this->Automaton::Builder::ResetBuilder();
      this->formula_ = nullptr;
      this->values_as_constants_ = std::unordered_map<std::string, int>();
      this->values_as_semilinear_set_ = std::unordered_map<std::string, SemilinearSet_ptr>();
    }

    void NaturalNumberAutomaton::Builder::BuildDFA()
    {
      // TODO add an option to to call and return base builder
//      this->Automaton::Builder::BuildDFA();
      LOG(FATAL)<< "implement logic based on semilinear set or constants";

      switch (formula_->get_type())
      {
        case ArithmeticFormula::Type::EQ:
        case ArithmeticFormula::Type::NOTEQ:
        {
          this->BuildEqualityDFA();
          break;
        }
        case ArithmeticFormula::Type::GT:
        case ArithmeticFormula::Type::GE:
        case ArithmeticFormula::Type::LE:
        {
          auto tmp_formula = formula_;
          this->formula_ = formula_->ToLessThanEquivalentFormula();
          this->BuildInEqualityDFA();
          delete formula_;
          this->formula_ = tmp_formula;
          break;
        }
        case ArithmeticFormula::Type::LT:
        {
          this->BuildInEqualityDFA();
          break;
        }
        case ArithmeticFormula::Type::VAR:
        {
          this->AcceptAllNaturalNumbers();
          break;
        }
        default:
        LOG(FATAL)<< "Equation type is not specified, please set type for input formula: " << *formula_;
        break;
      }
    }

    void NaturalNumberAutomaton::Builder::BuildEqualityDFA()
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
      const int number_of_states = max - min + 3;
      const int sink_state = number_of_states - 2;
      const int shifted_initial_state = number_of_states - 1;

      unsigned max_states_allowed = 0x80000000;
      unsigned mona_check = 8 * number_of_states;
      CHECK_LE(mona_check, max_states_allowed);  // MONA bug/limit, infinite loops
      CHECK_LT(active_number_of_variables, 64);  // avoid overflow below

      const unsigned long number_of_transitions = 1 << active_number_of_variables;

      // populated and used if initial state is in cycle and accepting.
      std::unordered_map<std::string, int> transitions_from_initial_state;

      std::unordered_map<int, StateIndices> carry_map;  // maps carries to state indices
      carry_map[constant].s = 1;
      carry_map[constant].i = 0;

      const bool is_equality = (ArithmeticFormula::Type::EQ == formula_->get_type());
      const bool needs_shift_state = ((is_equality and constant == 0) or ((not is_equality) and constant != 0));
      bool is_initial_state_shifted = false;

      int next_index = 0;
      int next_label = constant;
      int current_state = 0;

      Libs::MONALib::DFASetup(number_of_states, total_number_of_variables);
      while (next_label < max + 1)
      {
        //there is a state to expand (excuding sink)
        carry_map[next_label].s = 2;

        // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
        Libs::MONALib::DFASetNumberOfExceptionalTransitions(number_of_transitions / 2);

        int result;
        int target;

        for (unsigned long j = 0; j < number_of_transitions; ++j)
        {
          result = next_label + formula_->CountOnes(j);
          if (not (result & 1))
          {
            target = result / 2;
            if (carry_map[target].s == 0)
            {
              carry_map[target].s = 1;
              ++next_index;
              carry_map[target].i = next_index;
            }

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

            // hack to avoid an accepting initial state
            int to_state = carry_map[target].i;
            if (needs_shift_state)
            {  // initial state is accepting, shift it
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
            (next_label <= max) and (carry_map[next_label].i != current_state); ++next_label)
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

      if (carry_map[0].s == 2)
      {
        if (carry_map[0].i == 0 and is_initial_state_shifted)
        {
          statuses[shifted_initial_state] = target_status;
        }
        else
        {
          statuses[carry_map[0].i] = target_status;
        }
      }

      CHECK_EQ('-', statuses[0]);
      this->dfa_ = Libs::MONALib::DFABuildAndMinimize(statuses);
    }

    void NaturalNumberAutomaton::Builder::BuildInEqualityDFA()
    {
      formula_->Simplify();

      auto coefficient_info = formula_->GetCoefficientInfo();
      const int constant = coefficient_info.constant_;
      const int min = coefficient_info.minimum_sum_of_coefficients_;
      const int max = coefficient_info.maximum_sum_of_coefficients_;
      const std::vector<int>& coefficients = coefficient_info.coefficients_;
      const int total_number_of_variables = coefficients.size();
      const int active_number_of_variables = total_number_of_variables - coefficient_info.number_of_zero_coefficients_;
      const int number_of_states = max - min + 2;

      unsigned max_states_allowed = 0x80000000;
      unsigned mona_check = 8 * number_of_states;
      CHECK_LE(mona_check, max_states_allowed);  // MONA bug/limit, infinite loops
      CHECK_LT(active_number_of_variables, 64);  // avoid overflow below

      const unsigned long number_of_transitions = 1 << active_number_of_variables;

      std::unordered_map<int, StateIndices> carry_map;  // maps carries to state indices
      carry_map[constant].s = 1;
      carry_map[constant].i = 0;

      int next_index = 0;
      int next_label = constant;
      int current_state = 0;

      Libs::MONALib::DFASetup(number_of_states, total_number_of_variables);
      while (next_label < max + 1)
      {
        //there is a state to expand (excuding sink)
        carry_map[next_label].s = 2;

        // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
        Libs::MONALib::DFASetNumberOfExceptionalTransitions(number_of_transitions);

        int result;
        int target;

        for (unsigned long j = 0; j < number_of_transitions; ++j)
        {
          result = next_label + formula->CountOnes(j);
          if (result >= 0)
          {
            target = result / 2;
          }
          else
          {
            target = (result - 1) / 2;
          }

          if (carry_map[target].s == 0)
          {
            carry_map[target].s = 1;
            ++next_index;
            carry_map[target].i = next_index;
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

          // hack to avoid an accepting initial state
          int to_state = carry_map[target].i;

          if (to_state == 0)
          {
            to_state = shifted_initial_state;
            is_initial_state_in_cycle = true;
          }

          if (current_state == 0 and is_initial_state_in_cycle)
          {  // save transition for shifted initial start
            transitions_from_initial_state[current_exception] = to_state;
          }

          Libs::MONALib::DFASetExceptionalTransition(current_exception, to_state);
        }

        Libs::MONALib::DFASetTargetForRemaningTransitions(current_state);
        ++current_state;

        //find next state to expand
        for (next_label = min;
            (next_label <= max) and (carry_map[next_label].i != current_state); ++next_label)
        {
        }
      }
      // baki left here
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

    void NaturalNumberAutomaton::Builder::BuildConstantsDFA()
    {
      LOG(FATAL)<< "implement me";
    }

    void NaturalNumberAutomaton::Builder::BuildSemilinearSetsDFA()
    {
      LOG(FATAL)<< "implement me";
    }

    Libs::MONALib::DFA_ptr NaturalNumberAutomaton::Builder::BuildSemilinearSetDFA(const std::string variable_name,
                                                                            const SemilinearSet_ptr semilinear_set)
    {
      const int var_index = formula_->get_variable_index(variable_name);
      const int number_of_variables = number_of_bdd_variables_ + 1;
      const int lz_index = number_of_variables - 1;

      std::string bit_transition(number_of_variables + 1, 'X');
      bit_transition[number_of_variables] = '\0';

      std::vector<BinaryState_ptr> binary_states;
      // TODO refactor that call, especially for the constants
      NaturalNumberAutomaton::ComputeBinaryStates(binary_states, semilinear_set);

      const int number_of_binary_states = binary_states.size();
      const int number_of_states = number_of_binary_states + 2;
      const int leading_zero_state = number_of_states - 2;
      const int sink_state = number_of_states - 1;

      std::string statuses(number_of_states, '-');
      Libs::MONALib::DFASetup(number_of_states, number_of_variables);

      for (int i = 0; i < number_of_binary_states; i++)
      {
        if (NaturalNumberAutomaton::is_accepting_binary_state(binary_states[i], semilinear_set))
        {
          if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() >= 0)
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(3);
            bit_transition[var_index] = '0';
            bit_transition[lz_index] = '0';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd0());
            bit_transition[var_index] = '1';
            bit_transition[lz_index] = 'X';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd1());
            bit_transition[var_index] = '0';
            bit_transition[lz_index] = '1';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, leading_zero_state);
          }
          else if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() < 0)
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(2);
            bit_transition[var_index] = '0';
            bit_transition[lz_index] = '0';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd0());
            bit_transition[var_index] = '0';
            bit_transition[lz_index] = '1';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, leading_zero_state);
          }
          else if (binary_states[i]->getd0() < 0 && binary_states[i]->getd1() >= 0)
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(2);
            bit_transition[var_index] = '1';
            bit_transition[lz_index] = 'X';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd1());
            bit_transition[var_index] = '0';
            bit_transition[lz_index] = '1';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, leading_zero_state);
          }
          else
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
            bit_transition[var_index] = '0';
            bit_transition[lz_index] = '1';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, leading_zero_state);
          }
          bit_transition[lz_index] = 'X';
        }
        else
        {
          if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() >= 0)
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(2);
            bit_transition[var_index] = '0';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd0());
            bit_transition[var_index] = '1';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd1());
          }
          else if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() < 0)
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
            bit_transition[var_index] = '0';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd0());
          }
          else if (binary_states[i]->getd0() < 0 && binary_states[i]->getd1() >= 0)
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
            bit_transition[var_index] = '1';
            Libs::MONALib::DFASetExceptionalTransition(bit_transition, binary_states[i]->getd1());
          }
          else
          {
            Libs::MONALib::DFASetNumberOfExceptionalTransitions(0);
          }
        }

        Libs::MONALib::DFASetTargetForRemaningTransitions(sink_state);
      }

      // for the leading zero state
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
      bit_transition[var_index] = '0';
      bit_transition[lz_index] = '1';
      Libs::MONALib::DFASetExceptionalTransition(bit_transition, leading_zero_state);
      Libs::MONALib::DFASetTargetForRemaningTransitions(sink_state);
      statuses[leading_zero_state] = '+';

      // for the sink state
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
      Libs::MONALib::DFASetTargetForRemaningTransitions(sink_state);

      // TODO temporary removal, fix this control
//      int zero_state = binary_states[0]->getd0();  // adding leading zeros makes accepting zero 00, fix here
//      if (zero_state > -1 and is_accepting_binary_state(binary_states[zero_state], semilinear_set))
//      {
//        //    statuses[zero_state] = '+';
//      }

      for (auto bin_state : binary_states)
      {
        delete bin_state;
      }
      binary_states.clear();

      Libs::MONALib::DFA_ptr binary_dfa = Libs::MONALib::DFABuildAndMinimize(statuses);
      auto tmp_dfa = binary_dfa;
      binary_dfa = Libs::MONALib::DFAProjectAway(binary_dfa, lz_index);
      dfaFree(tmp_dfa);
      return binary_dfa;
    }
  } /* namespace Theory */
} /* namespace Vlab */
