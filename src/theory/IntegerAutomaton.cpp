/*
 * IntegerAutomaton.cpp
 *
 *  Created on: Mar 14, 2018
 *      Author: baki
 */

#include "IntegerAutomaton.h"

namespace Vlab
{
  namespace Theory
  {

    const int IntegerAutomaton::VLOG_LEVEL = 9;

    IntegerAutomaton::IntegerAutomaton(const Libs::MONALib::DFA_ptr dfa, const int number_of_bdd_variables) // @suppress("Class members should be properly initialized")
        : Automaton(dfa, number_of_bdd_variables),
          formula_ { nullptr }
    {
    }

    IntegerAutomaton::IntegerAutomaton(const Libs::MONALib::DFA_ptr dfa, const ArithmeticFormula_ptr formula) // @suppress("Class members should be properly initialized")
        : Automaton(dfa, formula->get_number_of_variables()),
          formula_ { formula }
    {
    }

    IntegerAutomaton::IntegerAutomaton(const IntegerAutomaton& other) // @suppress("Class members should be properly initialized")
        : Automaton(other)
    {
      if (other.formula_)
      {
        formula_ = other.formula_->clone();
      }
    }

    IntegerAutomaton::~IntegerAutomaton()
    {
      delete formula_;
    }

    IntegerAutomaton_ptr IntegerAutomaton::Clone() const
    {
      IntegerAutomaton_ptr cloned_auto = new IntegerAutomaton(*this);
      DVLOG(VLOG_LEVEL) << cloned_auto->id_ << " = [" << this->id_ << "]->Clone()";
      return cloned_auto;
    }

    IntegerAutomaton::Builder& IntegerAutomaton::DynamicBuilder() const
    {
      delete dynamic_builder_;
      this->dynamic_builder_ = new IntegerAutomaton::Builder();
      return static_cast<Builder&>(*dynamic_builder_);
    }

    IntegerAutomaton_ptr IntegerAutomaton::MakeAutomaton(const Libs::MONALib::DFA_ptr dfa,
                                                         const int number_of_bdd_variables) const
    {
      CHECK_EQ(number_of_bdd_variables, this->formula_->get_number_of_variables());
      return new IntegerAutomaton(dfa, this->formula_->clone());
    }

    std::string IntegerAutomaton::Str() const
    {
      std::stringstream ss;
      ss << "IntegerAutomaton[" << id_ << "]";
      return ss.str();
    }

    ArithmeticFormula_ptr IntegerAutomaton::GetFormula() const
    {
      return formula_;
    }

    bool IntegerAutomaton::IsAcceptingNegativeOne() const
    {
      CHECK_EQ(1, number_of_bdd_variables_)<< "implemented for single track binary automaton";

      std::string transition =
      { '1'};
      std::unordered_map<int, bool> is_visited;
      int current_state = this->GetInitialState();
      while (not is_visited[current_state])
      {
        is_visited[current_state] = true;
        current_state = this->GetNextState(current_state, transition);
        if (current_state > -1 and IsAcceptingState(current_state))
        {
          return true;
        }
      }

      return false;
    }

    void IntegerAutomaton::Complement()
    {
      this->Automaton::Complement();
      // a complemented auto may have initial state accepting, we should be safely avoided from that
      IntegerAutomaton_ptr accepts_all = Builder().SetFormula(this->GetFormula()->clone())
          .AcceptAll().Build();
      IntegerAutomaton_ptr tmp = this->Intersect(accepts_all);
      delete this->dfa_;
      delete accepts_all;
      this->dfa_ = tmp->dfa_;
      tmp->dfa_ = nullptr;
      delete tmp;
      auto frml = this->GetFormula();
      this->formula_ = frml->negate();
      delete frml;
    }

    IntegerAutomaton_ptr IntegerAutomaton::GetBinaryAutomatonFor(std::string var_name)
    {
      CHECK_EQ(number_of_bdd_variables_, formula_->get_number_of_variables())<< "number of variables is not consistent with formula";
      int bdd_var_index = formula_->get_variable_index(var_name);;
      auto single_var_dfa = Libs::MONALib::DFAProjectTo(this->dfa_, number_of_bdd_variables_, bdd_var_index);
      auto single_var_formula = new ArithmeticFormula();
      single_var_formula->set_type(ArithmeticFormula::Type::INTERSECT);
      single_var_formula->add_variable(var_name, 1);
      IntegerAutomaton_ptr single_var_auto = Builder().SetFormula(single_var_formula).SetDfa(single_var_dfa).Build();
      DVLOG(VLOG_LEVEL) << single_var_auto->id_ << " = [" << this->id_ << "]->GetBinaryAutomatonOf(" << var_name << ")";
      return single_var_auto;
    }

    IntegerAutomaton_ptr IntegerAutomaton::TrimLeadingZeros()
    {
      // TODO
      // carefully understand each step here
      // before trimming make sure automaton only accepts positive numbers
      // try to figure out an easier way to do this, if possible.
      // try to understan if we really need this for unary conversion,
      // we might have an algorithm that works with leading zeros...

      CHECK_EQ(1, number_of_bdd_variables_)<< "trimming is implemented for single track positive binary automaton";

      auto tmp_auto = this->Clone();

      // identify leading zeros
      std::string transition = {'0'};
      int next_state = -1;
      int sink_state = tmp_auto->GetSinkState();
      std::map<int, std::vector<int>> possible_final_states;
      std::stack<int> final_states;
      for (int i = 0; i < tmp_auto->dfa_->ns; i++)
      {
        next_state = GetNextState(i, transition);
        if ((sink_state not_eq next_state) and (i not_eq next_state))
        {
          possible_final_states[next_state].push_back(i);
        }
        if (IsAcceptingState(i))
        {
          final_states.push(i);
        }
      }

      while (not final_states.empty())
      {
        next_state = final_states.top(); final_states.pop();
        for (auto s : possible_final_states[next_state])
        {
          if (not tmp_auto->IsAcceptingState(s))
          {
            tmp_auto->dfa_->f[s] = 1;
            final_states.push(s);
          }
        }
      }

      tmp_auto->Minimize();

      auto trim_helper_auto = IntegerAutomaton::MakeTrimHelperAuto(0,number_of_bdd_variables_);
      trim_helper_auto->formula_ = tmp_auto->formula_->clone();
      auto trimmed_auto = tmp_auto->Intersect(trim_helper_auto);
      delete tmp_auto;
      delete trim_helper_auto;

      DVLOG(VLOG_LEVEL) << trimmed_auto->id_ << " = [" << this->id_ << "]->TrimLeadingZeros()";
      return trimmed_auto;
    }

    /*
     *  TODO options to fix problems, works for automaton that has 1 variable
     *  Search to improve period search part to make it sound
     * TRY to move this code into a common place where both integer automaton
     * and natural number automaton benefits
     */
    SemilinearSet_ptr IntegerAutomaton::GetSemilinearSet()
    {
      SemilinearSet_ptr semilinear_set = nullptr, current_set = nullptr, tmp_set = nullptr;
      IntegerAutomaton_ptr subject_auto = nullptr, tmp_1_auto = nullptr, tmp_2_auto = nullptr, diff_auto = nullptr;
      std::vector<SemilinearSet_ptr> semilinears;
      std::string var_name = this->formula_->get_variable_coefficient_map().begin()->first;
      int current_state = this->dfa_->s, sink_state = this->GetSinkState();
      std::vector<int> constants, bases;
      bool is_cyclic = false;
      std::map<int, bool> cycle_status;

      semilinear_set = new SemilinearSet();

      // 1- First get the constants that are reachable by only taking an edge of a SCC that has one state inside

      is_cyclic = GetCycleStatus(cycle_status);
      GetConstants(cycle_status, constants);
      Util::List::sort_and_remove_duplicate(constants);
      cycle_status.clear();
      semilinear_set->set_constants(constants);

      // CASE automaton has only constants
      if (not is_cyclic)
      {
        DVLOG(VLOG_LEVEL) << *semilinear_set;
        DVLOG(VLOG_LEVEL) << "<semilinear set> = [" << this->id_ << "]->GetSemilinearSet()";
        return semilinear_set;
      }

      /*
       * - Get the maximum constant and make an automaton Ac that accepts 0 <= x <= max
       * - Make new constants equal to the numbers that are accepted by original automaton (A)
       * intersection with Ac
       * Delete these numbers from original automaton
       */
      if (semilinear_set->has_constants())
      {

        int max_constant = constants.back();  // it is already sorted
        constants.clear();
        for (int i = 0; i <= max_constant; i++)
        {
          constants.push_back(i);
        }
        semilinear_set->set_constants(constants);
        constants.clear();
        tmp_1_auto = Builder().SetFormula(formula_->clone()).SetValue(var_name, semilinear_set).Build();
        semilinear_set->clear();

        tmp_2_auto = this->Intersect(tmp_1_auto);
        delete tmp_1_auto;
        tmp_1_auto = nullptr;

        tmp_2_auto->GetBaseConstants(constants);  // if automaton is acyclic, it will return all constants
        Util::List::sort_and_remove_duplicate(constants);
        semilinear_set->set_constants(constants);
        constants.clear();

        subject_auto = this->Difference(tmp_2_auto);
        delete tmp_2_auto;
        tmp_2_auto = nullptr;
      }
      else
      {
        subject_auto = this->Clone();
      }

      semilinears.push_back(semilinear_set);

      unsigned i = 0;
      int cycle_head = 0;
      std::vector<int> tmp_periods;
      int bound = 0;
      while (not subject_auto->IsEmptyLanguage() and (bound++ < 5))
      {
        i = 0;
        cycle_head = 0;
        tmp_periods.clear();
        semilinear_set = new SemilinearSet();
        subject_auto->GetBaseConstants(bases);
        Util::List::sort_and_remove_duplicate(bases);

        // usually we do not need to much numbers once they are sorted, note that this is not sound
        // to make it sound iteratively check for periods instead of deleting them
        if (bases.size() > 10)
        {
          bases.erase(bases.begin() + 10, bases.end());
        }

        if (bases.size() == 1)
        {
          semilinear_set->set_period(bases[0]);
          semilinear_set->add_periodic_constant(0);
          semilinears.push_back(semilinear_set->clone());
          // no need to verify period
        }
        else if (bases.size() > 1)
        {
          int possible_period = 0;

          for (auto it = bases.begin(); it < bases.end() - 1; it++)
          {

            cycle_head = *it;
            bool period_found = false;
            for (auto jt = it + 1; jt < bases.end(); jt++)
            {
              possible_period = *jt - cycle_head;

              bool add_me = true;
              for (auto p : tmp_periods)
              {
                if ((possible_period % p) == 0)
                {
                  add_me = false;
                  break;
                }
              }
              if (add_me)
              {
                current_set = new SemilinearSet();
                current_set->set_cycle_head(cycle_head);
                current_set->set_period(possible_period);
                current_set->add_periodic_constant(0);

                tmp_1_auto = Builder().SetFormula(formula_->clone()).SetValue(var_name, current_set).Build();
                tmp_2_auto = subject_auto->Intersect(tmp_1_auto);
                diff_auto = tmp_1_auto->Difference(tmp_2_auto);
                delete tmp_1_auto;
                tmp_1_auto = nullptr;
                delete tmp_2_auto;
                tmp_2_auto = nullptr;
                if (diff_auto->IsEmptyLanguage())
                {
                  tmp_set = semilinear_set;
                  semilinear_set = tmp_set->Merge(current_set);
                  delete tmp_set;
                  tmp_set = nullptr;
                  semilinears.push_back(current_set);
                  tmp_periods.push_back(possible_period);
                  period_found = true;
                }
                else
                {
                  delete current_set;
                }
                delete diff_auto;
                diff_auto = nullptr;
                current_set = nullptr;
              }
            }

            if (period_found)
            {
              for (auto rt = it + 1; rt < bases.end();)
              {
                possible_period = *rt - cycle_head;
                bool remove_me = false;
                for (auto p : tmp_periods)
                {
                  if ((possible_period % p) == 0)
                  {
                    remove_me = true;
                    break;
                  }
                }
                if (remove_me)
                {
                  rt = bases.erase(rt);
                }
                else
                {
                  rt++;
                }
              }
              period_found = false;
            }
          }
        }
        else
        {
          LOG(FATAL)<< "Automaton must have an accepting state, check base extraction algorithm";
        }
        tmp_1_auto = Builder().SetFormula(formula_->clone()).SetValue(var_name, semilinear_set).Build();
        tmp_2_auto = subject_auto;
        subject_auto = tmp_2_auto->Difference(tmp_1_auto);
        delete tmp_1_auto;
        tmp_1_auto = nullptr;
        delete tmp_2_auto;
        tmp_2_auto = nullptr;
        delete semilinear_set;
        semilinear_set = nullptr;
        bases.clear();
      }

      delete subject_auto;
      subject_auto = nullptr;

      semilinear_set = new SemilinearSet();
      for (auto s : semilinears)
      {
        tmp_set = semilinear_set;
        semilinear_set = tmp_set->Merge(s);
        delete tmp_set;
        delete s;
      }

      DVLOG(VLOG_LEVEL) << *semilinear_set;
      DVLOG(VLOG_LEVEL) << "semilinear set = [" << this->id_ << "]->GetSemilinearSet()";

      return semilinear_set;
    }

    UnaryAutomaton_ptr IntegerAutomaton::ToUnaryAutomaton()
    {
      UnaryAutomaton_ptr unary_auto = nullptr;
      IntegerAutomaton_ptr trimmed_auto = nullptr;
      SemilinearSet_ptr semilinear_set = nullptr;
      trimmed_auto = this->TrimLeadingZeros();

      semilinear_set = trimmed_auto->GetSemilinearSet();
      delete trimmed_auto;
      trimmed_auto = nullptr;

      unary_auto = UnaryAutomaton::Builder().SetSemilinearSet(semilinear_set).Build();
      DVLOG(VLOG_LEVEL) << unary_auto->GetId() << " = [" << this->id_ << "]->ToUnaryAutomaton()";
      return unary_auto;
    }

    std::map<std::string, int> IntegerAutomaton::GetAnAcceptingIntForEachVar()
    {
      std::map<std::string, int> var_values;
      std::map<int, int> values;
      std::vector<bool>* example = getAnAcceptingWord();

      // Reads from most significant bits

      auto rit = example->rbegin();
      // read the sign bit for integers
      for (int var_index = number_of_bdd_variables_ - 1; var_index >= 0; --var_index)
      {
        if (*rit)
        {
          values[var_index] = -1;
        }
        else
        {
          values[var_index] = 0;
        }
        rit++;
      }

      // read value bits
      for (int var_index = number_of_bdd_variables_ - 1; rit != example->rend(); rit++)
      {
        values[var_index] <<= 1;
        values[var_index] |= (*rit);
        var_index--;

        if (var_index == -1)
        {
          var_index = number_of_bdd_variables_ - 1;
        }
      }

      delete example;
      example = nullptr;

      int var_index;
      std::string var_name;
      for (auto& var_entry : formula_->get_variable_coefficient_map())
      {
        var_name = var_entry.first;
        var_index = formula_->get_variable_index(var_name);
        ;
        if (var_name.length() > 10)
        {
          var_name = var_name.substr(0, 10);
        }
        var_values[var_name] = values[var_index];
      }

      return var_values;
    }

    void IntegerAutomaton::decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix)
    {
      counter_.set_type(SymbolicCounter::Type::BINARYINT);
    }

    BigInteger IntegerAutomaton::SymbolicCount(double bound, bool count_less_than_or_equal_to_bound)
    {
      std::stringstream cmd;
      std::string str_result;
      std::string tmp_result_file = Option::Theory::TMP_PATH + "/arith_result.dot";
      std::string math_script_path = Option::Theory::SCRIPT_PATH + "/count.m";

      std::ofstream outfile(tmp_result_file.c_str());
      if (!outfile.good())
      {
        std::cout << "cannot open file: " << tmp_result_file << std::endl;
        exit(2);
      }

      this->ToDot(outfile, false);

      cmd << "math -script " << math_script_path << " " << tmp_result_file << " ";

      ++bound;  // consider sign bit

      if (std::floor(bound) == bound)
      {
        cmd << static_cast<int>(bound);
      }
      else
      {
        cmd << bound;
      }

      try
      {
        DVLOG(VLOG_LEVEL) << "run_cmd(`" << cmd.str() << "`)";
        str_result = Util::Cmd::run_cmd(cmd.str());
      }
      catch (std::string& e)
      {
        LOG(ERROR)<< e;
      }

      return BigInteger(str_result);
    }

    IntegerAutomaton_ptr IntegerAutomaton::MakeIntGraterThanOrEqualToZero(std::vector<int> indexes,
                                                                          int number_of_variables)
    {
      int number_of_states = 3;
      char statuses[3] { '-', '+', '-' };
      std::vector<char> exception;

      for (int i = 0; i < number_of_variables; i++)
      {
        exception.push_back('X');
      }
      exception.push_back('\0');

      Libs::MONALib::DFASetup(number_of_states, number_of_variables);
      dfaAllocExceptions(1);
      for (int i : indexes)
      {
        exception[i] = '0';
      }
      dfaStoreException(1, &*exception.begin());
      dfaStoreState(0);

      dfaAllocExceptions(1);
      for (int i : indexes)
      {
        exception[i] = '1';
      }
      dfaStoreException(0, &*exception.begin());
      dfaStoreState(1);

      dfaAllocExceptions(0);
      dfaStoreState(2);

      auto positive_numbers_dfa = dfaBuild(statuses);
      auto postivie_numbers_auto = new IntegerAutomaton(positive_numbers_dfa, number_of_variables);

      DVLOG(VLOG_LEVEL) << postivie_numbers_auto->id_
                        << " = [IntegerAutomaton]->MakeIntGraterThanOrEqualToZero(<indexes>, " << number_of_variables
                        << ")";
      return postivie_numbers_auto;
    }

    IntegerAutomaton_ptr IntegerAutomaton::MakeTrimHelperAuto(int var_index, int number_of_variables)
    {
      std::string statuses = { '-', '+', '+', '-', '-' };
      std::string exception(number_of_variables + 1, 'X');
      exception[number_of_variables] = '\0';

      const int number_of_states = 5;
      Libs::MONALib::DFASetup(number_of_states, number_of_variables);

      // state 0
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(2);
      exception[var_index] = '0';
      Libs::MONALib::DFASetExceptionalTransition(exception, 1);
      exception[var_index] = '1';
      Libs::MONALib::DFASetExceptionalTransition(exception, 2);
      Libs::MONALib::DFASetTargetForRemaningTransitions(0);
      // state 1
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(2);
      exception[var_index] = '0';
      Libs::MONALib::DFASetExceptionalTransition(exception, 3);
      exception[var_index] = '1';
      Libs::MONALib::DFASetExceptionalTransition(exception, 2);
      Libs::MONALib::DFASetTargetForRemaningTransitions(1);
      // state 2
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
      exception[var_index] = '0';
      Libs::MONALib::DFASetExceptionalTransition(exception, 4);
      Libs::MONALib::DFASetTargetForRemaningTransitions(2);
      // state 3
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
      exception[var_index] = '1';
      Libs::MONALib::DFASetExceptionalTransition(exception, 2);
      Libs::MONALib::DFASetTargetForRemaningTransitions(3);
      // state 4
      Libs::MONALib::DFASetNumberOfExceptionalTransitions(1);
      exception[var_index] = '1';
      Libs::MONALib::DFASetExceptionalTransition(exception, 2);
      Libs::MONALib::DFASetTargetForRemaningTransitions(4);

      auto trim_helper_dfa = Libs::MONALib::DFABuild(statuses);
      auto trim_helper_auto = new IntegerAutomaton(trim_helper_dfa, number_of_variables);

      DVLOG(VLOG_LEVEL) << trim_helper_auto->id_ << " = [IntegerAutomaton]->MakeTrimHelperAuto(" << var_index << ", "
                        << number_of_variables << ")";
      return trim_helper_auto;
    }

    void IntegerAutomaton::ComputeBinaryStates(std::vector<BinaryState_ptr>& binary_states,
                                               SemilinearSet_ptr semilinear_set)
    {
      if (semilinear_set->get_period() == 0)
      {
        AddBinaryState(binary_states, semilinear_set->get_constants());
      }
      else
      {
        AddBinaryState(binary_states, semilinear_set->get_cycle_head(), semilinear_set->get_period(),
                       BinaryState::Type::VAL, -1, -1);
      }
    }

    /**
     * works for positive numbers for now
     */
    void IntegerAutomaton::AddBinaryState(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants)
    {
      std::map<std::pair<int, int>, int> binary_state_map;

      binary_states.push_back(new BinaryState(-1, 0));
      binary_state_map.insert(std::make_pair(std::make_pair(-1, 0), 0));

      for (auto value : constants)
      {
        CHECK_GE(value, 0)<< "works for positive numbers only";
        unsigned i = 0;
        int rank = 1;
        int mask = value;
        int state_value = 0;
        int current_bit = 0;

        do
        {
          current_bit = mask & 1;
          if (current_bit)
          {
            state_value = state_value | (1 << (rank - 1));
          }
          auto key = std::make_pair(state_value, rank);
          auto it = binary_state_map.find(key);

          if (it == binary_state_map.end())
          {
            binary_states.push_back(new BinaryState(state_value, rank));

            int index = binary_states.size() - 1;
            binary_state_map[key] = index;
            if (current_bit)
            {
              binary_states[i]->setd1(index);
            }
            else
            {
              binary_states[i]->setd0(index);
            }
            i = index;
          }
          else
          {
            i = it->second;
          }

          mask >>= 1;
          rank += 1;
        }while (state_value not_eq value);
      }
    }

    int IntegerAutomaton::AddBinaryState(std::vector<BinaryState_ptr>& binary_states, int C, int R, BinaryState::Type t,
                                         int v, int b)
    {
      unsigned i = 0;
      int d0 = -1, d1 = -1;

      for (i = 0; i < binary_states.size(); i++)
      {
        if (binary_states[i]->isEqualTo(t, v, b))
        {
          return i;
        }
      }

      binary_states.push_back(new BinaryState(t, v, b));

      if (b < 0)
      {
        if (C == 0)
        {
          d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, 1 % R, 1 % R);
          d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, 0, 1 % R);
        }
        else if (C == 1)
        {
          d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, 1 % R, 1 % R);
          d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMF, 0, 1 % R);
        }
        else
        {
          d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, 1, 1);
          d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, 0, 1);
        }
      }
      else if (BinaryState::Type::VAL == t && (v + 2 * b >= C))
      {
        d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
        d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMF, v % R, (2 * b) % R);
      }
      else if (BinaryState::Type::VAL == t && (v + 2 * b < C))
      {
        d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, v + 2 * b, 2 * b);
        d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, v, 2 * b);
      }
      else if (BinaryState::Type::REMT == t)
      {
        d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
        d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, v % R, (2 * b) % R);
      }
      else if (BinaryState::Type::REMF == t)
      {
        d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
        d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMF, v % R, (2 * b) % R);
      }

      binary_states[i]->setd0d1(d0, d1);

      return i;
    }

    bool IntegerAutomaton::is_accepting_binary_state(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set)
    {
      if (BinaryState::Type::VAL == binary_state->getType())
      {
        for (auto i : semilinear_set->get_constants())
        {
          if (i == binary_state->getV())
          {
            return true;
          }
        }
      }
      else if (BinaryState::Type::REMT == binary_state->getType())
      {
        for (auto i : semilinear_set->get_periodic_constants())
        {
          if (((i + semilinear_set->get_cycle_head()) % (semilinear_set->get_period())) == binary_state->getV())
          {
            return true;
          }
        }
      }
      return false;
    }

    bool IntegerAutomaton::GetCycleStatus(std::map<int, bool>& cycle_status)
    {
      std::map<int, int> disc;
      std::map<int, int> low;
      std::map<int, bool> is_stack_member;
      std::vector<int> st;
      std::vector<bool> path;
      int time = 0;
      int sink_state = GetSinkState();

      if (sink_state > 0)
      {
        disc[sink_state] = 0;  // avoid exploring sink state
        is_stack_member[sink_state] = false;  // avoid looping to sink state
        cycle_status[sink_state] = true;
      }
      GetCycleStatus(this->dfa_->s, disc, low, st, is_stack_member, cycle_status, time);
      DVLOG(VLOG_LEVEL) << cycle_status[-2] << " = [" << this->id_ << "]->getCycleStatus(<constants>)";
      return cycle_status[-2];  // -2 is to keep if it is cyclic at all or not
    }

    void IntegerAutomaton::GetCycleStatus(int state, std::map<int, int>& disc, std::map<int, int>& low,
                                          std::vector<int>& st, std::map<int, bool>& is_stack_member,
                                          std::map<int, bool>& cycle_status, int& time)
    {
      int next_state = 0;
      std::string exception = { '0' };
      int l, r;
//  std::cout << "visiting: " << state << std::endl;
      disc[state] = low[state] = time;
      time++;
      st.push_back(state);
      is_stack_member[state] = true;

      l = GetNextState(state, exception);
      exception[0] = '1';
      r = GetNextState(state, exception);

      for (int b = 0; b < 2; b++)
      {
        next_state = (b == 0) ? l : r;
        if (disc.find(next_state) == disc.end())
        {
          GetCycleStatus(next_state, disc, low, st, is_stack_member, cycle_status, time);
          low[state] = std::min(low[state], low[next_state]);
        }
        else if (is_stack_member[next_state])
        {
          low[state] = std::min(low[state], disc[next_state]);
        }
      }

      if (low[state] == disc[state])
      {  // head of SCC
        int current_state = st.back();

        while (current_state != state)
        {
          st.pop_back();
          is_stack_member[current_state] = false;
          cycle_status[current_state] = true;
          cycle_status[-2] = true;
          current_state = st.back();
        }

        is_stack_member[current_state] = false;
        st.pop_back();

        if (current_state == l or current_state == r)
        {
          cycle_status[current_state] = true;
          cycle_status[-2] = true;
        }
      }

      return;
    }

    void IntegerAutomaton::GetConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants)
    {
      std::vector<bool> path;

      // current state cannot be accepting in binary automaton
      if ((not IsSinkState(this->dfa_->s)) and (not cycle_status[this->dfa_->s]))
      {
        GetConstants(this->dfa_->s, cycle_status, path, constants);
      }

      DVLOG(VLOG_LEVEL) << "<void> = [" << this->id_ << "]->getConstants(<cycle status>, <constants>)";
      return;
    }

    void IntegerAutomaton::GetConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path,
                                        std::vector<int>& constants)
    {
      int next_state = 0;
      std::string exception = { '0' };
      int l, r;

      if (path.size() > 31)
      {  // limit samples to integer length for now
        return;
      }

      l = GetNextState(state, exception);
      exception[0] = '1';
      r = GetNextState(state, exception);

      for (int b = 0; b < 2; b++)
      {
        next_state = (b == 0) ? l : r;

        if ((not IsSinkState(next_state)))
        {
          path.push_back(b == 1);
          if (IsAcceptingState(next_state))
          {
            unsigned c = 0;
            for (unsigned i = 0; i < path.size(); i++)
            {
              if (path[i])
              {
                c += (1 << i);
              }
            }
            constants.push_back(c);
          }
          if (not cycle_status[next_state])
          {  // if next state is not in a cycle continue exploration
            GetConstants(next_state, cycle_status, path, constants);
          }
          path.pop_back();
        }
      }
    }

    /**
     * TODO that function does not catch all the constants because of automaton structure
     * Sets constant numbers accepted by this automaton
     * (constant numbers are reachable without involving any SCC except the ones with size 1)
     * @return true if automaton is cyclic, false otherwise
     */
//bool IntegerAutomaton::getConstants(std::vector<int>& constants) {
//  std::map<int, int> disc;
//  std::map<int, int> low;
//  std::map<int, bool> is_stack_member;
//  std::vector<int> st;
//  std::vector<bool> path;
//  int time = 0;
//  bool result = false;
//  int sink_state = getSinkState();
//
//  if (sink_state == this->dfa->s) {
//    return false;
//  }
//
//  disc[sink_state] = 0; // avoid exploring sink state
//  is_stack_member[sink_state] = false; // avoid looping to sink state
//
//  result = getConstants(this->dfa->s, disc, low, st, is_stack_member, path, constants, time);
//  DVLOG(VLOG_LEVEL) << result << " = [" << this->id << "]->getConstants(<constants>)";
//  return result;
//}
//
//bool IntegerAutomaton::getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
//        std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::vector<int>& constants, int& time) {
//
//  int next_state = 0;
//  std::vector<char> exception = {'0'};
//  int l, r;
//
////  std::cout << "visiting state: " << state << std::endl;
//  disc[state] = low[state] = time; time++;
//  st.push_back(state);
//  is_stack_member[state] = true;
//
//  l = getNextState(state, exception);
//  exception[0] = '1';
//  r = getNextState(state, exception);
//  bool is_cyclic = true; // TODO figure out that
//
//  for (int b = 0; b < 2; b++) {
//    next_state = (b == 0) ? l : r;
////    std::cout << "next state: " << next_state << std::endl;
//    if (disc.find(next_state) == disc.end()) {
//      path.push_back( b == 1);
//      is_cyclic = getConstants(next_state, disc, low, st, is_stack_member, path, constants, time);
//      low[state] = std::min(low[state], low[next_state]);
//      path.pop_back();
//    } else if (is_stack_member[next_state]) {
//      low[state] = std::min(low[state], disc[next_state]);
//    }
//
//  }
//
//  bool is_in_cycle = false;
//  if (low[state] == disc[state]) { // head of SCC
//    int current_state = st.back();
//    while (current_state != state) {
//      st.pop_back();
//      is_stack_member[current_state] = false;
//      current_state = st.back();
//      is_in_cycle = true;
//    }
//    is_stack_member[current_state] = false;
//    st.pop_back();
//
//    if (current_state == l or current_state == r) {
//      is_in_cycle = true;
//    }
//
//    if ((not is_in_cycle) and isAcceptingState(current_state)) {
//
//      unsigned c = 0;
//      for (unsigned i = 0; i < path.size(); i++) {
//        if (path[i]) {
//          c += (1 << i);
//        }
//      }
//      constants.push_back(c);
//    }
//  }
//
//  return is_in_cycle;
//}
    void IntegerAutomaton::GetBaseConstants(std::vector<int>& constants, unsigned max_number_of_bit_limit)
    {
      unsigned char *is_visited = new unsigned char[this->dfa_->ns];
      std::vector<bool> path;

      for (int i = 0; i < this->dfa_->ns; i++)
      {
        is_visited[i] = false;
      }

      if (not IsSinkState(this->dfa_->s))
      {
        GetBaseConstants(this->dfa_->s, is_visited, path, constants, max_number_of_bit_limit);
      }

      delete[] is_visited;

      DVLOG(VLOG_LEVEL) << "<void> = [" << this->id_ << "]->getBaseConstants(<base constants>)";

      return;
    }

    /**
     * @param is_visited to keep track of visited transition; 1st is for '0' transition, 2nd bit is for '1' transition
     * @returns populated constants, ignores the value of initial state whether is an accepted or not
     */
    void IntegerAutomaton::GetBaseConstants(int state, unsigned char *is_visited, std::vector<bool>& path,
                                            std::vector<int>& constants, unsigned max_number_of_bit_limit)
    {
      int next_state = 0;
      std::string exception = { '0' };

      if (path.size() > max_number_of_bit_limit)
      {  // limit samples to integer length for now
        return;
      }

      if (IsAcceptingState(state))
      {
        unsigned c = 0;
        for (unsigned i = 0; i < path.size(); i++)
        {
          if (path[i])
          {
            c += (1 << i);
          }
        }
        constants.push_back(c);
      }

      next_state = GetNextState(state, exception);  // taking transition 0

      if ((is_visited[state] & 1) == 0 and (not IsSinkState(next_state)))
      {
        is_visited[state] |= 1;
        path.push_back(false);
        GetBaseConstants(next_state, is_visited, path, constants, max_number_of_bit_limit);
        path.pop_back();
        is_visited[state] &= 2;
      }

      exception[0] = '1';
      next_state = GetNextState(state, exception);  // taking transition 1

      if ((is_visited[state] & 2) == 0 and (not IsSinkState(next_state)))
      {
        is_visited[state] |= 2;
        path.push_back(true);
        GetBaseConstants(next_state, is_visited, path, constants, max_number_of_bit_limit);
        path.pop_back();
        is_visited[state] &= 1;
      }
    }

//void IntegerAutomaton::getBaseConstants2(std::vector<int>& constants) {
//  bool *is_stack_member = new bool[this->dfa->ns];
//  std::vector<bool> path;
//
//  for (int i = 0; i < this->dfa->ns; i++) {
//    is_stack_member[i] = false;
//  }
//
//  if (not isSinkState(this->dfa->s)) {
//    getBaseConstants(this->dfa->s, is_stack_member, path, constants);
//  }
//
//  delete[] is_stack_member;
//
//  DVLOG(VLOG_LEVEL) << "<void> = [" << this->id << "]->getBaseConstants(<base constants>)";
//
//  return;
//}
//
///**
// * @returns populated constants, ignores the value of initial state whether is an accepted or not
// */
//void IntegerAutomaton::getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants) {
//  int next_state = 0;
//  std::vector<char> exception = {'0'};
//  int l, r;
//
//  is_stack_member[state] = true;
//
//  if (path.size() > 31) { // limit samples to integer length for now
//    return;
//  }
//
//  l = getNextState(state, exception);
//  exception[0] = '1';
//  r = getNextState(state, exception);
//
//  // this case cannot happen in state other than sink (automaton does not have leading zeros)
//  if (state == l and state == r) {
//    LOG(FATAL)<< "Automaton cannot have leading zeros at this point, please debug the bug";
//  }
//
//  for (int b = 0; b < 2; b++) {
//    next_state = (b == 0) ? l : r;
//    // take simple paths
//    if ( (not is_stack_member[next_state]) and (not isSinkState(next_state)) ) {
//      path.push_back( b == 1);
//
//      if (isAcceptingState(next_state)) {
//        unsigned c = 0;
//        for (unsigned i = 0; i < path.size(); i++) {
//          if (path[i]) {
//            c += (1 << i);
//          }
//        }
//        constants.push_back(c);
//      }
//
//      getBaseConstants(next_state, is_stack_member, path, constants);
//      path.pop_back();
//    }
//  }
//  is_stack_member[state] = false;
//}

    void IntegerAutomaton::add_print_label(std::ostream& out)
    {
      out << " subgraph cluster_0 {\n";
      out << "  style = invis;\n  center = true;\n  margin = 0;\n";
      out << "  node[shape=plaintext];\n";
      out << " \"\"[label=\"";
      for (auto& el : formula_->get_variable_coefficient_map())
      {
        out << el.first << "\n";
      }
      out << "\"]\n";
      out << " }";
    }

  } /* namespace Theory */
} /* namespace Vlab */
