/*
 * MONALib.cpp
 *
 *  Created on: Oct 5, 2017
 *      Author: baki
 */

#include "MONALib.h"

namespace Vlab
{
  namespace Theory
  {
    namespace Libs
    {
      std::unordered_map<int, int*> MONALib::bdd_variable_indices;

      void MONALib::DFASetup(const int number_of_states, const int number_of_bdd_variables)
      {
        dfaSetup(number_of_states, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));
      }

      void MONALib::DFASetNumberOfExceptionalTransitions(const int number_of_exceptional_transtions)
      {
        dfaAllocExceptions(number_of_exceptional_transtions);
      }

      void MONALib::DFASetExceptionalTransition(const std::string& exceptional_transition, const int to)
      {
        dfaStoreException(to, const_cast<char*>(exceptional_transition.data()));
      }

      void MONALib::DFASetTargetForRemaningTransitions(const int state)
      {
        dfaStoreState(state);
      }

      MONALib::DFA_ptr MONALib::DFABuild(const std::string& statuses)
      {
        return dfaBuild(const_cast<char*>(statuses.data()));
      }

      MONALib::DFA_ptr MONALib::DFABuildAndMinimize(const std::string& statuses)
      {
        auto tmp_dfa = MONALib::DFABuild(statuses);
        auto result_dfa = dfaMinimize(tmp_dfa);
        dfaFree(tmp_dfa);
        return result_dfa;
      }

      int* MONALib::GetBddVariableIndices(const int number_of_bdd_variables)
      {
        auto it = MONALib::bdd_variable_indices.find(number_of_bdd_variables);
        if (it != MONALib::bdd_variable_indices.end())
        {
          return it->second;
        }
        int* indices = MONALib::CreateBddVariableIndices(number_of_bdd_variables);
        MONALib::bdd_variable_indices[number_of_bdd_variables] = indices;
        return indices;
      }

      int* MONALib::CreateBddVariableIndices(const int number_of_bdd_variables)
      {
        int* indices = new int[number_of_bdd_variables];
        for (int i = 0; i < number_of_bdd_variables; ++i)
        {
          indices[i] = i;
        }
        return indices;
      }

      bool MONALib::DFAIsMinimizedEmtpy(const MONALib::DFA_ptr minimized_dfa)
      {
        return (minimized_dfa->ns == 1 && minimized_dfa->f[minimized_dfa->s] == -1) ? true : false;
      }

      // TODO implement general is empty function
      bool MONALib::DFAIsEmpty(const MONALib::DFA_ptr dfa)
      {
        bool result = false;
        for (int s = 0; s < dfa->ns; ++s)
        {
          if (MONALib::DFAIsAcceptingState(dfa, s))
          {
            // check if the accepting state is reachable
            LOG(FATAL)<< "Not implemented";
          }
        }
        return result;
      }

      bool MONALib::DFAIsMinimizedOnlyAcceptingEmptyInput(const MONALib::DFA_ptr minimized_dfa)
      {
        if (not MONALib::DFAIsAcceptingState(minimized_dfa, minimized_dfa->s))
        {
          return false;
        }
        for (int s = 0; s < minimized_dfa->ns; s++)
        {
          if (MONALib::DFAIsAcceptingState(minimized_dfa, s) and s != minimized_dfa->s)
          {
            return false;
          }
          else if (MONALib::DFAIsOneStepAway(minimized_dfa, s, minimized_dfa->s))
          {  // if initial state is reachable in a minimized auto, there is a loop
            return false;
          }
        }
        return true;
      }

      bool MONALib::DFAIsAcceptingState(const MONALib::DFA_ptr dfa, const int state_id)
      {
        return (dfa->f[state_id] == 1);
      }

      bool MONALib::DFAIsInitialState(const MONALib::DFA_ptr dfa, const int state_id)
      {
        return (state_id == dfa->s);
      }

      bool MONALib::DFAIsSinkState(const MONALib::DFA_ptr dfa, const int state_id)
      {
        return (bdd_is_leaf(dfa->bddm, dfa->q[state_id])
            and (bdd_leaf_value(dfa->bddm, dfa->q[state_id]) == (unsigned) state_id) and dfa->f[state_id] == -1);
      }

      bool MONALib::DFAIsOneStepAway(const MONALib::DFA_ptr dfa, const int from_state, const int to_state)
      {
        unsigned p, l, r, index;  // BDD traversal variables
        std::stack<unsigned> nodes;

        p = dfa->q[from_state];
        nodes.push(p);
        while (not nodes.empty())
        {
          p = nodes.top();
          nodes.pop();
          LOAD_lri(&dfa->bddm->node_table[p], l, r, index);
          if (index == BDD_LEAF_INDEX)
          {
            if (l == (unsigned) to_state)
            {
              return true;
            }
          }
          else
          {
            nodes.push(l);
            nodes.push(r);
          }
        }
        return false;
      }

      bool MONALib::DFAIsEqual(const MONALib::DFA_ptr dfa1, const MONALib::DFA_ptr dfa2)
      {
        MONALib::DFA_ptr impl_1 = dfaProduct(dfa1, dfa2, dfaIMPL);
        MONALib::DFA_ptr impl_2 = dfaProduct(dfa2, dfa1, dfaIMPL);
        MONALib::DFA_ptr result_dfa = dfaProduct(impl_1, impl_2, dfaAND);
        dfaFree(impl_1);
        dfaFree(impl_2);
        dfaNegation(result_dfa);
        MONALib::DFA_ptr minimized_dfa = dfaMinimize(result_dfa);
        dfaFree(result_dfa);
        bool result = MONALib::DFAIsMinimizedEmtpy(minimized_dfa);
        dfaFree(minimized_dfa);
        return result;
      }

      int MONALib::DFAGetInitialState(const MONALib::DFA_ptr dfa)
      {
        return dfa->s;
      }

      int MONALib::DFAGetSinkState(const MONALib::DFA_ptr dfa)
      {
        for (int s = 0; s < dfa->ns; ++s)
        {
          if (MONALib::DFAIsSinkState(dfa, s))
          {
            return s;
          }
        }
        return -1;
      }

      MONALib::DFA_ptr MONALib::DFAMakePhi(const int number_of_bdd_variables)
      {
        char statuses[1] { '-' };
        dfaSetup(1, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));
        dfaAllocExceptions(0);
        dfaStoreState(0);
        return dfaBuild(statuses);
      }

      /**
       *
       * @returns a dfa that accepts any input including an accepting initial state
       */
      MONALib::DFA_ptr MONALib::DFAMakeAny(const int number_of_bdd_variables)
      {
        char statuses[1] { '+' };
        dfaSetup(1, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));
        dfaAllocExceptions(0);
        dfaStoreState(0);
        return dfaBuild(statuses);
      }

      /**
       *
       * @returns a dfa that accepts any input except initial state is not accepting
       */
      MONALib::DFA_ptr MONALib::DFAMakeAnyButNotEmpty(const int number_of_bdd_variables)
      {
        char statuses[2] { '-', '+' };
        dfaSetup(2, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));
        dfaAllocExceptions(0);
        dfaStoreState(1);
        dfaAllocExceptions(0);
        dfaStoreState(1);
        return dfaBuild(statuses);
      }

      MONALib::DFA_ptr MONALib::DFAMakeEmpty(const int number_of_bdd_variables)
      {
        char statuses[2] { '+', '-' };
        dfaSetup(2, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));
        dfaAllocExceptions(0);
        dfaStoreState(1);
        dfaAllocExceptions(0);
        dfaStoreState(1);
        return dfaBuild(statuses);
      }

      void MONALib::DFAComplement(MONALib::DFA_ptr dfa)
      {
        dfaNegation(dfa);
      }

      MONALib::DFA_ptr MONALib::DFAUnion(const MONALib::DFA_ptr dfa1, const MONALib::DFA_ptr dfa2)
      {
        MONALib::DFA_ptr union_dfa = dfaProduct(dfa1, dfa2, dfaOR);
        MONALib::DFA_ptr minimized_dfa = dfaMinimize(union_dfa);
        dfaFree(union_dfa);
        return minimized_dfa;
      }

      MONALib::DFA_ptr MONALib::DFAIntersect(const MONALib::DFA_ptr dfa1, const MONALib::DFA_ptr dfa2)
      {
        MONALib::DFA_ptr intersect_dfa = dfaProduct(dfa1, dfa2, dfaAND);
        MONALib::DFA_ptr minimized_dfa = dfaMinimize(intersect_dfa);
        dfaFree(intersect_dfa);
        return minimized_dfa;
      }

      MONALib::DFA_ptr MONALib::DFADifference(const MONALib::DFA_ptr dfa1, MONALib::DFA_ptr dfa2)
      {
        dfaNegation(dfa2);  // efficient
        MONALib::DFA_ptr difference_dfa = MONALib::DFAIntersect(dfa1, dfa2);
        dfaNegation(dfa2);  // restore back
        return difference_dfa;
      }

      MONALib::DFA_ptr MONALib::DFAProjectAway(const MONALib::DFA_ptr dfa, const int index)
      {
        MONALib::DFA_ptr projected_dfa = dfaProject(dfa, (unsigned) index);
        MONALib::DFA_ptr minimized_dfa = dfaMinimize(projected_dfa);
        dfaFree(projected_dfa);
        return minimized_dfa;
      }

      MONALib::DFA_ptr MONALib::DFAProjectAwayAndReMap(const MONALib::DFA_ptr dfa, const int number_of_bdd_variables,
                                                       const int index)
      {
        MONALib::DFA_ptr projected_dfa = dfaProject(dfa, (unsigned) index);
        if (index < (number_of_bdd_variables - 1))
        {
          int* indices_map = new int[number_of_bdd_variables];
          for (int i = 0, j = 0; i < number_of_bdd_variables; ++i)
          {
            if (i != index)
            {
              indices_map[i] = j;
              j++;
            }
          }
          dfaReplaceIndices(projected_dfa, indices_map);
          delete[] indices_map;
        }

        MONALib::DFA_ptr minimized_dfa = dfaMinimize(projected_dfa);
        dfaFree(projected_dfa);
        return minimized_dfa;
      }

      MONALib::DFA_ptr MONALib::DFAProjectTo(const MONALib::DFA_ptr dfa, const int number_of_bdd_variables,
                                             const int index)
      {
        MONALib::DFA_ptr projected_dfa = dfaCopy(dfa);
        for (int i = 0; i < number_of_bdd_variables; ++i)
        {
          if (i != index)
          {
            MONALib::DFA_ptr tmp_dfa = projected_dfa;
            projected_dfa = MONALib::DFAProjectAway(tmp_dfa, i);
            dfaFree(tmp_dfa);
          }
        }

        int* indices_map = MONALib::CreateBddVariableIndices(number_of_bdd_variables);
        indices_map[index] = 0;
        indices_map[0] = index;
        dfaReplaceIndices(projected_dfa, indices_map);
        delete[] indices_map;
        return projected_dfa;
      }

      MONALib::DFA_ptr MONALib::DFAMakeAcceptingAnyWithInRange(const int number_of_bdd_variables, const int start,
                                                               const int end)
      {
        CHECK((start >= 0) && (end >= start));
        // 1 initial state and 1 sink state
        const int number_of_states = end + 2;
        char *statuses = new char[number_of_states];
        dfaSetup(number_of_states, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));

        // 0 to start - 1 not accepting, start to end accepting states
        for (int i = 0; i <= end; ++i)
        {
          dfaAllocExceptions(0);
          dfaStoreState(i + 1);
          if (i >= start)
          {
            statuses[i] = '+';
          }
          else
          {
            statuses[i] = '-';
          }
        }

        //the sink state
        dfaAllocExceptions(0);
        dfaStoreState(number_of_states - 1);  // sink state
        statuses[number_of_states - 1] = '-';

        MONALib::DFA_ptr result_dfa = dfaBuild(statuses);
        delete[] statuses;
        return result_dfa;
      }

      MONALib::DFA_ptr MONALib::DFAMakeAcceptingAnyAfterLength(const int number_of_bdd_variables, const int length)
      {
        CHECK(length >= 0);
        // 1 initial state
        const int number_of_states = length + 1;
        char *statuses = new char[number_of_states];
        dfaSetup(number_of_states, number_of_bdd_variables, MONALib::GetBddVariableIndices(number_of_bdd_variables));

        // 0 to length - 1 not accepting
        for (int i = 0; i < length; ++i)
        {
          dfaAllocExceptions(0);
          dfaStoreState(i + 1);
          statuses[i] = '-';
        }

        // final state
        dfaAllocExceptions(0);
        dfaStoreState(length);
        statuses[length] = '+';

        MONALib::DFA_ptr result_dfa = dfaBuild(statuses);
        delete[] statuses;
        return result_dfa;
      }

      std::unordered_map<std::string, int> MONALib::DFAGetTransitionsFrom(const MONALib::DFA_ptr dfa,
                                                                          const int number_of_bdd_variables,
                                                                          const int from, const std::string& extra_bits)
      {
        const int* bdd_indices = MONALib::GetBddVariableIndices(number_of_bdd_variables);
        const int sink_state = MONALib::DFAGetSinkState(dfa);
        std::unordered_map<std::string, int> transition_map;
        paths pp = make_paths(dfa->bddm, dfa->q[from]);
        while (pp)
        {
          if (sink_state != -1 and pp->to != (unsigned) sink_state)
          {
            std::string current_exception;
            for (int j = 0; j < number_of_bdd_variables; ++j)
            {
              trace_descr tp = nullptr;
              for (tp = pp->trace; tp && (tp->index != (unsigned) bdd_indices[j]); tp = tp->next)
                ;
              if (tp)
              {
                if (tp->value)
                {
                  current_exception.push_back('1');
                }
                else
                {
                  current_exception.push_back('0');
                }
              }
              else
              {
                current_exception.push_back('X');
              }
            }
            current_exception.append(extra_bits);
            current_exception.push_back('\0');
            transition_map[current_exception] = pp->to;
          }
          pp = pp->next;
        }
        return transition_map;

      }

      std::unordered_set<std::string> MONALib::DFAGetTransitionsFromTo(const MONALib::DFA_ptr dfa,
                                                                       const int number_of_bdd_variables,
                                                                       const int from, const int to,
                                                                       const std::string& extra_bits)
      {
        const int* bdd_indices = MONALib::GetBddVariableIndices(number_of_bdd_variables);
        std::unordered_set<std::string> transitions;
        paths pp = make_paths(dfa->bddm, dfa->q[from]);
        while (pp)
        {
          if (pp->to == (unsigned) to)
          {
            std::string current_exception;
            for (int j = 0; j < number_of_bdd_variables; ++j)
            {
              trace_descr tp = nullptr;
              for (tp = pp->trace; tp && (tp->index != (unsigned) bdd_indices[j]); tp = tp->next)
                ;
              if (tp)
              {
                if (tp->value)
                {
                  current_exception.push_back('1');
                }
                else
                {
                  current_exception.push_back('0');
                }
              }
              else
              {
                current_exception.push_back('X');
              }
            }
            current_exception.append(extra_bits);
            current_exception.push_back('\0');
            transitions.insert(current_exception);
          }
          pp = pp->next;
        }
        return transitions;
      }

      std::unordered_set<int> MONALib::DFAGetNextStates(const MONALib::DFA_ptr dfa, const int from)
      {
        unsigned p, l, r, index;  // BDD traversal variables
        std::unordered_set<int> next_states;
        std::stack<unsigned> nodes;

        p = dfa->q[from];
        nodes.push(p);
        while (not nodes.empty())
        {
          p = nodes.top();
          nodes.pop();
          LOAD_lri(&dfa->bddm->node_table[p], l, r, index);
          if (index == BDD_LEAF_INDEX)
          {
            next_states.insert(l);
          }
          else
          {
            nodes.push(l);
            nodes.push(r);
          }
        }
        return next_states;
      }

      int MONALib::DFAGetNextState(const DFA_ptr dfa, const int number_of_bdd_variables, const int from,
                                   const std::string& transition)
      {
        int next_state = -1;
        unsigned p, l, r, index = 0;  // BDD traversal variables

        CHECK_EQ(number_of_bdd_variables, transition.size());

        p = dfa->q[from];

        for (int i = 0; i < number_of_bdd_variables; ++i)
        {
          LOAD_lri(&dfa->bddm->node_table[p], l, r, index);
          if (index == BDD_LEAF_INDEX)
          {
            next_state = l;
            break;
          }
          else
          {
            if (transition[i] == '0')
            {
              p = l;
            }
            else if (transition[i] == '1')
            {
              p = r;
            }
          }
        }

        if (index != BDD_LEAF_INDEX)
        {
          LOAD_lri(&dfa->bddm->node_table[p], l, r, index);
          if (index == BDD_LEAF_INDEX)
          {
            next_state = l;
          }
        }

        return next_state;
      }

      MONALib::DFA_ptr MONALib::DFAConcat(const MONALib::DFA_ptr dfa1, const MONALib::DFA_ptr dfa2,
                                          const int number_of_bdd_variables)
      {
        if (MONALib::DFAIsMinimizedEmtpy(dfa1) or MONALib::DFAIsMinimizedEmtpy(dfa2))
        {
          return MONALib::DFAMakeEmpty(number_of_bdd_variables);
        }
        else if (MONALib::DFAIsMinimizedOnlyAcceptingEmptyInput(dfa1))
        {
          return dfaCopy(dfa2);
        }
        else if (MONALib::DFAIsMinimizedOnlyAcceptingEmptyInput(dfa2))
        {
          return dfaCopy(dfa1);
        }

        // TODO refactor handling empty string case
        bool left_hand_side_accepts_emtpy_input = MONALib::DFAIsAcceptingState(dfa1, dfa1->s);
        bool right_hand_side_accepts_empty_input = MONALib::DFAIsAcceptingState(dfa2, dfa2->s);

        MONALib::DFA_ptr left_dfa = dfa1, right_dfa = dfa2;

        if (left_hand_side_accepts_emtpy_input or right_hand_side_accepts_empty_input)
        {
          auto any_input_other_than_empty = MONALib::DFAMakeAcceptingAnyAfterLength(number_of_bdd_variables, 1);
          if (left_hand_side_accepts_emtpy_input)
          {
            left_dfa = MONALib::DFAIntersect(dfa1, any_input_other_than_empty);
          }

          if (right_hand_side_accepts_empty_input)
          {
            right_dfa = MONALib::DFAIntersect(dfa2, any_input_other_than_empty);
          }
          dfaFree(any_input_other_than_empty);
        }

        int* indices = MONALib::GetBddVariableIndices(number_of_bdd_variables);
        int tmp_num_of_variables, state_id_shift_amount, expected_num_of_states, sink_state_left_auto,
            sink_state_right_auto, to_state = 0, loc, i = 0, j = 0;

        bool is_start_state_reachable = false;
        paths state_paths = nullptr, pp = nullptr;
        trace_descr tp = nullptr;

        std::unordered_map<std::string, int> exceptions_left_auto;
        std::unordered_map<std::string, int> exceptions_right_auto;
        std::unordered_map<std::string, int> exceptions_fix;
        char* statuses = nullptr;
        tmp_num_of_variables = number_of_bdd_variables + 1;  // add one extra bit
        state_id_shift_amount = left_dfa->ns;
        expected_num_of_states = left_dfa->ns + right_dfa->ns;

        is_start_state_reachable = MONALib::TEMPisStartStateReachableFromAnAcceptingState(right_dfa);
        if (not is_start_state_reachable)
        {
          expected_num_of_states = expected_num_of_states - 1;  // if start state is reachable from an accepting state, it will be merge with accepting states of left hand side
        }
        // variable initializations
        sink_state_left_auto = MONALib::DFAGetSinkState(left_dfa);
        sink_state_right_auto = MONALib::DFAGetSinkState(right_dfa);

        bool left_sink = true, right_sink = true;
        int sink = sink_state_left_auto;

        if (sink_state_left_auto < 0 && sink_state_right_auto < 0)
        {
          left_sink = right_sink = false;
          sink = expected_num_of_states;
          expected_num_of_states++;
        }
        else if (sink_state_left_auto < 0)
        {
          left_sink = false;
          sink = sink_state_right_auto + state_id_shift_amount;
          if (not is_start_state_reachable)
          {
            sink--;
          }
        }
        else if (sink_state_right_auto < 0)
        {
          right_sink = false;
        }
        else
        {
          expected_num_of_states--;
        }

        statuses = new char[expected_num_of_states + 1];
        int* concat_indices = MONALib::GetBddVariableIndices(tmp_num_of_variables);

        dfaSetup(expected_num_of_states, tmp_num_of_variables, concat_indices);  //sink states are merged
        state_paths = pp = make_paths(right_dfa->bddm, right_dfa->q[right_dfa->s]);
        while (pp)
        {
          if (!right_sink || pp->to != (unsigned) sink_state_right_auto)
          {
            to_state = pp->to + state_id_shift_amount;
            // if there is a self loop keep it
            if (pp->to == (unsigned) right_dfa->s)
            {
              to_state -= 2;
            }
            else
            {
              if (left_sink && right_sink && pp->to > (unsigned) sink_state_right_auto)
              {
                to_state--;  //to new state, sink state will be eliminated and hence need -1
              }
              if ((not is_start_state_reachable) && pp->to > (unsigned) right_dfa->s)
              {
                to_state--;  // to new state, init state will be eliminated if init is not reachable
              }
            }

            std::string current_exception = "";
            for (j = 0; j < number_of_bdd_variables; j++)
            {
              //the following for loop can be avoided if the indices are in order
              for (tp = pp->trace; tp && (tp->index != (unsigned) indices[j]); tp = tp->next)
                ;
              if (tp)
              {
                if (tp->value)
                {
                  current_exception.push_back('1');
                }
                else
                {
                  current_exception.push_back('0');
                }
              }
              else
              {
                current_exception.push_back('X');
              }
            }

            current_exception.push_back('1');  // new path
            current_exception.push_back('\0');
            exceptions_right_auto[current_exception] = to_state;
          }
          tp = nullptr;
          pp = pp->next;
        }

        kill_paths(state_paths);
        state_paths = pp = nullptr;

        for (i = 0; i < dfa1->ns; i++)
        {
          state_paths = pp = make_paths(dfa1->bddm, dfa1->q[i]);
          while (pp)
          {
            if (left_sink && pp->to == (unsigned) sink_state_left_auto)
            {
              pp = pp->next;
              continue;
            }
            to_state = pp->to;
            std::string current_exception = "";
            for (j = 0; j < number_of_bdd_variables; j++)
            {
              for (tp = pp->trace; tp && (tp->index != (unsigned) indices[j]); tp = tp->next)
                ;
              if (tp)
              {
                if (tp->value)
                {
                  current_exception.push_back('1');
                }
                else
                {
                  current_exception.push_back('0');
                }
              }
              else
              {
                current_exception.push_back('X');
              }
            }

            current_exception.push_back('0');  // add extra bit, '0' is used for the exceptions coming from left auto
            current_exception.push_back('\0');
            exceptions_left_auto[current_exception] = to_state;
            tp = nullptr;
            pp = pp->next;
          }
          // generate concat Automaton
          if (MONALib::DFAIsAcceptingState(dfa1, i))
          {
            dfaAllocExceptions(exceptions_left_auto.size() + exceptions_right_auto.size());
            for (auto entry : exceptions_left_auto)
            {
              dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
            }

            for (auto entry : exceptions_right_auto)
            {
              dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
            }

            dfaStoreState(sink);
            if (MONALib::DFAIsAcceptingState(dfa2, 0))
            {
              statuses[i] = '+';
            }
            else
            {
              statuses[i] = '-';
            }
          }
          else
          {
            dfaAllocExceptions(exceptions_left_auto.size());
            for (auto entry : exceptions_left_auto)
            {
              dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
            }
            dfaStoreState(sink);
            statuses[i] = '-';
          }
          kill_paths(state_paths);
          state_paths = pp = nullptr;
        }

        //  initflag is 1 iff init is reached by some state. In this case,
        for (i = 0; i < dfa2->ns; i++)
        {
          if (i != sink_state_right_auto)
          {
            if (i != dfa2->s || is_start_state_reachable)
            {
              state_paths = pp = make_paths(dfa2->bddm, dfa2->q[i]);
              while (pp)
              {
                if (!right_sink || pp->to != (unsigned) sink_state_right_auto)
                {
                  to_state = pp->to + state_id_shift_amount;

                  if (right_sink && left_sink && pp->to > (unsigned) sink_state_right_auto)
                  {
                    to_state--;  //to new state, sink state will be eliminated and hence need -1
                  }

                  if ((not is_start_state_reachable) && pp->to > (unsigned) dfa2->s)
                  {
                    to_state--;  // to new state, init state will be eliminated if init is not reachable
                  }

                  std::string current_exception = "";
                  for (j = 0; j < number_of_bdd_variables; j++)
                  {
                    for (tp = pp->trace; tp && (tp->index != (unsigned) indices[j]); tp = tp->next)
                      ;
                    if (tp)
                    {
                      if (tp->value)
                      {
                        current_exception.push_back('1');
                      }
                      else
                      {
                        current_exception.push_back('0');
                      }
                    }
                    else
                    {
                      current_exception.push_back('X');
                    }
                  }
                  current_exception.push_back('0');  // old value
                  current_exception.push_back('\0');
                  exceptions_fix[current_exception] = to_state;
                  tp = nullptr;
                }
                pp = pp->next;
              }

              dfaAllocExceptions(exceptions_fix.size());
              for (auto entry : exceptions_fix)
              {
                dfaStoreException(entry.second, const_cast<char*>(entry.first.data()));
              }

              dfaStoreState(sink);

              loc = state_id_shift_amount + i;
              if ((not is_start_state_reachable) && i > dfa2->s)
              {
                loc--;
              }
              if (left_sink && right_sink && i > sink_state_right_auto)
              {
                loc--;
              }

              if (MONALib::DFAIsAcceptingState(dfa2, i))
              {
                statuses[loc] = '+';
              }
              else
              {
                statuses[loc] = '-';
              }

              kill_paths(state_paths);
              state_paths = pp = nullptr;
            }
          }
          else if (!left_sink && right_sink)
          {
            dfaAllocExceptions(0);
            dfaStoreState(sink);
            statuses[sink] = '-';
          }
        }

        if (!right_sink && !left_sink)
        {
          dfaAllocExceptions(0);
          dfaStoreState(sink);
          statuses[sink] = '-';
        }

        statuses[expected_num_of_states] = '\0';

        MONALib::DFA_ptr concat_dfa = dfaBuild(statuses);
        delete[] statuses;
        statuses = nullptr;
        delete[] concat_indices;
        concat_indices = nullptr;
        MONALib::DFA_ptr tmp_dfa = dfaProject(concat_dfa, (unsigned) number_of_bdd_variables);
        dfaFree(concat_dfa);
        concat_dfa = dfaMinimize(tmp_dfa);
        dfaFree(tmp_dfa);
        tmp_dfa = nullptr;

        if (left_hand_side_accepts_emtpy_input)
        {
          tmp_dfa = concat_dfa;
          concat_dfa = MONALib::DFAUnion(tmp_dfa, dfa2);
          delete tmp_dfa;
          delete left_dfa;
          left_dfa = nullptr;
        }

        if (right_hand_side_accepts_empty_input)
        {
          tmp_dfa = concat_dfa;
          concat_dfa = MONALib::DFAUnion(tmp_dfa, dfa1);
          delete tmp_dfa;
          delete right_dfa;
          right_dfa = nullptr;
        }

        return concat_dfa;
      }

      /**
       * TODO will remove this function with a better approach in its uses
       * @returns true if a start state is reachable from an accepting state, false otherwise
       */
      bool MONALib::TEMPisStartStateReachableFromAnAcceptingState(MONALib::DFA_ptr dfa)
      {
        paths state_paths, pp;
        for (int i = 0; i < dfa->ns; i++)
        {
          if (MONALib::DFAIsAcceptingState(dfa, i))
          {
            state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
            while (pp)
            {
              if (pp->to == (unsigned) dfa->s)
              {
                kill_paths(state_paths);
                return true;
              }
              pp = pp->next;
            }
            kill_paths(state_paths);
          }
        }
        return false;
      }

    } /* namespace Libs */
  } /* namespace Theory */
} /* namespace Vlab */
