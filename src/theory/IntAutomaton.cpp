/*
 * IntAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "IntAutomaton.h"

namespace Vlab {
namespace Theory {

const int IntAutomaton::VLOG_LEVEL = 9;

int IntAutomaton::DEFAULT_NUM_OF_VARIABLES = 8;

int* IntAutomaton::DEFAULT_VARIABLE_INDICES = Automaton::getIndices(
        IntAutomaton::DEFAULT_NUM_OF_VARIABLES);

unsigned* IntAutomaton::DEFAULT_UNSIGNED_VARIABLE_INDICES = Automaton::getIndices(
        (unsigned)IntAutomaton::DEFAULT_NUM_OF_VARIABLES);

IntAutomaton::IntAutomaton(DFA_ptr) :
        Automaton(Automaton::Type::INT, dfa, IntAutomaton::DEFAULT_NUM_OF_VARIABLES),
        has_negative_1(false) {

}
IntAutomaton::IntAutomaton(DFA_ptr, int num_of_variables) :
        Automaton(Automaton::Type::INT, dfa, num_of_variables),
        has_negative_1 (false) {
}

IntAutomaton::IntAutomaton(DFA_ptr, bool has_negative_1) :
        Automaton(Automaton::Type::INT, dfa, IntAutomaton::DEFAULT_NUM_OF_VARIABLES),
        has_negative_1 (has_negative_1) {
}

IntAutomaton::IntAutomaton(DFA_ptr, bool has_negative_1, int num_of_variables) :
        Automaton(Automaton::Type::INT, dfa, num_of_variables),
        has_negative_1 (has_negative_1) {

}

IntAutomaton::IntAutomaton(const IntAutomaton& other) :
        Automaton(other), has_negative_1 (other.has_negative_1) {
}

IntAutomaton::~IntAutomaton() {
}

IntAutomaton_ptr IntAutomaton::clone() const {
  IntAutomaton_ptr cloned_auto = new IntAutomaton(*this);
  DVLOG(VLOG_LEVEL) << cloned_auto->id << " = [" << this->id << "]->clone()";
  return cloned_auto;
}

IntAutomaton_ptr IntAutomaton::makePhi(int num_of_variables, int* variable_indices) {
  DFA_ptr non_accepting_int_dfa = nullptr;
  IntAutomaton_ptr non_acception_int_auto = nullptr;
  non_accepting_int_dfa = Automaton::makePhi(num_of_variables, variable_indices);
  non_acception_int_auto = new IntAutomaton(non_accepting_int_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << non_acception_int_auto->id << " = makePhi()";

  return non_acception_int_auto;
}

IntAutomaton_ptr IntAutomaton::makeZero(int num_of_variables, int* variable_indices) {
  DFA_ptr zero_int_dfa = nullptr;
  IntAutomaton_ptr zero_int = nullptr;
  std::array<char, 2> statuses { '+', '-' };

  dfaSetup(2, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  zero_int_dfa = dfaBuild(&*statuses.begin());
  zero_int = new IntAutomaton(zero_int_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << zero_int->id << " = makeZero()";

  return zero_int;
}

/**
 *
 * Returns Sigma* except two reserved words (11111111, 11111110)
 */
IntAutomaton_ptr IntAutomaton::makeAnyInt(int num_of_variables, int* variable_indices) {
  DFA_ptr any_int_dfa = nullptr;
  IntAutomaton_ptr any_int = nullptr;
  std::array<char, 2> statuses { '+', '-' };
  std::vector<char> reserved_1 = Automaton::getReservedWord('1', num_of_variables);
  std::vector<char> reserved_2 = Automaton::getReservedWord('0', num_of_variables);
  char* sharp1 = &*reserved_1.begin();
  char* sharp0 = &*reserved_2.begin();

  dfaSetup(2, num_of_variables, variable_indices);
  dfaAllocExceptions(2);
  dfaStoreException(1, sharp1); // word 11111111
  dfaStoreException(1, sharp0); // word 11111110
  dfaStoreState(0);

  dfaAllocExceptions(0);
  dfaStoreState(1);

  any_int_dfa = dfaBuild(&*statuses.begin());
  any_int = new IntAutomaton(any_int_dfa, true, num_of_variables);

  DVLOG(VLOG_LEVEL) << any_int->id << " = makeAnyInt()";

  return any_int;
}

IntAutomaton_ptr IntAutomaton::makeInt(int value, int num_of_variables, int* variable_indices){
  DFA_ptr int_dfa = nullptr;
  IntAutomaton_ptr int_auto = nullptr;

  if(value < 0){
    int_auto = IntAutomaton::makePhi();
    int_auto->has_negative_1 = true;
  }
  else if (value == 0){
    int_auto = IntAutomaton::makeZero();
  }
  else{
    int_dfa = dfaStringAutomatonL1toL2(value, value,
             IntAutomaton::DEFAULT_NUM_OF_VARIABLES, IntAutomaton::DEFAULT_VARIABLE_INDICES);
         int_auto = new IntAutomaton(int_dfa, IntAutomaton::DEFAULT_NUM_OF_VARIABLES);
  }

  DVLOG(VLOG_LEVEL) << int_auto->id << " = makeInt(" << value <<  ")";

  return int_auto;
}

IntAutomaton_ptr IntAutomaton::makeIntLessThan(int value, int num_of_variables, int* variable_indices){
  DFA_ptr int_dfa = nullptr;
  IntAutomaton_ptr int_auto = nullptr;

   if(value < 0){
     int_auto = IntAutomaton::makePhi();
   }
   else if (value == 0){
     int_auto = IntAutomaton::makePhi();
     int_auto->has_negative_1 = true;
   }
   else{
     int_dfa = dfaStringAutomatonL1toL2(0, value-1,
         IntAutomaton::DEFAULT_NUM_OF_VARIABLES, IntAutomaton::DEFAULT_VARIABLE_INDICES);
     int_auto = new IntAutomaton(int_dfa, IntAutomaton::DEFAULT_NUM_OF_VARIABLES);
   }

   DVLOG(VLOG_LEVEL) << int_auto->id << " = makeIntLessThan(" << value <<  ")";

   return int_auto;
}

IntAutomaton_ptr IntAutomaton::makeIntLessThanEqual(int value, int num_of_variables, int* variable_indices){
  DFA_ptr int_dfa = nullptr;
  IntAutomaton_ptr int_auto = nullptr;

  if(value < 0){
    int_auto = IntAutomaton::makePhi();
    int_auto->has_negative_1 = true;
  }
  else if (value == 0){
    int_auto = IntAutomaton::makeZero();
    int_auto->has_negative_1 = true;
  }
  else{
    int_dfa = dfaStringAutomatonL1toL2(0, value,
             IntAutomaton::DEFAULT_NUM_OF_VARIABLES, IntAutomaton::DEFAULT_VARIABLE_INDICES);
         int_auto = new IntAutomaton(int_dfa, IntAutomaton::DEFAULT_NUM_OF_VARIABLES);
  }

  DVLOG(VLOG_LEVEL) << int_auto->id << " = makeIntLessThanEqual(" << value <<  ")";

  return int_auto;
}

IntAutomaton_ptr IntAutomaton::makeIntGreaterThan(int value, int num_of_variables, int* variable_indices){
  IntAutomaton_ptr int_auto = nullptr;

  if(value < -1){
    int_auto = IntAutomaton::makeAnyInt();
  }
  else{
    int_auto = IntAutomaton::makeIntLessThanEqual(value)->complement();
  }

  DVLOG(VLOG_LEVEL) << int_auto->id << " = makeIntGreaterThan(" << value <<  ")";

  return int_auto;
}

IntAutomaton_ptr IntAutomaton::makeIntGreaterThanEqual(int value, int num_of_variables, int* variable_indices){
  IntAutomaton_ptr int_auto = nullptr;

  if(value < -1){
    int_auto = IntAutomaton::makeAnyInt();
  }
  else{
    int_auto = IntAutomaton::makeIntLessThan(value)->complement();
  }

  DVLOG(VLOG_LEVEL) << int_auto->id << " = makeIntGreaterThanEqual(" << value <<  ")";

  return int_auto;
}

IntAutomaton_ptr IntAutomaton::makeIntRange(int start, int end, int num_of_variables, int* variable_indices){
  IntAutomaton_ptr range_auto = nullptr, lessThan_auto = nullptr, greaterThanEqual_auto = nullptr;

  greaterThanEqual_auto = IntAutomaton::makeIntGreaterThanEqual(start);
  lessThan_auto = IntAutomaton::makeIntLessThan(end);
  range_auto = lessThan_auto->intersect(greaterThanEqual_auto);

  delete greaterThanEqual_auto;
  delete lessThan_auto;

  DVLOG(VLOG_LEVEL) << range_auto->id << " = makeIntRange(" << start << "," << end <<  ")";

  return range_auto;
}

IntAutomaton_ptr IntAutomaton::complement() {
  DFA_ptr complement_dfa = nullptr, minimized_dfa = nullptr, current_dfa = dfaCopy(dfa);
  IntAutomaton_ptr complement_auto = nullptr;
  IntAutomaton_ptr any_int = IntAutomaton::makeAnyInt();

  dfaNegation(current_dfa);
  complement_dfa = dfaProduct(any_int->dfa, current_dfa, dfaAND);
  delete any_int;
  any_int = nullptr;
  dfaFree(current_dfa);
  current_dfa = nullptr;

  minimized_dfa = dfaMinimize(complement_dfa);
  dfaFree(complement_dfa);
  complement_dfa = nullptr;

  complement_auto = new IntAutomaton(minimized_dfa, num_of_variables);
  complement_auto->has_negative_1 = (not this->has_negative_1);

  DVLOG(VLOG_LEVEL) << complement_auto->id << " = [" << this->id << "]->makeComplement()";

  return complement_auto;
}

/**
 * TODO Figure out why empty check is necessary
 */
IntAutomaton_ptr IntAutomaton::union_(IntAutomaton_ptr other_auto) {
  DFA_ptr union_dfa = nullptr, minimized_dfa = nullptr;
  IntAutomaton_ptr union_auto = nullptr;

  union_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaOR);
  minimized_dfa = dfaMinimize(union_dfa);
  dfaFree(union_dfa);
  union_dfa = nullptr;

  union_auto = new IntAutomaton(minimized_dfa, num_of_variables);
  union_auto->has_negative_1 = this->has_negative_1 or other_auto->has_negative_1;

  DVLOG(VLOG_LEVEL) << union_auto->id << " = [" << this->id << "]->union(" << other_auto->id << ")";

  return union_auto;
}

IntAutomaton_ptr IntAutomaton::intersect(IntAutomaton_ptr other_auto) {
  DFA_ptr intersect_dfa = nullptr, minimized_dfa = nullptr;
  IntAutomaton_ptr intersect_auto = nullptr;

  intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaAND);
  minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
  intersect_dfa = nullptr;

  intersect_auto = new IntAutomaton(minimized_dfa, num_of_variables);
  intersect_auto->has_negative_1 = this->has_negative_1 and other_auto->has_negative_1;

  DVLOG(VLOG_LEVEL) << intersect_auto->id << " = [" << this->id << "]->intersect(" << other_auto->id << ")";

  return intersect_auto;
}

IntAutomaton_ptr IntAutomaton::difference(IntAutomaton_ptr other_auto) {
  IntAutomaton_ptr difference_auto = nullptr, complement_auto = nullptr;

  complement_auto = other_auto->complement();
  difference_auto = this->intersect(complement_auto);
  // negative one handled in complement and intersect

  DVLOG(VLOG_LEVEL) << difference_auto->id << " = [" << this->id << "]->difference(" << other_auto->id << ")";

  return difference_auto;
}

IntAutomaton_ptr IntAutomaton::add(IntAutomaton_ptr other_auto) {
  DFA_ptr concat_dfa = nullptr;
  IntAutomaton_ptr concat_auto = nullptr;

//  concat_dfa = dfa_concat(this->dfa, other_auto->dfa, IntAutomaton::DEFAULT_NUM_OF_VARIABLES,
//          IntAutomaton::DEFAULT_VARIABLE_INDICES);
//

  DFA_ptr M1 = this->dfa;
  DFA_ptr M2 = other_auto->dfa;
  int var = IntAutomaton::DEFAULT_NUM_OF_VARIABLES;
  int* indices = IntAutomaton::DEFAULT_VARIABLE_INDICES;

  IntAutomaton_ptr tmp0 = nullptr;
      DFA *tmp1 = nullptr;

//      if (checkOnlyEmptyString(M1, var, indices)) {
//        return new IntAutomaton(dfaCopy(M2));
//      }
//
//      if (checkOnlyEmptyString(M2, var, indices)) {
//        return new IntAutomaton(dfaCopy(M1));
//      }

      if(checkEmptyString(M2)) {
        if(state_reachable(M2, M2->s, var, indices)){
          tmp1 = dfa_shift_empty_M(M2, var, indices);
          IntAutomaton_ptr tmp = new IntAutomaton(tmp1, var);
          tmp0 = this->concat(tmp);
          dfaFree(tmp1);
        }
        else{
          tmp0 =  concat(other_auto);
        }
        tmp1 = dfa_union(tmp0->dfa, M1);
        delete tmp0;
      }else{
        tmp1 = concat(other_auto)->dfa;
      }
  concat_auto = new IntAutomaton(tmp1, num_of_variables);

  DVLOG(VLOG_LEVEL) << concat_auto->id << " = [" << this->id << "]->concatenate(" << other_auto->id << ")";

  return concat_auto;
}

/**
 * Re-implementation of  'dfa_concat_extrabit' in LibStranger
 */
IntAutomaton_ptr IntAutomaton::concat(IntAutomaton_ptr other_auto) {
  DFA_ptr concat_dfa = nullptr, tmp_dfa = nullptr;
  IntAutomaton_ptr concat_auto = nullptr;
  int var = IntAutomaton::DEFAULT_NUM_OF_VARIABLES;
  int* indices = IntAutomaton::DEFAULT_VARIABLE_INDICES;
  int tmp_num_of_variables,
      state_id_shift_amount,
      expected_num_of_states,
      num_of_exceptions_to_add = 0,
      sink_state_left_auto,
      sink_state_right_auto,
      state_key_left_auto = 0,
      state_key_right_auto = 0,
      state_key_fix = 0,
      loc,
      i = 0,
      j = 0;

  long max_exceptions;
  bool is_start_state_reachable;
  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;

  std::map<int, std::vector<char>*> exceptions_left_auto;
  std::map<int, std::vector<char>*> exceptions_right_auto;
  std::map<int, std::vector<char>*> exceptions_fix;
  std::map<int, int> state_map_right_auto;
  std::map<int, int> state_map_left_auto;
  std::map<int, int> state_map_fix;
  char* statuses = nullptr;

  // variable initializations
  sink_state_left_auto = this->getSinkState();
  sink_state_right_auto = other_auto->getSinkState();

  CHECK_GT(sink_state_left_auto, -1);
  CHECK_GT(sink_state_right_auto, -1);

  tmp_num_of_variables = this->num_of_variables + 1; // add one extra bit
  state_id_shift_amount = this->dfa->ns;

  max_exceptions = 1 << tmp_num_of_variables;
  if (tmp_num_of_variables > 10) {
    max_exceptions = 1 << 10; // saving for multi-track automaton
  }

  expected_num_of_states = this->dfa->ns + other_auto->dfa->ns - 1; // -1 is for to remove one of the sink states
  is_start_state_reachable = other_auto->isStartStateReachable();
  if (not is_start_state_reachable) {
    expected_num_of_states = expected_num_of_states  - 1; // if start state is reachable from an accepting state, it will be merge with accepting states of left hand side
  }

  statuses = new char[expected_num_of_states];

//  std::cout << "sink 1: " << sink_state_left_auto << std::endl;
//  std::cout << "sink 2: " << sink_state_right_auto << std::endl;
//  std::cout << "left ns: " << this->dfa->ns << std::endl;
//  std::cout << "right ns: " << other_auto->dfa->ns << std::endl;
//  std::cout << "right initflag: " << is_start_state_reachable << std::endl;
//  std::cout << "new ns: " << expected_num_of_states << std::endl;
//  std::cout << "max exeps: " << max_exceptions << std::endl << std::endl;
//
//  std::cout << "shift: " << state_id_shift_amount << std::endl;
//  std::cout << "right start state: " << other_auto->dfa->s << std::endl;

  dfaSetup(expected_num_of_states, tmp_num_of_variables, getIndices(tmp_num_of_variables)); //sink states are merged
  state_paths = pp = make_paths(other_auto->dfa->bddm, other_auto->dfa->q[other_auto->dfa->s]);
  while (pp) {
    if ( pp->to != (unsigned)sink_state_right_auto ) {
      state_map_right_auto[state_key_right_auto] = pp->to + state_id_shift_amount;
      // if there is a self loop keep it
      if ( pp->to == (unsigned)other_auto->dfa->s ) {
        state_map_right_auto[state_key_right_auto] -= 2;
      } else {
        if ( sink_state_right_auto >= 0 && pp->to > (unsigned)sink_state_right_auto ) {
          state_map_right_auto[state_key_right_auto]--; //to new state, sink state will be eliminated and hence need -1
        }
        if ((not is_start_state_reachable) && pp->to > (unsigned)other_auto->dfa->s) {
          state_map_right_auto[state_key_right_auto]--; // to new state, init state will be eliminated if init is not reachable
        }
      }

      exceptions_right_auto[state_key_right_auto] = new std::vector<char>();
      for (j = 0; j < other_auto->num_of_variables; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            exceptions_right_auto[state_key_right_auto]->push_back('1');
          }
          else {
            exceptions_right_auto[state_key_right_auto]->push_back('0');
          }
        }
        else {
          exceptions_right_auto[state_key_right_auto]->push_back('X');
        }
      }

      exceptions_right_auto[state_key_right_auto]->push_back('1'); // new path
      exceptions_right_auto[state_key_right_auto]->push_back('\0');
      state_key_right_auto++;
    }

    tp = nullptr;
    pp = pp->next;
  }

  kill_paths(state_paths);
  state_paths = pp = nullptr;

  num_of_exceptions_to_add = state_key_right_auto; //num_of_exceptions_to_add is the number of new paths
  for (i = 0; i < this->dfa->ns; i++) {
    state_paths = pp = make_paths(this->dfa->bddm, this->dfa->q[i]);
    state_key_left_auto = 0;
    while (pp) {
      if (pp->to == (unsigned)sink_state_left_auto) {
        pp = pp->next;
        continue;
      }

      state_map_left_auto[state_key_left_auto] = pp->to;
      exceptions_left_auto[state_key_left_auto] = new std::vector<char>();
      for (j = 0; j < this->num_of_variables; j++) {
        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            exceptions_left_auto[state_key_left_auto]->push_back('1');
          } else {
            exceptions_left_auto[state_key_left_auto]->push_back('0');
          }
        } else {
          exceptions_left_auto[state_key_left_auto]->push_back('X');
        }
      }

      exceptions_left_auto[state_key_left_auto]->push_back('0'); // add extra bit, '0' is used for the exceptions coming from left auto
      exceptions_left_auto[state_key_left_auto]->push_back('\0');

      state_key_left_auto++;
      tp = nullptr;
      pp = pp->next;
    }

    // generate concat automaton
    int num_of_exceptions_left_auto = state_key_left_auto;
    if (this->isAcceptingState(i)) {
      dfaAllocExceptions(num_of_exceptions_left_auto + num_of_exceptions_to_add);
      for (int state_key = 0; state_key < num_of_exceptions_left_auto; state_key++) {
        dfaStoreException(state_map_left_auto[state_key], &*(exceptions_left_auto[state_key]->begin()));
      }
      for (int state_key = 0; state_key < num_of_exceptions_to_add; state_key++) {
        dfaStoreException(state_map_right_auto[state_key], &*(exceptions_right_auto[state_key]->begin()));
      }

      dfaStoreState(sink_state_left_auto);
      if (other_auto->isAcceptingState(0)) {
        statuses[i]='+';
      }
      else {
        statuses[i]='-';
      }
    } else {
      dfaAllocExceptions(num_of_exceptions_left_auto);
      for (int state_key = 0; state_key < num_of_exceptions_left_auto; state_key++) {
        dfaStoreException(state_map_left_auto[state_key], &*exceptions_left_auto[state_key]->begin());
      }
      dfaStoreState(sink_state_left_auto);
      statuses[i] = '-';
    }
    kill_paths(state_paths);
    state_paths = pp = nullptr;
  }

  // clear maps
  for (auto& entry : exceptions_left_auto) {
    entry.second->clear();
    delete entry.second;
  }
  for (auto& entry : exceptions_right_auto) {
    entry.second->clear();
    delete entry.second;
  }
  state_map_left_auto.clear();
  state_map_right_auto.clear();

  //  initflag is 1 iff init is reached by some state. In this case,
  for (i = 0; i < other_auto->dfa->ns; i++) {
    if ( i != sink_state_right_auto ) {
      if ( i != other_auto->dfa->s || is_start_state_reachable) {
        state_paths = pp = make_paths(other_auto->dfa->bddm, other_auto->dfa->q[i]);
        state_key_fix = 0;
        while (pp) {
          if ( pp->to != (unsigned)sink_state_right_auto) {
            state_map_fix[state_key_fix] = pp->to + state_id_shift_amount;

            if ( sink_state_right_auto >= 0 && pp->to > (unsigned)sink_state_right_auto) {
              state_map_fix[state_key_fix]--; //to new state, sink state will be eliminated and hence need -1
            }

            if ( (not is_start_state_reachable) && pp->to > (unsigned)other_auto->dfa->s) {
              state_map_fix[state_key_fix]--; // to new state, init state will be eliminated if init is not reachable
            }

            exceptions_fix[state_key_fix] = new std::vector<char>();
            for (j = 0; j < var; j++) {
              for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp =tp->next);
              if (tp) {
                if (tp->value){
                  exceptions_fix[state_key_fix]->push_back('1');
                }
                else {
                  exceptions_fix[state_key_fix]->push_back('0');
                }
              }
              else {
                exceptions_fix[state_key_fix]->push_back('X');
              }
            }
            exceptions_fix[state_key_fix]->push_back('0'); // old value
            exceptions_fix[state_key_fix]->push_back('\0');
            state_key_fix++;
            tp = nullptr;
          }
          pp = pp->next;
        }

        dfaAllocExceptions(state_key_fix);
        for (int state_key = 0; state_key < state_key_fix; state_key++) {
          dfaStoreException(state_map_fix[state_key], &*(exceptions_fix[state_key]->begin()));
        }

        dfaStoreState(sink_state_left_auto);

        loc = state_id_shift_amount + i;
        if ( (not is_start_state_reachable) && i > other_auto->dfa->s) {
          loc--;
        }
        if ( sink_state_right_auto >= 0 && i > sink_state_right_auto) {
          loc--;
        }

        if ( other_auto->isAcceptingState(i)) {
          statuses[loc]='+';
        } else {
          statuses[loc]='-';
        }

        kill_paths(state_paths);
        state_paths = pp = nullptr;
      }
    }
  }

//  statuses[expected_num_of_states]='\0';
  for (auto& entry : exceptions_fix) {
    entry.second->clear();
    delete entry.second;
  }
  state_map_fix.clear();

  concat_dfa = dfaBuild(statuses);
  tmp_dfa = dfaProject(concat_dfa, (unsigned) var);
  delete concat_dfa;
  concat_dfa = dfaMinimize(tmp_dfa);
  delete tmp_dfa;

  concat_auto = new IntAutomaton(concat_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << concat_auto->id << " = [" << this->id << "]->concat(" << other_auto->id << ")";

  return concat_auto;
}

IntAutomaton_ptr IntAutomaton::substract(IntAutomaton_ptr other_auto) {
  LOG(FATAL) << "Implement me";
  return nullptr;
}

bool IntAutomaton::checkEquivalance(IntAutomaton_ptr other_auto) {
  return (Automaton::checkEquivalence(other_auto) and (has_negative_1 == other_auto->has_negative_1));
}

bool IntAutomaton::isEmptyLanguage() {
  if (has_negative_1) {
    return false;
  }
  return Automaton::isEmptyLanguage();
}

bool IntAutomaton::hasZero() {
  return Automaton::isInitialStateAccepting();
}

bool IntAutomaton::isZero() {
  return (Automaton::isOnlyInitialStateAccepting() and (not has_negative_1));
}

bool IntAutomaton::isAcceptingSingleInt() {
  return (Automaton::isAcceptingSingleWord() not_eq has_negative_1);
}


} /* namespace Theory */
} /* namespace Vlab */
