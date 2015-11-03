/*
 * UnaryAutomaton.cpp
 *
 *  Created on: Nov 5, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "UnaryAutomaton.h"

namespace Vlab {
namespace Theory {

const int UnaryAutomaton::VLOG_LEVEL = 9;

UnaryAutomaton::UnaryAutomaton(DFA_ptr dfa) :
      Automaton(Automaton::Type::UNARY, dfa, 1) { }

UnaryAutomaton::UnaryAutomaton(const UnaryAutomaton& other) : Automaton (other) {
}

UnaryAutomaton::~UnaryAutomaton() {
}

UnaryAutomaton_ptr UnaryAutomaton::clone() const {
  UnaryAutomaton_ptr cloned_auto = new UnaryAutomaton(*this);
  DVLOG(VLOG_LEVEL) << cloned_auto->id << " = [" << this->id << "]->clone()";
  return cloned_auto;
}

// TODO Refactor LibStranger implementation here
UnaryAutomaton_ptr UnaryAutomaton::makeAutomaton(IntAutomaton_ptr int_auto) {
  UnaryAutomaton_ptr unary_auto = nullptr;
  DFA_ptr unary_dfa = nullptr;

  unary_dfa = dfa_string_to_unaryDFA(int_auto->getDFA(), int_auto->getNumberOfVariables(), int_auto->getVariableIndices());
  unary_auto = new UnaryAutomaton(unary_dfa);
  DVLOG(VLOG_LEVEL) << unary_auto->id << " = UnaryAutomaton::makeAutomaton(" << int_auto->getId() << ")";
  return unary_auto;
}

UnaryAutomaton_ptr UnaryAutomaton::makeAutomaton(BinaryIntAutomaton_ptr bin_auto) {
  UnaryAutomaton_ptr unary_auto = nullptr;
  BinaryIntAutomaton_ptr trimmed_auto = nullptr;
  DFA_ptr unary_dfa = nullptr;
  SemilinearSet_ptr semilinear_set = nullptr;

  trimmed_auto = bin_auto->trimLeadingZeros();
  trimmed_auto->inspectAuto();

  semilinear_set = trimmed_auto->getSemilinearSet();

  // TODO construct semilinear set from binary auto
  delete trimmed_auto; trimmed_auto = nullptr;
  // TODO construct unary auto from semilinear set


  LOG(FATAL)<< "working here";
  // TEMPORARY MOCK
  IntAutomaton_ptr test = IntAutomaton::makeInt(8);
  unary_auto = UnaryAutomaton::makeAutomaton(test);
  // END TEMPORARY MOCK

//  unary_auto = new UnaryAutomaton(unary_dfa);
  DVLOG(VLOG_LEVEL) << unary_auto->id << " = UnaryAutomaton::makeAutomaton(" << bin_auto->getId() << ")";
  return unary_auto;
}

SemilinearSet_ptr UnaryAutomaton::getSemilinearSet() {
  SemilinearSet_ptr semilinear_set = nullptr;

  int cycle_head_state = -1,
          current_state = this->dfa->s,
          sink_state = this->getSinkState();

  CHECK_NE(-1, sink_state);

  std::vector<int> states;
  std::map<int, int> values;
  std::set<int>* next_states = nullptr;

  if (sink_state == current_state) {
    return new SemilinearSet();
  }

  // loop over all states except for sink state
  for (int s = 0; (s < this->dfa->ns - 1); s++) {
    values[current_state] = s;
    states.push_back(current_state);

    next_states = getNextStates(current_state);
    for (auto next_state : *next_states) {
      if (next_state != sink_state) {
        if (values.find(next_state) != values.end()) {
          cycle_head_state = next_state;
          break;
        }
        current_state = next_state;
      }
    }

    delete next_states; next_states = nullptr;
    if (cycle_head_state != -1) {
      break;
    }
  }

  semilinear_set = new SemilinearSet();
  int cycle_head_value = 0;
  bool is_in_cycle = isStartState(cycle_head_state);

  for (auto state : states) {
    if (not is_in_cycle) {
      if (state == cycle_head_state) {
        is_in_cycle = true;
        cycle_head_value = values[state];
        if (isAcceptingState(state)) {
          semilinear_set->addPeriodicConstant(0);
        }
      } else {
        if (isAcceptingState(state)) {
          semilinear_set->addConstant(values[state]);
        }
      }
    } else {
      if (isAcceptingState(state)) {
        semilinear_set->addPeriodicConstant(values[state] - cycle_head_value);
      }
    }
  }

  semilinear_set->setCycleHead(cycle_head_value);
  int period = (cycle_head_state == -1) ? 0 : values[states.back()] - cycle_head_value + 1;
  semilinear_set->setPeriod(period);

  DVLOG(VLOG_LEVEL) << "semilinear set = [" << this->id << "]->getSemilinearSet()";

  return semilinear_set;
}

IntAutomaton_ptr UnaryAutomaton::toIntAutomaton(bool add_minus_one) {
  IntAutomaton_ptr int_auto = nullptr, positive_int_auto = nullptr;
  DFA_ptr int_dfa = nullptr;

  positive_int_auto = IntAutomaton::makeIntGreaterThanOrEqual(0);
  int_dfa = dfa_restrict_by_unaryDFA(positive_int_auto->getDFA(), this->dfa,
          positive_int_auto->getNumberOfVariables(), positive_int_auto->getVariableIndices());

  int_auto = new IntAutomaton(int_dfa, positive_int_auto->getNumberOfVariables());
  int_auto->setMinus1(add_minus_one);
  delete positive_int_auto; positive_int_auto = nullptr;

  DVLOG(VLOG_LEVEL)  << int_auto->getId() << " = [" << this->id << "]->toIntAutomaton(" << add_minus_one << ")";

  return int_auto;
}

BinaryIntAutomaton_ptr UnaryAutomaton::toBinaryIntAutomaton(std::string var_name, ArithmeticFormula_ptr formula, bool add_minus_one) {
  BinaryIntAutomaton_ptr binary_auto = nullptr;

  int var_index = formula->getNumberOfVariables() - formula->getVariableIndex(var_name) - 1;
  binary_auto = toBinaryIntAutomaton(var_index, formula->getNumberOfVariables());
  binary_auto->setFormula(formula);

  if (add_minus_one) {
    BinaryIntAutomaton_ptr minus_one_auto = nullptr, tmp_auto = nullptr;
    ArithmeticFormula_ptr minus_one_formula = formula->clone();
    minus_one_formula->resetCoefficients();
    minus_one_formula->setVariableCoefficient(var_name, 1);
    minus_one_formula->setConstant(1);
    minus_one_formula->setType(ArithmeticFormula::Type::EQ);
    minus_one_auto = BinaryIntAutomaton::makeAutomaton(minus_one_formula);
    tmp_auto = binary_auto;
    binary_auto = tmp_auto->union_(minus_one_auto);
    delete tmp_auto; tmp_auto = nullptr;
    delete minus_one_auto; minus_one_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL)  << binary_auto->getId() << " = [" << this->id << "]->toBinaryIntAutomaton(" << var_name << ", " << *formula << ", " << add_minus_one << ")";

  return binary_auto;
}

BinaryIntAutomaton_ptr UnaryAutomaton::toBinaryIntAutomaton(int var_index, int number_of_variables) {
  BinaryIntAutomaton_ptr binary_auto = nullptr;
  DFA_ptr binary_dfa = nullptr;
  SemilinearSet_ptr semilinear_set = getSemilinearSet();
  DVLOG(VLOG_LEVEL)<< *semilinear_set;
  int number_of_binary_states;
  std::vector<BinaryState_ptr> binary_states;
  int* bin_variable_indices = getIndices(number_of_variables);
  char* statuses = nullptr;
  char* bit_transition = new char[number_of_variables + 1];

  for (int i = 0; i < number_of_variables; i++) {
    bit_transition[i] = 'X';
  }
  bit_transition[number_of_variables] = '\0';

  compute_binary_states(binary_states, semilinear_set);

  number_of_binary_states = binary_states.size();

  dfaSetup(number_of_binary_states + 1, number_of_variables, bin_variable_indices); // one extra state as sink state
  statuses = new char[number_of_binary_states + 2];
  for (int i = 0; i < number_of_binary_states; i++) {
    if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() >= 0) {
      dfaAllocExceptions(2);
      bit_transition[var_index] = '0';
      dfaStoreException(binary_states[i]->getd0(), bit_transition);
      bit_transition[var_index] = '1';
      dfaStoreException(binary_states[i]->getd1(), bit_transition);
    } else if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() < 0) {
      dfaAllocExceptions(1);
      bit_transition[var_index] = '0';
      dfaStoreException(binary_states[i]->getd0(), bit_transition);
    } else if (binary_states[i]->getd0() < 0 && binary_states[i]->getd1() >= 0) {
      dfaAllocExceptions(1);
      bit_transition[var_index] = '1';
      dfaStoreException(binary_states[i]->getd1(), bit_transition);
    } else {
      dfaAllocExceptions(0);
    }
    dfaStoreState(number_of_binary_states);
    statuses[i] = get_binary_status(binary_states[i], semilinear_set);
  }

  // for the sink state
  dfaAllocExceptions(0);
  dfaStoreState(number_of_binary_states);
  statuses[number_of_binary_states] = '-';
  statuses[number_of_binary_states + 1] = '\0';
  binary_dfa = dfaBuild(statuses);

  for (auto &bin_state : binary_states) {
    delete bin_state; bin_state = nullptr;
  }
  delete semilinear_set;
  delete[] statuses;
  delete[] bin_variable_indices;
  delete[] bit_transition;

  binary_auto = new BinaryIntAutomaton(dfaMinimize(binary_dfa), number_of_variables);
  // formula is set on the caller site
  delete binary_dfa; binary_dfa = nullptr;

  DVLOG(VLOG_LEVEL)  << binary_auto->getId() << " = [" << this->id << "]->toBinaryIntAutomaton(" << var_index << ", " << number_of_variables << ")";

  return binary_auto;
}

void UnaryAutomaton::compute_binary_states(std::vector<BinaryState_ptr>& binary_states, SemilinearSet_ptr semilinear_set) {
  if (semilinear_set->getPeriod() == 0) {
    add_binary_state(binary_states, semilinear_set->getConstants());
  } else {
    add_binary_state(binary_states, semilinear_set->getCycleHead(), semilinear_set->getPeriod(), BinaryState::Type::VAL, -1, -1);

    // add leading zeros

    BinaryState_ptr next_state = nullptr, leading_zero_state = nullptr;
    int leading_zero_index = -1;
    int num_of_binary_states = binary_states.size();

    for (int i = 0; i < num_of_binary_states; i++) {
      if ( (not binary_states[i]->isLeadingZeroState()) and '+' == get_binary_status(binary_states[i], semilinear_set)) {
        if (binary_states[i]->getd0() == -1) {
          leading_zero_state = new BinaryState(-2, -1);
          leading_zero_index = binary_states.size();
          binary_states.push_back(leading_zero_state);
          leading_zero_state->setd0(leading_zero_index);
          binary_states[i]->setd0(leading_zero_index);
        } else {
          next_state = binary_states[binary_states[i]->getd0()];

          if ( '-' == get_binary_status(next_state, semilinear_set)) {
            CHECK_EQ(binary_states[i]->getd0(), next_state->getd0()) << "next state should not have a zero transition other than self (if for sure it has fix me)";
            leading_zero_state = new BinaryState(-2, -1);
            leading_zero_index = binary_states.size();
            binary_states.push_back(leading_zero_state);

            leading_zero_state->setd0(leading_zero_index);
            binary_states[i]->setd0(leading_zero_index);
            leading_zero_state->setd1(next_state->getd1());
          }
        }
      }
    }
  }
}

/**
 * Works for only positive constants, can be extended to handle negative ones
 */
void UnaryAutomaton::add_binary_state(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants) {

  std::map<std::pair<int, int>, int> binary_state_map;

  binary_states.push_back(new BinaryState(-1, 0));
  binary_state_map.insert(std::make_pair(std::make_pair(-1, 0), 0));

  for (auto value : constants) {
    unsigned i = 0;
    int rank = 1;
    int mask = value;
    int state_value = 0;
    int current_bit = 0;

    do {
      current_bit = mask & 1;
      if (current_bit) {
        state_value = state_value | (1 << (rank - 1));
      }
      auto key = std::make_pair(state_value, rank);
      auto it = binary_state_map.find(key);

      if (it == binary_state_map.end()) {
        binary_states.push_back(new BinaryState(state_value, rank));
        int index = binary_states.size() - 1;
        binary_state_map[key] = index;
        if (current_bit) {
          binary_states[i]->setd1(index);
        } else {
          binary_states[i]->setd0(index);
        }
        i = index;
      } else {
        i = it->second;
      }

      mask >>= 1;
      rank += 1;
    } while (state_value not_eq value);
  }

  int leading_zero_index = -1;
  if (constants.size() > 0) {
    binary_states.push_back(new BinaryState(-2, -1)); // (-2, -1) is a special node for leading zeros
    leading_zero_index = binary_states.size() - 1;
    binary_state_map.insert(std::make_pair(std::make_pair(-2, -1), leading_zero_index));
    binary_states[leading_zero_index]->setd0(leading_zero_index);
  }

  // add leading zeros
  for (auto value : constants) {
    int rank = 0;
    int mask = value;
    do {
      mask >>= 1;
      rank += 1;
    } while (mask > 0);

    auto key = std::make_pair(value, rank);
    auto it = binary_state_map.find(key);
    int index = it->second;
    bool has_leading_zero = false;

    while (binary_states[index]->getd0() != -1 and index != leading_zero_index) {
      index = binary_states[index]->getd0();
    }

    if (index != leading_zero_index) {
      binary_states[index]->setd0(leading_zero_index);
    }
  }
}

int UnaryAutomaton::add_binary_state(std::vector<BinaryState_ptr>& binary_states, int C, int R, BinaryState::Type t, int v, int b) {
  unsigned i = 0;
  int d0 = -1, d1 = -1;

  for (i = 0; i < binary_states.size(); i++) {
    if (binary_states[i]->isEqualTo(t, v, b)) {
      return i;
    }
  }

  binary_states.push_back(new BinaryState(t, v, b));

  if (b < 0) {
    if (C == 0) {
      d1 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, 1 % R, 1 % R);
      d0 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, 0, 1 % R);
    } else if (C == 1) {
      d1 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, 1 % R, 1 % R);
      d0 = add_binary_state(binary_states, C, R, BinaryState::Type::REMF, 0, 1 % R);
    } else {
      d1 = add_binary_state(binary_states, C, R, BinaryState::Type::VAL, 1, 1);
      d0 = add_binary_state(binary_states, C, R, BinaryState::Type::VAL, 0, 1);
    }
  } else if (BinaryState::Type::VAL == t && (v + 2 * b >= C)) {
    d1 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
    d0 = add_binary_state(binary_states, C, R, BinaryState::Type::REMF, v % R, (2 * b) % R);
  } else if (BinaryState::Type::VAL == t && (v + 2 * b < C)) {
    d1 = add_binary_state(binary_states, C, R, BinaryState::Type::VAL, v + 2 * b, 2 * b);
    d0 = add_binary_state(binary_states, C, R, BinaryState::Type::VAL, v, 2 * b);
  } else if (BinaryState::Type::REMT == t) {
    d1 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
    d0 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, v % R, (2 * b) % R);
  } else if (BinaryState::Type::REMF == t) {
    d1 = add_binary_state(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
    d0 = add_binary_state(binary_states, C, R, BinaryState::Type::REMF, v % R, (2 * b) % R);
  }

  binary_states[i]->setd0d1(d0, d1);

  return i;
}

char UnaryAutomaton::get_binary_status(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set) {
  if (binary_state->isLeadingZeroState()) {
    return '+';
  } else if (BinaryState::Type::VAL == binary_state->getType()) {
    for (auto i : semilinear_set->getConstants()) {
      if (i == binary_state->getV()) {
        return '+';
      }
    }
  } else if (BinaryState::Type::REMT == binary_state->getType()) {
    for (auto i : semilinear_set->getPeriodicConstants()) {
      if ( ((i + semilinear_set->getCycleHead()) % (semilinear_set->getPeriod())) == binary_state->getV() ) {
        return '+';
      }
    }
  }
  return '-';
}

} /* namespace Theory */
} /* namespace Vlab */
