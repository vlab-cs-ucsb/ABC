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

#include "BinaryIntAutomaton.h"
#include "IntAutomaton.h"
#include "StringAutomaton.h"

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
  DVLOG(VLOG_LEVEL) << cloned_auto->id_ << " = [" << this->id_ << "]->clone()";
  return cloned_auto;
}

UnaryAutomaton_ptr UnaryAutomaton::makePhi() {
  DFA_ptr non_accepting_unary_dfa = nullptr;
  UnaryAutomaton_ptr non_acception_unary_auto = nullptr;
  int a[1] = {0};
  non_accepting_unary_dfa = Automaton::DfaMakePhi(1, a);
  non_acception_unary_auto = new UnaryAutomaton(non_accepting_unary_dfa);

  DVLOG(VLOG_LEVEL) << non_acception_unary_auto->getId() << " = makePhi()";
  return non_acception_unary_auto;
}

UnaryAutomaton_ptr UnaryAutomaton::makeAutomaton(SemilinearSet_ptr semilinear_set) {
  UnaryAutomaton_ptr unary_auto = nullptr;
  DFA_ptr unary_dfa = nullptr, tmp_dfa = nullptr;

  const int cycle_head = semilinear_set->getCycleHead();
  const int period = semilinear_set->getPeriod();
  int number_of_variables = 1;
  int number_of_states = cycle_head + semilinear_set->getPeriod() + 1;
  int sink_state = number_of_states - 1;
  int* indices = getIndices(number_of_variables);
  char unary_exception[1] = {'1'};
  std::vector<char> statuses;
  bool has_only_constants = semilinear_set->hasOnlyConstants();

  if (semilinear_set->isEmptySet()) {
    return UnaryAutomaton::makePhi();
  } else if (has_only_constants) {
    number_of_states = semilinear_set->getConstants().back() + 2;
    sink_state = number_of_states - 1;
    semilinear_set->getPeriodicConstants().clear();
  }

  for (int i = 0; i < number_of_states; i++) {
    statuses.push_back('-');
  }
  statuses.push_back('\0');

  dfaSetup(number_of_states, number_of_variables, indices);

  for (int s = 0; s < number_of_states - 2; s++) {

    dfaAllocExceptions(1);
    dfaStoreException(s + 1, unary_exception);
    dfaStoreState(sink_state);
  }

  // Handle last state
  if (has_only_constants) {
    dfaAllocExceptions(0);
    dfaStoreState(sink_state);
  } else {
    dfaAllocExceptions(1);
    dfaStoreException(cycle_head, unary_exception);
    dfaStoreState(sink_state);
  }

  dfaAllocExceptions(0);
  dfaStoreState(sink_state);

  for (auto c : semilinear_set->getConstants()) {
    statuses[c] = '+';
  }

  for (auto r : semilinear_set->getPeriodicConstants()) {
    statuses[cycle_head + r] = '+';
  }

  unary_dfa = dfaBuild(&*statuses.begin());
  delete[] indices; indices = nullptr;
  if (not has_only_constants) {
    tmp_dfa = unary_dfa;
    unary_dfa = dfaMinimize(tmp_dfa);
    dfaFree(tmp_dfa); tmp_dfa = nullptr;
  }

  unary_auto = new UnaryAutomaton(unary_dfa);

  DVLOG(VLOG_LEVEL) << unary_auto->id_ << " = " << *semilinear_set;
  DVLOG(VLOG_LEVEL) << unary_auto->id_ << " = UnaryAutomaton::makeAutomaton(<semilinear set>)";
  return unary_auto;
}

SemilinearSet_ptr UnaryAutomaton::getSemilinearSet() {
  SemilinearSet_ptr semilinear_set = nullptr;

  int cycle_head_state = -1,
          current_state = this->dfa_->s,
          sink_state = this->getSinkState();

  CHECK_NE(-1, sink_state);

  std::vector<int> states;
  std::map<int, int> values;

  if (sink_state == current_state) {
    return new SemilinearSet();
  }

  // loop over all states except for sink state
  for (int s = 0; (s < this->dfa_->ns - 1); s++) {
    values[current_state] = s;
    states.push_back(current_state);

    for (auto next_state : getNextStates(current_state)) {
      if (next_state != sink_state) {
        if (values.find(next_state) != values.end()) {
          cycle_head_state = next_state;
          break;
        }
        current_state = next_state;
      }
    }

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
        if (is_accepting_state(state)) {
          semilinear_set->addPeriodicConstant(0);
        }
      } else {
        if (is_accepting_state(state)) {
          semilinear_set->addConstant(values[state]);
        }
      }
    } else {
      if (is_accepting_state(state)) {
        semilinear_set->addPeriodicConstant(values[state] - cycle_head_value);
      }
    }
  }

  semilinear_set->setCycleHead(cycle_head_value);
  int period = (cycle_head_state == -1) ? 0 : values[states.back()] - cycle_head_value + 1;
  semilinear_set->setPeriod(period);

  DVLOG(VLOG_LEVEL) << "semilinear set = [" << this->id_ << "]->getSemilinearSet()";

  return semilinear_set;
}

IntAutomaton_ptr UnaryAutomaton::toIntAutomaton(int number_of_variables, bool add_minus_one) {
  IntAutomaton_ptr int_auto = nullptr;
  DFA_ptr int_dfa = nullptr;
  int* indices = getIndices(number_of_variables);
  const int number_of_states = this->dfa_->ns;
  int to_state, sink_state = getSinkState();
  bool has_sink = true;

  if(sink_state < 0) {
    has_sink = false;
    sink_state = 0;
  }

  std::vector<char> unary_exception = {'1'};
  char* statuses = new char[number_of_states + 1];
  std::vector< std::vector<char> > exceptions = {
          {'X', 'X', 'X', 'X', 'X', 'X', 'X', 'X'}
  };

  for (auto& exception : exceptions) {
    exception.push_back('\0');
  }

  dfaSetup(number_of_states, number_of_variables, indices);

  for (int s = 0; s < this->dfa_->ns; s++) {
    if (s != sink_state || !has_sink) {
      to_state = getNextState(s, unary_exception);
      dfaAllocExceptions(exceptions.size());
      for (auto& exception : exceptions) {
        dfaStoreException(to_state, &*exception.begin());
      }
      dfaStoreState(sink_state);
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(sink_state);
    }

    if (is_accepting_state(s)) {
      statuses[s] = '+';
    } else {
      statuses[s] = '-';
    }
  }

  statuses[number_of_states] = '\0';

  DFA_ptr temp_dfa = dfaBuild(statuses);
  int_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);

  int_auto = new IntAutomaton(int_dfa, number_of_variables);

  if(!has_sink) {
    for(int i = 0; i < int_dfa->ns; i++) {
      if(int_dfa->f[i] == 0) {
        int_dfa->f[i] = -1;
      }
    }
  }

  int_auto->setMinus1(add_minus_one);
  delete[] indices; indices = nullptr;
  delete[] statuses; statuses = nullptr;
  DVLOG(VLOG_LEVEL)  << int_auto->getId() << " = [" << this->id_ << "]->toIntAutomaton(" << number_of_variables << ", " << add_minus_one << ")";

  return int_auto;
}

BinaryIntAutomaton_ptr UnaryAutomaton::toBinaryIntAutomaton(std::string var_name, ArithmeticFormula_ptr formula, bool add_minus_one) {
  BinaryIntAutomaton_ptr binary_auto = nullptr;
  SemilinearSet_ptr semilinear_set = getSemilinearSet();

  binary_auto = BinaryIntAutomaton::MakeAutomaton(semilinear_set, var_name, formula, true);

  if (add_minus_one) {
    BinaryIntAutomaton_ptr minus_one_auto = nullptr, tmp_auto = nullptr;
    ArithmeticFormula_ptr minus_one_formula = formula->clone();
    minus_one_formula->reset_coefficients();
    minus_one_formula->set_variable_coefficient(var_name, 1);
    minus_one_formula->set_constant(1);
    minus_one_formula->set_type(ArithmeticFormula::Type::EQ);
    minus_one_auto = BinaryIntAutomaton::MakeAutomaton(minus_one_formula, false);
    tmp_auto = binary_auto;
    binary_auto = tmp_auto->Union(minus_one_auto);
    delete tmp_auto; tmp_auto = nullptr;
    delete minus_one_auto; minus_one_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL)  << binary_auto->getId() << " = [" << this->id_ << "]->toBinaryIntAutomaton(" << var_name << ", " << *binary_auto->get_formula() << ", " << add_minus_one << ")";

  return binary_auto;
}

StringAutomaton_ptr UnaryAutomaton::toStringAutomaton() {
  StringAutomaton_ptr result_auto = StringAutomaton::makePhi(),
          tmp_1_auto = nullptr,
          tmp_2_auto = nullptr;

  int sink_state = this->getSinkState();
  int curr_state {this->dfa_->s};

  std::map<int, bool> is_visited;
  std::queue<int> work_list;
  if (curr_state != sink_state) {
    work_list.push(curr_state);
  }

  int value = 0;
  while ( not work_list.empty()) {
    curr_state = work_list.front(); work_list.pop();

    if (is_visited[curr_state]) { // cycle over approximate rest, an algorithm can be found to map between encodings (from semilinear set to string encoding)
      std::string value_str = std::to_string(value);
      std::string regex_str = "[0-9]{" + std::to_string(value_str.length()) + ",}";
      tmp_1_auto = StringAutomaton::makeRegexAuto(regex_str);
      tmp_2_auto = result_auto;
      result_auto = tmp_2_auto->concat(tmp_1_auto);
      delete tmp_1_auto;
      delete tmp_2_auto;
      break;
    }

    if (is_accepting_state(curr_state)) {
      tmp_1_auto = StringAutomaton::makeString(std::to_string(value));
      tmp_2_auto = result_auto;
      result_auto = tmp_2_auto->union_(tmp_1_auto);
      delete tmp_1_auto;
      delete tmp_2_auto;
    }
    ++value;
    for (auto next_state : this->getNextStates(curr_state)) {
      if (sink_state != next_state) {
        work_list.push(next_state);
      }
    }
  }

  DVLOG(VLOG_LEVEL)  << result_auto->getId() << " = [" << this->id_ << "]->toStringAutomaton()";
  return result_auto;
}

} /* namespace Theory */
} /* namespace Vlab */
