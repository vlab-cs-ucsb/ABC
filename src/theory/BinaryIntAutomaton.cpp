/*
 * BinaryIntAutomaton.cpp
 *
 *  Created on: Oct 16, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "BinaryIntAutomaton.h"

#include <glog/logging.h>
#include <mona/dfa.h>
#include <iostream>
#include <iterator>
#include <map>
#include <string>

namespace Vlab {
namespace Theory {

const int BinaryIntAutomaton::VLOG_LEVEL = 9;

BinaryIntAutomaton::BinaryIntAutomaton() :
     Automaton(Automaton::Type::BINARYINT), formula (nullptr) {
}

BinaryIntAutomaton::BinaryIntAutomaton(DFA_ptr dfa, int num_of_variables) :
     Automaton(Automaton::Type::BINARYINT, dfa, num_of_variables), formula (nullptr) {

}

BinaryIntAutomaton::BinaryIntAutomaton(const BinaryIntAutomaton& other) :
     Automaton(other) {
  if (other.formula) {
    formula = other.formula->clone();
  }
}

BinaryIntAutomaton::~BinaryIntAutomaton() {
  delete formula;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::clone() const {
  BinaryIntAutomaton_ptr cloned_auto = new BinaryIntAutomaton(*this);
  DVLOG(VLOG_LEVEL) << cloned_auto->id << " = [" << this->id << "]->clone()";
  return cloned_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makePhi(ArithmeticFormula_ptr formula) {
  DFA_ptr non_accepting_dfa = nullptr;
  BinaryIntAutomaton_ptr non_accepting_binary_auto = nullptr;
  int num_variables = formula->getNumberOfVariables();
  int* indices = Automaton::getIndices(num_variables);

  non_accepting_dfa = Automaton::makePhi(num_variables, indices);
  delete[] indices; indices = nullptr;
  non_accepting_binary_auto = new BinaryIntAutomaton(non_accepting_dfa, num_variables);
  non_accepting_binary_auto->setFormula(formula);

  DVLOG(VLOG_LEVEL) << non_accepting_binary_auto->id << " = makePhi(" << *formula << ")";

  return non_accepting_binary_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeAutomaton(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr result_auto = nullptr;

  switch (formula->getType()) {
    case ArithmeticFormula::Type::EQ: {
      result_auto = BinaryIntAutomaton::makeEquality(formula);
      break;
    }
    case ArithmeticFormula::Type::NOTEQ: {
      result_auto = BinaryIntAutomaton::makeNotEquality(formula);
      break;
    }
    case ArithmeticFormula::Type::GT: {
      result_auto = BinaryIntAutomaton::makeGreaterThan(formula);
      break;
    }
    case ArithmeticFormula::Type::GE: {
      result_auto = BinaryIntAutomaton::makeGreaterThanOrEqual(formula);
      break;
    }
    case ArithmeticFormula::Type::LT: {
      result_auto = BinaryIntAutomaton::makeLessThan(formula);
      break;
    }
    case ArithmeticFormula::Type::LE: {
      result_auto = BinaryIntAutomaton::makeLessThanOrEqual(formula);
      break;
    }
    default:
      LOG(FATAL)<< "Equation type is not specified, please set type for input formula: " << *formula;
      break;
  }

  return result_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeAutomaton(int value, std::string var_name,
        ArithmeticFormula_ptr formula, bool add_leading_zeros) {

  ArithmeticFormula_ptr constant_value_formula = formula->clone();
  constant_value_formula->resetCoefficients();
  constant_value_formula->setVariableCoefficient(var_name, 1);
  constant_value_formula->setConstant(-value);
  constant_value_formula->setType(ArithmeticFormula::Type::EQ);
  BinaryIntAutomaton_ptr binary_auto = BinaryIntAutomaton::makeAutomaton(constant_value_formula);

  DVLOG(VLOG_LEVEL)  << binary_auto->getId() << " = BinaryIntAutomaton::makeAutomaton(" << value << ", " << var_name << ", " << *formula << ", " << std::boolalpha << add_leading_zeros << ")";

  return binary_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeAutomaton(SemilinearSet_ptr semilinear_set, std::string var_name,
        ArithmeticFormula_ptr formula, bool add_leading_zeros) {
  BinaryIntAutomaton_ptr binary_auto = nullptr;
  DFA_ptr binary_dfa = nullptr, tmp_dfa = nullptr;
  int var_index = formula->getNumberOfVariables() - formula->getVariableIndex(var_name) - 1;
  int number_of_variables = formula->getNumberOfVariables(),
          leading_zero_state = 0,
          sink_state = 0,
          number_of_binary_states = 0,
          number_of_states = 0,
          lz_index = 0;
  if (add_leading_zeros) {
    number_of_variables = number_of_variables + 1;
    lz_index = number_of_variables - 1;
  }

  DVLOG(VLOG_LEVEL)<< *semilinear_set;
  std::vector<BinaryState_ptr> binary_states;
  int* indices = getIndices(number_of_variables);
  char* statuses = nullptr;
  char* bit_transition = new char[number_of_variables + 1];

  for (int i = 0; i < number_of_variables; i++) {
    bit_transition[i] = 'X';
  }
  bit_transition[number_of_variables] = '\0';

  compute_binary_states(binary_states, semilinear_set);

  number_of_binary_states = binary_states.size();
  number_of_states = number_of_binary_states + 1;
  if (add_leading_zeros) {
    number_of_states = number_of_states + 1;
    leading_zero_state = number_of_states - 2;
  }
  sink_state = number_of_states - 1;

  dfaSetup(number_of_states, number_of_variables, indices);
  statuses = new char[number_of_states + 1];
  bool is_final_state = false;
  for (int i = 0; i < number_of_binary_states; i++) {
    is_final_state = is_accepting_binary_state(binary_states[i], semilinear_set);

    if (add_leading_zeros and is_final_state) {
      if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() >= 0) {
        dfaAllocExceptions(3);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '0';
        dfaStoreException(binary_states[i]->getd0(), bit_transition);
        bit_transition[var_index] = '1';
        bit_transition[lz_index] = 'X';
        dfaStoreException(binary_states[i]->getd1(), bit_transition);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, bit_transition);
      } else if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() < 0) {
        dfaAllocExceptions(2);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '0';
        dfaStoreException(binary_states[i]->getd0(), bit_transition);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, bit_transition);
      } else if (binary_states[i]->getd0() < 0 && binary_states[i]->getd1() >= 0) {
        dfaAllocExceptions(2);
        bit_transition[var_index] = '1';
        bit_transition[lz_index] = 'X';
        dfaStoreException(binary_states[i]->getd1(), bit_transition);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, bit_transition);
      } else {
        dfaAllocExceptions(1);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, bit_transition);
      }
      bit_transition[lz_index] = 'X';
    } else {
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
    }

    dfaStoreState(sink_state);

    if (add_leading_zeros) {
      statuses[i] = '-';
    } else if (is_final_state) {
      statuses[i] = '+';
    } else {
      statuses[i] = '-';
    }
  }

  // for the leading zero state
  if (add_leading_zeros) {
    dfaAllocExceptions(1);
    bit_transition[var_index] = '0';
    bit_transition[lz_index] = '1';
    dfaStoreException(leading_zero_state, bit_transition);
    dfaStoreState(sink_state);
    statuses[leading_zero_state] = '+';
  }

  // for the sink state
  dfaAllocExceptions(0);
  dfaStoreState(sink_state);
  statuses[sink_state] = '-';

  int zero_state = binary_states[0]->getd0(); // adding leading zeros makes acceptin zero 00, fix here
  if ( zero_state > -1 and is_accepting_binary_state(binary_states[zero_state], semilinear_set)) {
    statuses[zero_state] = '+';
  }

  statuses[number_of_states] = '\0';
  binary_dfa = dfaBuild(statuses);

  for (auto &bin_state : binary_states) {
    delete bin_state; bin_state = nullptr;
  }

  delete[] statuses;
  delete[] indices;
  delete[] bit_transition;

  if (add_leading_zeros) {
    tmp_dfa = binary_dfa;
    binary_dfa = dfaProject(binary_dfa, (unsigned) (lz_index));
    dfaFree(tmp_dfa); tmp_dfa = nullptr;
    number_of_variables = number_of_variables - 1;
  }

  binary_auto = new BinaryIntAutomaton(dfaMinimize(binary_dfa), number_of_variables);
  binary_auto->setFormula(formula);
  dfaFree(binary_dfa); binary_dfa = nullptr;

  // binary state computation for semilinear sets may have leading zeros, remove them
  if ((not add_leading_zeros) and (not semilinear_set->hasOnlyConstants())) {
    BinaryIntAutomaton_ptr trim_helper_auto = nullptr, tmp_auto = nullptr;
    trim_helper_auto = BinaryIntAutomaton::makeTrimHelperAuto(var_index, number_of_variables);
    trim_helper_auto->setFormula(formula->clone());
    tmp_auto = binary_auto;
    binary_auto = binary_auto->intersect(trim_helper_auto);
    binary_auto->setFormula(formula);
    delete trim_helper_auto; trim_helper_auto = nullptr;
    tmp_auto->setFormula(nullptr);
    delete tmp_auto; tmp_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL)  << binary_auto->getId() << " = BinaryIntAutomaton::makeAutomaton(<semilinear_set>, " << var_name << ", " << *formula << ", " << std::boolalpha << add_leading_zeros << ")";

  return binary_auto;
}

ArithmeticFormula_ptr BinaryIntAutomaton::getFormula() {
  return formula;
}

void BinaryIntAutomaton::setFormula(ArithmeticFormula_ptr formula) {
  this->formula = formula;
}

bool BinaryIntAutomaton::hasNegative1() {
  CHECK_EQ(1, num_of_variables)<< "implemented for single track binary automaton";
  std::vector<char> exception = {'1'};
  std::map<int, bool> is_visited;
  int current_state = this->dfa->s;
  while (not is_visited[current_state]) {
    is_visited[current_state] = true;
    current_state = getNextState(current_state, exception);
    if (current_state > -1 and isAcceptingState(current_state)) {
      return true;
    }
  }

  return false;
}

// bdd vars are ordered in the reverse order of coefficients
int BinaryIntAutomaton::getBddVarIndex(std::string var_name) {
  return num_of_variables - formula->getVariableIndex(var_name) - 1;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::complement() {
  BinaryIntAutomaton_ptr complement_auto = nullptr;
  DFA_ptr complement_dfa = dfaCopy(this->dfa);

  dfaNegation(complement_dfa);

  complement_auto = new BinaryIntAutomaton(complement_dfa, num_of_variables);
  complement_auto->setFormula(this->formula->negateOperation());

  DVLOG(VLOG_LEVEL) << complement_auto->id << " = [" << this->id << "]->complement()";
  return complement_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::intersect(BinaryIntAutomaton_ptr other_auto) {
  DFA_ptr intersect_dfa = nullptr, minimized_dfa = nullptr;
  BinaryIntAutomaton_ptr intersect_auto = nullptr;
  ArithmeticFormula_ptr intersect_formula = nullptr;

  if (not formula->isVariableOrderingSame(other_auto->formula)) {
    LOG(FATAL)<< "You cannot intersect binary automata with different variable orderings";
  }

  intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaAND);
  minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
  intersect_dfa = nullptr;

  intersect_auto = new BinaryIntAutomaton(minimized_dfa, num_of_variables);
  intersect_formula = this->formula->clone();
  intersect_formula->resetCoefficients();
  intersect_formula->setType(ArithmeticFormula::Type::INTERSECT);
  intersect_auto->setFormula(intersect_formula);

  DVLOG(VLOG_LEVEL) << intersect_auto->id << " = [" << this->id << "]->intersect(" << other_auto->id << ")";

  return intersect_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::union_(BinaryIntAutomaton_ptr other_auto) {
  DFA_ptr union_dfa = nullptr, minimized_dfa = nullptr;
  BinaryIntAutomaton_ptr union_auto = nullptr;
  ArithmeticFormula_ptr union_formula = nullptr;

  if (not formula->isVariableOrderingSame(other_auto->formula)) {
    LOG(FATAL)<< "You cannot union binary automata with different variable orderings";
  }

  union_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaOR);
  minimized_dfa = dfaMinimize(union_dfa);
  dfaFree(union_dfa);
  union_dfa = nullptr;

  union_auto = new BinaryIntAutomaton(minimized_dfa, num_of_variables);
  union_formula = this->formula->clone();
  union_formula->resetCoefficients();
  union_formula->setType(ArithmeticFormula::Type::UNION);
  union_auto->setFormula(union_formula);

  DVLOG(VLOG_LEVEL) << union_auto->id << " = [" << this->id << "]->union(" << other_auto->id << ")";

  return union_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::difference(BinaryIntAutomaton_ptr other_auto) {
  BinaryIntAutomaton_ptr difference_auto = nullptr, complement_auto = nullptr;

  complement_auto = other_auto->complement();
  difference_auto = this->intersect(complement_auto);
  delete complement_auto; complement_auto = nullptr;

  DVLOG(VLOG_LEVEL) << difference_auto->id << " = [" << this->id << "]->difference(" << other_auto->id << ")";

  return difference_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::exists(std::string var_name) {
  LOG(FATAL)<< "implement me";
  return nullptr;
}
BinaryIntAutomaton_ptr BinaryIntAutomaton::getBinaryAutomatonFor(std::string var_name) {
  BinaryIntAutomaton_ptr single_var_auto = nullptr;
  ArithmeticFormula_ptr single_var_formula = nullptr;
  DFA_ptr single_var_dfa = dfaCopy(this->dfa), tmp_dfa = nullptr;
  CHECK_EQ(num_of_variables, formula->getNumberOfVariables())<< "number of variables is not consistent with formula";
  int bdd_var_index = getBddVarIndex(var_name);
  for (int i = num_of_variables - 1 ; i >= 0; i--) {
    if (i != bdd_var_index) {
      tmp_dfa = single_var_dfa;
      single_var_dfa = dfaProject(tmp_dfa, (unsigned)i);
      if (tmp_dfa != dfa) {
        dfaFree(tmp_dfa);
      }
      tmp_dfa = single_var_dfa;
      single_var_dfa = dfaMinimize(tmp_dfa);
      dfaFree(tmp_dfa);
    }
  }

  int* indices_map = getIndices(num_of_variables);
  indices_map[bdd_var_index] = 0;
  dfaReplaceIndices(single_var_dfa, indices_map);
  delete[] indices_map;

  single_var_auto = new BinaryIntAutomaton(single_var_dfa, 1);
  single_var_formula = new ArithmeticFormula();
  single_var_formula->setType(ArithmeticFormula::Type::INTERSECT);
  single_var_formula->setVariableCoefficient(var_name, 1);
  single_var_auto->setFormula(single_var_formula);

  DVLOG(VLOG_LEVEL) << single_var_auto->id << " = [" << this->id << "]->getBinaryAutomatonOf(" << var_name << ")";
  return single_var_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::getPositiveValuesFor(std::string var_name) {
  BinaryIntAutomaton_ptr positives_auto = nullptr, greater_than_or_equalt_to_zero_auto = nullptr;

  std::vector<int> indexes;
  int var_index = formula->getNumberOfVariables() - formula->getVariableIndex(var_name) - 1;
  indexes.push_back(var_index);

  greater_than_or_equalt_to_zero_auto = BinaryIntAutomaton::makeGraterThanOrEqualToZero(indexes, formula->getNumberOfVariables());
  greater_than_or_equalt_to_zero_auto->setFormula(formula->clone());

  positives_auto = this->intersect(greater_than_or_equalt_to_zero_auto);

  delete greater_than_or_equalt_to_zero_auto;
  greater_than_or_equalt_to_zero_auto = nullptr;

  DVLOG(VLOG_LEVEL) << positives_auto->id << " = [" << this->id << "]->getPositiveValuesFor(" << var_name <<")";
  return positives_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::getNegativeValuesFor(std::string var_name) {
  BinaryIntAutomaton_ptr negatives_auto = nullptr;

  LOG(FATAL)<< "implement me";
//  negatives_auto = this->intersect();

  DVLOG(VLOG_LEVEL) << negatives_auto->id << " = [" << this->id << "]->getNegativeValuesFor(" << var_name <<")";
  return negatives_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::trimLeadingZeros() {
  CHECK_EQ(1, num_of_variables)<< "trimming is implemented for single track positive binary automaton";

  BinaryIntAutomaton_ptr tmp_auto = this->clone();

  // identify leading zeros
  std::vector<char> exception = {'0'};
  int next_state = -1;
  int sink_state = tmp_auto->getSinkState();
  std::unordered_map<int, std::vector<int>> possible_final_states;
  std::stack<int> final_states;
  for (int i = 0; i < tmp_auto->dfa->ns; i++) {
    next_state = getNextState(i, exception);
    if ((sink_state not_eq next_state) and (i not_eq next_state)) {
      possible_final_states[next_state].push_back(i);
    }
    if (isAcceptingState(i)) {
      final_states.push(i);
    }
  }

  while (not final_states.empty()) {
    next_state = final_states.top(); final_states.pop();
    for (auto s : possible_final_states[next_state]) {
      if (not tmp_auto->isAcceptingState(s)) {
        tmp_auto->dfa->f[s] = 1;
        final_states.push(s);
      }
    }
  }

  tmp_auto->minimize();

  BinaryIntAutomaton_ptr trim_helper_auto = BinaryIntAutomaton::makeTrimHelperAuto(0,num_of_variables);
  trim_helper_auto->setFormula(tmp_auto->formula->clone());
  BinaryIntAutomaton_ptr trimmed_auto = tmp_auto->intersect(trim_helper_auto);
  delete tmp_auto; tmp_auto = nullptr;
  delete trim_helper_auto; trim_helper_auto = nullptr;

  DVLOG(VLOG_LEVEL) << trimmed_auto->id << " = [" << this->id << "]->trimLeadingZeros()";
  return trimmed_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::addLeadingZeros() {
  LOG(FATAL)<< "implement me (similar to string->toUnary function)";
  BinaryIntAutomaton_ptr leading_zero_auto = nullptr;
  DFA_ptr leading_zero_dfa = nullptr, tmp_dfa = nullptr;

  int number_of_variables = num_of_variables + 1,
          leading_zero_state = number_of_variables - 1,
          to_state = 0;
  int* indices = getIndices(number_of_variables);

  std::vector<char> leading_zero_exception;
  std::vector<char> statuses;
  std::map<std::vector<char>*, int> exceptions;
  std::vector<char>* current_exception = nullptr;

  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;

  for (int i = 0; i < number_of_variables; i++) {
    leading_zero_exception.push_back('0');
  }

  DVLOG(VLOG_LEVEL) << leading_zero_auto->id << " = [" << this->id << "]->trimLeadingZeros()";
  return leading_zero_auto;
}

/*
 *  TODO options to fix problems
 *  Search to improve period search part to make it sound
 *
 */
SemilinearSet_ptr BinaryIntAutomaton::getSemilinearSet() {
  SemilinearSet_ptr semilinear_set = nullptr,
          current_set = nullptr, tmp_set = nullptr;
  BinaryIntAutomaton_ptr subject_auto = nullptr,
          tmp_1_auto = nullptr, tmp_2_auto = nullptr,
          diff_auto = nullptr;
  std::vector<SemilinearSet_ptr> semilinears;
  std::string var_name = this->formula->getCoefficientIndexMap().begin()->first;
  int current_state = this->dfa->s,
          sink_state = this->getSinkState();
  std::vector<int> constants, bases;
  bool is_cyclic = false;
  std::map<int, bool> cycle_status;

  semilinear_set = new SemilinearSet();

  // 1- First get the constants that are reachable by only taking an edge of a SCC that has one state inside

  is_cyclic = getCycleStatus(cycle_status);
  getConstants(cycle_status, constants);
  Util::List::sort_and_remove_duplicate(constants);
  cycle_status.clear();
  semilinear_set->setConstants(constants);

  // CASE automaton has only constants
  if (not is_cyclic) {
    DVLOG(VLOG_LEVEL)<< *semilinear_set;
    DVLOG(VLOG_LEVEL) << "<semilinear set> = [" << this->id << "]->getSemilinearSet()";
    return semilinear_set;
  }

  /*
   * - Get the maximum constant and make an automaton Ac that accepts 0 <= x <= max
   * - Make new constants equal to the numbers that are accepted by original automaton (A)
   * intersection with Ac
   * Delete these numbers from original automaton
   */
  if (semilinear_set->hasConstants()) {

    int max_constant = constants.back(); // it is already sorted
    constants.clear();
    for (int i = 0; i <= max_constant; i++) {
      constants.push_back(i);
    }
    semilinear_set->setConstants(constants);
    constants.clear();
    tmp_1_auto = BinaryIntAutomaton::makeAutomaton(semilinear_set, var_name, formula->clone(), false);
    semilinear_set->clear();

    tmp_2_auto = this->intersect(tmp_1_auto);
    delete tmp_1_auto; tmp_1_auto = nullptr;

    tmp_2_auto->getBaseConstants(constants); // automaton is acyclic, it will return all constants
    Util::List::sort_and_remove_duplicate(constants);
    semilinear_set->setConstants(constants);
    constants.clear();

    subject_auto = this->difference(tmp_2_auto);
    delete tmp_2_auto; tmp_2_auto = nullptr;
  } else {
    subject_auto = this->clone();
  }

  semilinears.push_back(semilinear_set);

  unsigned i = 0;
  int cycle_head = 0;
  std::vector<int> tmp_periods;
  int bound = 0;
  while (not subject_auto->isEmptyLanguage() and (bound++ < 5)) {
    i = 0;
    cycle_head = 0;
    tmp_periods.clear();
    semilinear_set = new SemilinearSet();
    subject_auto->getBaseConstants(bases);
    Util::List::sort_and_remove_duplicate(bases);

    // usually we do not need to much numbers once they are sorted, note that this is not sound
    // to make it sound iteratively check for periods instead of deleting them
    if (bases.size() > 10) {
      bases.erase(bases.begin() + 10, bases.end());
    }

    if (bases.size() == 1) {
      semilinear_set->setPeriod(bases[0]);
      semilinear_set->addPeriodicConstant(0);
      semilinears.push_back(semilinear_set->clone());
      // no need to verify period
    } else if (bases.size() > 1) {
      int possible_period = 0;

      for (auto it = bases.begin(); it < bases.end() - 1; it++) {
        cycle_head = *it;
        bool period_found = false;
        for (auto jt = it + 1; jt < bases.end(); jt++) {
          possible_period = *jt - cycle_head;

          bool add_me = true;
          for (auto p : tmp_periods) {
            if ( (possible_period % p) == 0 ) {
              add_me = false;
              break;
            }
          }
          if (add_me) {
            current_set = new SemilinearSet();
            current_set->setCycleHead(cycle_head);
            current_set->setPeriod(possible_period);
            current_set->addPeriodicConstant(0);
            tmp_1_auto = BinaryIntAutomaton::makeAutomaton(current_set, var_name, formula->clone(), false);
            tmp_2_auto = subject_auto->intersect(tmp_1_auto);
            diff_auto = tmp_1_auto->difference(tmp_2_auto);
            delete tmp_1_auto; tmp_1_auto = nullptr;
            delete tmp_2_auto; tmp_2_auto = nullptr;
            if (diff_auto->isEmptyLanguage()) {
              tmp_set = semilinear_set;
              semilinear_set = tmp_set->merge(current_set);
              delete tmp_set; tmp_set = nullptr;
              semilinears.push_back(current_set);
              tmp_periods.push_back(possible_period);
              period_found = true;
            } else {
              delete current_set;
            }
            delete diff_auto; diff_auto = nullptr;
            current_set = nullptr;
          }
        }

        if (period_found) {
          for (auto rt = it + 1; rt < bases.end();) {
            possible_period = *rt - cycle_head;
            bool remove_me = false;
            for (auto p : tmp_periods) {
              if ( (possible_period % p) == 0 ) {
                remove_me = true;
                break;
              }
            }
            if (remove_me) {
              rt = bases.erase(rt);
            } else {
              rt++;
            }
          }
          period_found = false;
        }
      }
    } else {
      LOG(FATAL)<< "Automaton must have an accepting state, check base extraction algorithm";
    }

    tmp_1_auto = BinaryIntAutomaton::makeAutomaton(semilinear_set, var_name, formula->clone(), false);
    tmp_2_auto = subject_auto;
    subject_auto = tmp_2_auto->difference(tmp_1_auto);
    delete tmp_1_auto; tmp_1_auto = nullptr;
    delete tmp_2_auto; tmp_2_auto = nullptr;
    delete semilinear_set; semilinear_set = nullptr;
    bases.clear();
  }

  semilinear_set = new SemilinearSet();
  for (auto s : semilinears) {
    tmp_set = semilinear_set;
    semilinear_set = semilinear_set->merge(s);
    delete tmp_set;
    delete s;
  }

  DVLOG(VLOG_LEVEL)<< *semilinear_set;
  DVLOG(VLOG_LEVEL) << "semilinear set = [" << this->id << "]->getSemilinearSet()";

  return semilinear_set;
}

UnaryAutomaton_ptr BinaryIntAutomaton::toUnaryAutomaton() {
  UnaryAutomaton_ptr unary_auto = nullptr;
  BinaryIntAutomaton_ptr trimmed_auto = nullptr;
  SemilinearSet_ptr semilinear_set = nullptr;
  trimmed_auto = this->trimLeadingZeros();
  semilinear_set = trimmed_auto->getSemilinearSet();
  delete trimmed_auto; trimmed_auto = nullptr;

  unary_auto = UnaryAutomaton::makeAutomaton(semilinear_set);
  delete semilinear_set; semilinear_set = nullptr;
  DVLOG(VLOG_LEVEL) << unary_auto->getId() << " = [" << this->id << "]->toUnaryAutomaton()";
  return unary_auto;
}

std::map<std::string, int> BinaryIntAutomaton::getAnAcceptingIntForEachVar() {
  std::map<std::string, int> var_values;
  std::map<int, int> values;
  std::vector<bool>* example = getAnAcceptingWord();

  // Reads from most significant bits

  // first read the sign bit
  auto rit = example->rbegin();
  for (int var_index = num_of_variables - 1; var_index >= num_of_variables; var_index--) {
    if (*rit) {
      values[var_index] = -1;
    } else {
      values[var_index] = 0;
    }
    rit++;
  }

  // read value bits
  for (int var_index = num_of_variables - 1; rit != example->rend(); rit++) {
    values[var_index] <<= 1;
    values[var_index] |= (*rit);
    var_index--;

    if (var_index == -1) {
      var_index = num_of_variables - 1;
    }
  }

  int bdd_index;
  std::string var_name;
  for (auto& var_entry : formula->getCoefficientIndexMap()) {
    var_name = var_entry.first;
    bdd_index = getBddVarIndex(var_name);
    if (var_name.length() > 10) {
      var_name = var_name.substr(0, 10);
    }

    var_values[var_name] = values[bdd_index];
  }

  return var_values;
}

std::string BinaryIntAutomaton::count(double bound, bool count_less_than_or_equal_to_bound) {
  std::stringstream cmd;
  std::string result;
  std::string tmp_result_file = Option::Theory::TMP_PATH + "/arith_result.dot";
  std::string math_script_path = Option::Theory::SCRIPT_PATH + "/count.m";

  std::ofstream outfile(tmp_result_file.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << tmp_result_file << std::endl;
    exit(2);
  }

  this->toDot(outfile, false);


  cmd << "math -script " << math_script_path << " " << tmp_result_file << " ";

  if (std::floor(bound) == bound) {
    cmd << static_cast<int>(bound);
  } else {
    cmd << bound;
  }

  try {
    DVLOG(VLOG_LEVEL) << "run_cmd(`" << cmd.str() << "`)";
    result = Util::Cmd::run_cmd(cmd.str());
  } catch (std::string& e) {
    LOG(ERROR) << e;
  }

  return result;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeGraterThanOrEqualToZero(std::vector<int> indexes, int number_of_variables) {
  BinaryIntAutomaton_ptr postivie_numbers_auto = nullptr;
  DFA_ptr positive_numbers_dfa = nullptr;
  int* bin_variable_indices = getIndices(number_of_variables);
  int number_of_states = 3;
  std::array<char, 3> statuses {'-', '+', '-'};
  std::vector<char> exception;

  for (int i = 0; i < number_of_variables; i++) {
    exception.push_back('X');
  }
  exception.push_back('\0');

  dfaSetup(3, number_of_variables, bin_variable_indices);
  dfaAllocExceptions(1);
  for(int i : indexes) {
    exception[i] = '0';
  }
  dfaStoreException(1, &*exception.begin());
  dfaStoreState(0);

  dfaAllocExceptions(1);
  for(int i : indexes) {
    exception[i] = '1';
  }
  dfaStoreException(0, &*exception.begin());
  dfaStoreState(1);

  dfaAllocExceptions(0);
  dfaStoreState(2);

  positive_numbers_dfa = dfaBuild(&*statuses.begin());
  postivie_numbers_auto = new BinaryIntAutomaton(positive_numbers_dfa, number_of_variables);

  delete[] bin_variable_indices;

  DVLOG(VLOG_LEVEL) << postivie_numbers_auto->id << " = [BinaryIntAutomaton]->makeGraterThanOrEqualToZero(<indexes>, " << number_of_variables << ")";
  return postivie_numbers_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeEquality(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr equality_auto = nullptr;
  DFA_ptr equality_dfa = nullptr, tmp_dfa = nullptr;

  if ( not formula->simplify() ) {
    equality_auto = BinaryIntAutomaton::makePhi(formula);
    DVLOG(VLOG_LEVEL) << equality_auto->id << " = makeEquality(" << *formula << ")";
    return equality_auto;
  }

  int min = 0, max = 0, num_of_states, next_index, next_label, result, target;
  unsigned long transitions;
  const int constant = formula->getConstant();
  const int num_of_variables = formula->getCoefficients().size();
  int* indices = getIndices(num_of_variables);
  char *statuses = nullptr;
  std::map<int , StateIndices> carry_map; // maps carries to state indices

  for (int& c : formula->getCoefficients()) {
    if (c > 0) {
      max += c;
    } else {
      min += c;
    }
  }

  if ( max < constant) {
    max = constant;
  } else if (min > constant) {
    min = constant;
  }

  num_of_states = 2 * max - 2 * min + 3;
  statuses = new char[num_of_states + 1];

  for (int i = min; i < max + 1; i++) {
    carry_map[i].s = 0;
    carry_map[i].sr = 0;
    carry_map[i].i = -1;
    carry_map[i].ir = -1;
  }

  carry_map[constant].sr = 1;
  next_index = 0;
  next_label = constant;
  carry_map[constant].i = -1;
  carry_map[constant].ir = 0;



  transitions = 1 << num_of_variables; //number of transitions from each state

  dfaSetup(num_of_states, num_of_variables, indices);

  int count = 0;
  while (next_label < max + 1) { //there is a state to expand (excuding sink)
    if (carry_map[next_label].i == count) {
      carry_map[next_label].s = 2;
    } else {
      carry_map[next_label].sr = 2;
    }

    dfaAllocExceptions(transitions / 2);

    for (unsigned long j = 0; j < transitions; j++) {
      result = next_label + formula->countOnes(j);
      if ( not (result & 1) ) {
        target = result / 2;
        if (target == next_label) {
          if (carry_map[target].s == 0) {
            carry_map[target].s = 1;
            next_index++;
            carry_map[target].i = next_index;
          }
          dfaStoreException(carry_map[target].i, binaryFormat(j, num_of_variables));
        } else {
          if (carry_map[target].sr == 0) {
            carry_map[target].sr = 1;
            next_index++;
            carry_map[target].ir = next_index;
          }
          dfaStoreException(carry_map[target].ir, binaryFormat(j, num_of_variables));
        }
      }
    }

    dfaStoreState(num_of_states - 1);

    count++;

    //find next state to expand
    for (next_label = min; (next_label <= max) and
        (carry_map[next_label].i != count) and
        (carry_map[next_label].ir != count); next_label++) { }

  }

  for (; count < num_of_states; count++) {
    dfaAllocExceptions(0);
    dfaStoreState(num_of_states - 1);
  }

  //define accepting and rejecting states

  for (int i = 0; i < num_of_states; i++) {
    statuses[i] = '-';
  }

  for (next_label = min; next_label <= max; next_label++) {
    if (carry_map[next_label].s == 2) {
      statuses[carry_map[next_label].i] = '+';
    }
  }
  statuses[num_of_states] = '\0';

  tmp_dfa = dfaBuild(statuses);
  equality_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);
  delete[] indices;

  equality_auto = new BinaryIntAutomaton(equality_dfa, num_of_variables);
  equality_auto->setFormula(formula);

  DVLOG(VLOG_LEVEL) << equality_auto->id << " = makeEquality(" << *formula << ")";

  return equality_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeNotEquality(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr not_equal_auto = nullptr, tmp_auto = nullptr;

  formula->setType(ArithmeticFormula::Type::EQ);
  tmp_auto = BinaryIntAutomaton::makeEquality(formula);
  not_equal_auto = tmp_auto->complement();
  delete tmp_auto; tmp_auto = nullptr;

  DVLOG(VLOG_LEVEL) << not_equal_auto->id << " = makeNotEquality(" << *not_equal_auto->getFormula() << ")";
  return not_equal_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeLessThan(ArithmeticFormula_ptr formula) {
  formula->simplify();

  int min = 0, max = 0;
  for (int& c : formula->getCoefficients()) {
    if (c > 0) {
     max += c;
    } else {
     min += c;
    }
  }

  const int constant = formula->getConstant();
  if ( max < constant) {
   max = constant;
  } else if (min > constant) {
   min = constant;
  }

  const int num_of_variables = formula->getCoefficients().size();
  int num_of_states = 2 * (max - min + 1);
  int* indices = getIndices(num_of_variables);
  dfaSetup(num_of_states, num_of_variables, indices);
  delete[] indices;

  int next_index = 0, next_label = constant, result, target;
  int write1, label1, label2;
  std::unordered_map<int, StateIndices> carry_map; // maps carries to state indices

  carry_map[constant].sr = 1;
  carry_map[constant].i = -1;
  carry_map[constant].ir = 0;

  CHECK_LT(num_of_variables, 64);
  unsigned long transitions = 1 << num_of_variables; //number of transitions from each state
  int count = 0;
  while (next_label < max + 1) { //there is a state to expand (excuding sink)
   if (carry_map[next_label].i == count) {
     carry_map[next_label].s = 2;
   } else {
     carry_map[next_label].sr = 2;
   }

   // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
   dfaAllocExceptions(transitions);

   for (unsigned long j = 0; j < transitions; j++) {
     int num_of_ones = formula->countOnes(j);
     result = next_label + num_of_ones;

     if (result >= 0) {
       target = result / 2;
     } else {
       target = (result - 1) / 2;
     }

     write1 = result & 1;
     label1 = next_label;
     label2 = target;

     while (label1 != label2) {
       label1 = label2;
       result = label1 + num_of_ones;
       if (result >= 0) {
         label2 = result / 2;
       } else {
         label2 = (result - 1) / 2;
       }
       write1 = result & 1;
     }

     if (write1) {
       if (carry_map[target].s == 0) {
         carry_map[target].s = 1;
         next_index++;
         carry_map[target].i = next_index;
       }
//       std::cout << count << " -> " << carry_map[target].i << " : " << &*getBinaryFormat(j, num_of_variables).begin() << std::endl;
       dfaStoreException(carry_map[target].i, &*(getBinaryFormat(j, num_of_variables)).begin());
     } else {
       if (carry_map[target].sr == 0) {
         carry_map[target].sr = 1;
         next_index++;
         carry_map[target].ir = next_index;
       }
//       std::cout << count << " -> " << carry_map[target].i << " : " << &*getBinaryFormat(j, num_of_variables).begin() << std::endl;
       dfaStoreException(carry_map[target].ir, &*(getBinaryFormat(j, num_of_variables)).begin());
     }
   }

   dfaStoreState(count);

   count++;

   //find next state to expand
   for (next_label = min; (next_label <= max) and
       (carry_map[next_label].i != count) and
       (carry_map[next_label].ir != count); next_label++) { }

  }

  for (int i = count; i < num_of_states; i++) {
   dfaAllocExceptions(0);
   dfaStoreState(i);
  }

  //define accepting and rejecting states
  char *statuses = new char[num_of_states + 1];
  for (int i = 0; i < num_of_states; i++) {
   statuses[i] = '-';
  }

  for (next_label = min; next_label <= max; next_label++) {
   if (carry_map[next_label].s == 2) {
     statuses[carry_map[next_label].i] = '+';
   }
  }
  statuses[num_of_states] = '\0';

  DFA_ptr tmp_dfa = dfaBuild(statuses);
  tmp_dfa->ns = tmp_dfa->ns - (num_of_states - count);
  DFA_ptr less_than_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);

  BinaryIntAutomaton_ptr less_than_auto = new BinaryIntAutomaton(less_than_dfa, num_of_variables);
  less_than_auto->setFormula(formula);

  DVLOG(VLOG_LEVEL) << less_than_auto->id << " = makeLessThan(" << *formula << ")";

  return less_than_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeLessThanOrEqual(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr less_than_or_equal_auto = nullptr;

  ArithmeticFormula_ptr less_than_formula = formula->clone();
  less_than_formula->setConstant(less_than_formula->getConstant() - 1);
  less_than_formula->setType(ArithmeticFormula::Type::LT);

  less_than_or_equal_auto = BinaryIntAutomaton::makeLessThan(less_than_formula);
  less_than_or_equal_auto->setFormula(formula);
  delete less_than_formula;

  DVLOG(VLOG_LEVEL) << less_than_or_equal_auto->id << " = makeLessThanOrEqual(" << *formula << ")";

  return less_than_or_equal_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeGreaterThan(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr greater_than_auto = nullptr;

  ArithmeticFormula_ptr less_than_formula = formula->multiply(-1);
  less_than_formula->setType(ArithmeticFormula::Type::LT);

  greater_than_auto = BinaryIntAutomaton::makeLessThan(less_than_formula);
  greater_than_auto->setFormula(formula);
  delete less_than_formula;

  DVLOG(VLOG_LEVEL) << greater_than_auto->id << " = makeGreaterThan(" << *formula << ")";

  return greater_than_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeGreaterThanOrEqual(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr greater_than_or_equal_auto = nullptr;

  ArithmeticFormula_ptr less_than_formula = formula->multiply(-1);
  less_than_formula->setConstant(less_than_formula->getConstant() - 1);
  less_than_formula->setType(ArithmeticFormula::Type::LT);

  greater_than_or_equal_auto = BinaryIntAutomaton::makeLessThan(less_than_formula);
  greater_than_or_equal_auto->setFormula(formula);
  delete less_than_formula;

  DVLOG(VLOG_LEVEL) << greater_than_or_equal_auto->id << " = makeGreaterThanOrEqual(" << *formula << ")";

  return greater_than_or_equal_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeTrimHelperAuto(int var_index, int number_of_variables) {
  BinaryIntAutomaton_ptr trim_helper_auto = nullptr;
  DFA_ptr trim_helper_dfa = nullptr;
  int* indices = getIndices(number_of_variables);
  int number_of_states = 5;
  char statuses[5] = {'-', '+', '+', '-', '-'};
  char* exception = new char[number_of_variables + 1];
  for (int i = 0; i < number_of_variables; i++) {
    exception[i] = 'X';
  }
  exception[number_of_variables] = '\0';

  dfaSetup(number_of_states, number_of_variables, indices);
  // state 0
  dfaAllocExceptions(2);
  exception[var_index] = '0';
  dfaStoreException(1, exception);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(0);
  // state 1
  dfaAllocExceptions(2);
  exception[var_index] = '0';
  dfaStoreException(3, exception);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(1);
  // state 2
  dfaAllocExceptions(1);
  exception[var_index] = '0';
  dfaStoreException(4, exception);
  dfaStoreState(2);
  // state 3
  dfaAllocExceptions(1);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(3);
  // state 4
  dfaAllocExceptions(1);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(4);

  trim_helper_dfa = dfaBuild(statuses);
  trim_helper_auto = new BinaryIntAutomaton(trim_helper_dfa, number_of_variables);

  delete[] indices;
  delete[] exception;

  DVLOG(VLOG_LEVEL) << trim_helper_auto->id << " = [BinaryIntAutomaton]->makeTrimHelperAuto(" << var_index << ", " << number_of_variables << ")";
  return trim_helper_auto;
}

void BinaryIntAutomaton::compute_binary_states(std::vector<BinaryState_ptr>& binary_states,
        SemilinearSet_ptr semilinear_set) {
  if (semilinear_set->getPeriod() == 0) {
    add_binary_state(binary_states, semilinear_set->getConstants());
  } else {
    add_binary_state(binary_states, semilinear_set->getCycleHead(), semilinear_set->getPeriod(), BinaryState::Type::VAL, -1, -1);
  }
}

/**
 * works for positive numbers for now
 */
void BinaryIntAutomaton::add_binary_state(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants) {
  std::map<std::pair<int, int>, int> binary_state_map;

  binary_states.push_back(new BinaryState(-1, 0));
  binary_state_map.insert(std::make_pair(std::make_pair(-1, 0), 0));

  for (auto value : constants) {
    CHECK_GE(value, 0)<< "works for positive numbers only";
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
}

int BinaryIntAutomaton::add_binary_state(std::vector<BinaryState_ptr>& binary_states,
        int C, int R, BinaryState::Type t, int v, int b) {
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

bool BinaryIntAutomaton::is_accepting_binary_state(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set) {
  if (BinaryState::Type::VAL == binary_state->getType()) {
    for (auto i : semilinear_set->getConstants()) {
      if (i == binary_state->getV()) {
        return true;
      }
    }
  } else if (BinaryState::Type::REMT == binary_state->getType()) {
    for (auto i : semilinear_set->getPeriodicConstants()) {
      if ( ((i + semilinear_set->getCycleHead()) % (semilinear_set->getPeriod())) == binary_state->getV() ) {
        return true;
      }
    }
  }
  return false;
}

bool BinaryIntAutomaton::getCycleStatus(std::map<int, bool>& cycle_status) {
  std::map<int, int> disc;
  std::map<int, int> low;
  std::map<int, bool> is_stack_member;
  std::vector<int> st;
  std::vector<bool> path;
  int time = 0;
  int sink_state = getSinkState();

  disc[sink_state] = 0; // avoid exploring sink state
  is_stack_member[sink_state] = false; // avoid looping to sink state
  cycle_status[sink_state] = true;
  getCycleStatus(this->dfa->s, disc, low, st, is_stack_member, cycle_status, time);
  DVLOG(VLOG_LEVEL) << cycle_status[-2] << " = [" << this->id << "]->getCycleStatus(<constants>)";
  return cycle_status[-2]; // -2 is to keep if it is cyclic at all or not
}

void BinaryIntAutomaton::getCycleStatus(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
          std::map<int, bool>& is_stack_member, std::map<int, bool>& cycle_status, int& time) {
  int next_state = 0;
  std::vector<char> exception = {'0'};
  int l, r;
//  std::cout << "visiting: " << state << std::endl;
  disc[state] = low[state] = time; time++;
  st.push_back(state);
  is_stack_member[state] = true;

  l = getNextState(state, exception);
  exception[0] = '1';
  r = getNextState(state, exception);

  for (int b = 0; b < 2; b++) {
    next_state = (b == 0) ? l : r;
    if (disc.find(next_state) == disc.end()) {
      getCycleStatus(next_state, disc, low, st, is_stack_member, cycle_status, time);
      low[state] = std::min(low[state], low[next_state]);
    } else if (is_stack_member[next_state]) {
      low[state] = std::min(low[state], disc[next_state]);
    }

  }

  if (low[state] == disc[state]) { // head of SCC
    int current_state = st.back();

    while (current_state != state) {
      st.pop_back();
      is_stack_member[current_state] = false;
      cycle_status[current_state] = true;
      cycle_status[-2] = true;
      current_state = st.back();
    }

    is_stack_member[current_state] = false;
    st.pop_back();

    if (current_state == l or current_state == r) {
      cycle_status[current_state] = true;
      cycle_status[-2] = true;
    }
  }

  return;
}

void BinaryIntAutomaton::getConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants) {
  std::vector<bool> path;

  // current state cannot be accepting in binary automaton
  if ((not isSinkState(this->dfa->s)) and (not cycle_status[this->dfa->s])) {
    getConstants(this->dfa->s, cycle_status, path, constants);
  }

  DVLOG(VLOG_LEVEL) << "<void> = [" << this->id << "]->getConstants(<cycle status>, <constants>)";
  return;
}

void BinaryIntAutomaton::getConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path, std::vector<int>& constants) {
  int next_state = 0;
  std::vector<char> exception = {'0'};
  int l, r;

  if (path.size() > 31) { // limit samples to integer length for now
    return;
  }

  l = getNextState(state, exception);
  exception[0] = '1';
  r = getNextState(state, exception);

  for (int b = 0; b < 2; b++) {
    next_state = (b == 0) ? l : r;

    if ((not isSinkState(next_state))) {
      path.push_back( b == 1);
      if (isAcceptingState(next_state)) {
        unsigned c = 0;
        for (unsigned i = 0; i < path.size(); i++) {
          if (path[i]) {
            c += (1 << i);
          }
        }
        constants.push_back(c);
      }
      if (not cycle_status[next_state]) { // if next state is not in a cycle continue exploration
        getConstants(next_state, cycle_status, path, constants);
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
//bool BinaryIntAutomaton::getConstants(std::vector<int>& constants) {
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
//bool BinaryIntAutomaton::getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
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

void BinaryIntAutomaton::getBaseConstants(std::vector<int>& constants, unsigned max_number_of_bit_limit) {
  unsigned char *is_visited = new unsigned char[this->dfa->ns];
  std::vector<bool> path;

  for (int i = 0; i < this->dfa->ns; i++) {
    is_visited[i] = false;
  }

  if (not isSinkState(this->dfa->s)) {
    getBaseConstants(this->dfa->s, is_visited, path, constants, max_number_of_bit_limit);
  }

  delete[] is_visited;

  DVLOG(VLOG_LEVEL) << "<void> = [" << this->id << "]->getBaseConstants(<base constants>)";

  return;
}

/**
 * @param is_visited to keep track of visited transition; 1st is for '0' transition, 2nd bit is for '1' transition
 * @returns populated constants, ignores the value of initial state whether is an accepted or not
 */
void BinaryIntAutomaton::getBaseConstants(int state, unsigned char *is_visited, std::vector<bool>& path, std::vector<int>& constants, unsigned max_number_of_bit_limit) {
  int next_state = 0;
  std::vector<char> exception = {'0'};

  if (path.size() > max_number_of_bit_limit) { // limit samples to integer length for now
    return;
  }

  if (isAcceptingState(state)) {
    unsigned c = 0;
    for (unsigned i = 0; i < path.size(); i++) {
      if (path[i]) {
        c += (1 << i);
      }
    }
    constants.push_back(c);
  }

  next_state = getNextState(state, exception); // taking transition 0

  if ( (is_visited[state] & 1) == 0 and (not isSinkState(next_state)) ) {
    is_visited[state] |= 1;
    path.push_back(false);
    getBaseConstants(next_state, is_visited, path, constants, max_number_of_bit_limit);
    path.pop_back();
    is_visited[state] &= 2;
  }

  exception[0] = '1';
  next_state = getNextState(state, exception); // taking transition 1

  if ( (is_visited[state] & 2) == 0  and (not isSinkState(next_state)) ) {
    is_visited[state] |= 2;
    path.push_back(true);
    getBaseConstants(next_state, is_visited, path, constants, max_number_of_bit_limit);
    path.pop_back();
    is_visited[state] &= 1;
  }
}

//void BinaryIntAutomaton::getBaseConstants2(std::vector<int>& constants) {
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
//void BinaryIntAutomaton::getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants) {
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

} /* namespace Theory */
} /* namespace Vlab */
