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

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeAutomaton(std::vector<int>&constants, std::string var_name) {
  BinaryIntAutomaton_ptr constants_binary_auto = nullptr;
  ArithmeticFormula_ptr formula = nullptr;
  DFA_ptr binary_dfa = nullptr;
  int number_of_variables = 1;
  int var_index = 0;
  int number_of_binary_states;
  std::vector<BinaryState_ptr> binary_states;
  int* bin_variable_indices = getIndices(number_of_variables);
  char* statuses = nullptr;
  char* bit_transition = new char[number_of_variables + 1];

  auto get_status = [&constants] (BinaryState_ptr binary_state) {
    if (binary_state->isLeadingZeroState()) {
      return '+';
    } else if (BinaryState::Type::VAL == binary_state->getType()) {
      for (auto c : constants) {
        if (c == binary_state->getV()) {
          return '+';
        }
      }
    }
    return '-';
  };

  for (int i = 0; i < number_of_variables; i++) {
    bit_transition[i] = 'X';
  }
  bit_transition[number_of_variables] = '\0';

  add_binary_state(binary_states, constants, false);

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

    statuses[i] = get_status(binary_states[i]);
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

  delete[] statuses;
  delete[] bin_variable_indices;
  delete[] bit_transition;

  constants_binary_auto = new BinaryIntAutomaton(dfaMinimize(binary_dfa), number_of_variables);
  delete binary_dfa; binary_dfa = nullptr;
  formula = new ArithmeticFormula();
  formula->setVariableCoefficient(var_name, 1);
  constants_binary_auto->setFormula(formula);

  DVLOG(VLOG_LEVEL) << constants_binary_auto->id << " = makeAutomaton(<constants>, " << var_name << ")";

  return constants_binary_auto;
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
  // bdd vars are ordered in the reverse order of coefficients
  int bdd_var_index = num_of_variables - formula->getVariableIndex(var_name) - 1;

  for (int i = num_of_variables - 1 ; i >= 0; i--) {
    if (i != bdd_var_index) {
      tmp_dfa = single_var_dfa;
//      dfaRightQuotient(tmp_dfa, (unsigned)i);
      single_var_dfa = dfaProject(tmp_dfa, (unsigned)i);
      dfaFree(tmp_dfa);
      tmp_dfa = single_var_dfa;
//      dfaPrefixClose(tmp_dfa);
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

  BinaryIntAutomaton_ptr trimmed_auto = nullptr, tmp_auto = this->clone(),
          trim_helper_auto = nullptr;
  DFA_ptr tmp_dfa = nullptr;
  std::vector<char> exception = {'0'};
  int next_state = -1;

  for (int i = 0; i < tmp_auto->dfa->ns; i++) {
    if (i != tmp_auto->dfa->s) {
      next_state = getNextState(i, exception);
      if (isAcceptingState(next_state)) {
        tmp_auto->dfa->f[i] = 1;
      }
    }
  }

  trim_helper_auto = BinaryIntAutomaton::makeTrimHelperAuto();
  trim_helper_auto->setFormula(tmp_auto->formula->clone());

  trimmed_auto = tmp_auto->intersect(trim_helper_auto);
  delete tmp_auto; tmp_auto = nullptr;
  delete trim_helper_auto; trim_helper_auto = nullptr;

  DVLOG(VLOG_LEVEL) << trimmed_auto->id << " = [" << this->id << "]->trimLeadingZeros()";
  return trimmed_auto;
}

SemilinearSet_ptr BinaryIntAutomaton::getSemilinearSet() {
  SemilinearSet_ptr semilinear_set = nullptr;
  BinaryIntAutomaton_ptr subject_auto = nullptr, tmp_auto = nullptr;
  int current_state = this->dfa->s,
          sink_state = this->getSinkState();

  std::vector<int> constants = getBaseConstants(true);

  std::sort(constants.begin(), constants.end());
  auto last1 = std::unique(constants.begin(), constants.end());
  constants.erase(last1, constants.end());

  if (0 < constants.size()) {
    std::string var_name = this->formula->getCoefficientIndexMap().begin()->first;
    tmp_auto = BinaryIntAutomaton::makeAutomaton(constants, var_name);
    tmp_auto->inspectAuto();
    subject_auto = this->difference(tmp_auto);
  }
// TODO baki loop here
  std::vector<int> bases = subject_auto->getBaseConstants();

  std::sort(bases.begin(), bases.end());
  auto last2 = std::unique(bases.begin(), bases.end());
  bases.erase(last2, bases.end());

  std::cout << "bases: ";
  for (int i : bases) {
    std::cout << i << " ";
  }
  std::cout << std::endl;

  DVLOG(VLOG_LEVEL) << "semilinear set = [" << this->id << "]->getSemilinearSet()";

  return semilinear_set;
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
  BinaryIntAutomaton_ptr less_than_auto = nullptr;
  DFA_ptr less_than_dfa = nullptr, tmp_dfa = nullptr;

  formula->simplify();

  int min = 0, max = 0, num_of_states, next_index, next_label, result, target;
  int write1, label1, label2;
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

  num_of_states = 2 * (max - min + 1);
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
  delete[] indices;
  int count = 0;
  while (next_label < max + 1) { //there is a state to expand (excuding sink)
   if (carry_map[next_label].i == count) {
     carry_map[next_label].s = 2;
   } else {
     carry_map[next_label].sr = 2;
   }

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
  tmp_dfa->ns = tmp_dfa->ns - (num_of_states - count);
  less_than_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);

  less_than_auto = new BinaryIntAutomaton(less_than_dfa, num_of_variables);
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

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeTrimHelperAuto() {
  BinaryIntAutomaton_ptr trim_helper_auto = nullptr;
  DFA_ptr trim_helper_dfa = nullptr;
  int number_of_variables = 1;
  int* bin_variable_indices = getIndices(number_of_variables);
  int number_of_states = 5;
  std::array<char, 5> statuses {'-', '+', '+', '-', '-'};
  std::vector<char> exception;

  exception.push_back('X');
  exception.push_back('\0');

  dfaSetup(number_of_states, number_of_variables, bin_variable_indices);
  // state 0
  dfaAllocExceptions(2);
  exception[0] = '0';
  dfaStoreException(1, &*exception.begin());
  exception[0] = '1';
  dfaStoreException(2, &*exception.begin());
  dfaStoreState(0);
  // state 1
  dfaAllocExceptions(2);
  exception[0] = '0';
  dfaStoreException(3, &*exception.begin());
  exception[0] = '1';
  dfaStoreException(2, &*exception.begin());
  dfaStoreState(1);
  // state 2
  dfaAllocExceptions(1);
  exception[0] = '0';
  dfaStoreException(4, &*exception.begin());
  dfaStoreState(2);
  // state 3
  dfaAllocExceptions(1);
  exception[0] = '1';
  dfaStoreException(2, &*exception.begin());
  dfaStoreState(3);
  // state 4
  dfaAllocExceptions(1);
  exception[0] = '1';
  dfaStoreException(2, &*exception.begin());
  dfaStoreState(4);

  trim_helper_dfa = dfaBuild(&*statuses.begin());
  trim_helper_auto = new BinaryIntAutomaton(trim_helper_dfa, number_of_variables);

  delete[] bin_variable_indices;

  DVLOG(VLOG_LEVEL) << trim_helper_auto->id << " = [BinaryIntAutomaton]->makeTrimHelperAuto()";
  return trim_helper_auto;
}

/**
 * works for positive numbers for now
 */
void BinaryIntAutomaton::add_binary_state(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants, bool add_leading_zeros) {

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

  if (add_leading_zeros) {
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
}

std::vector<int> BinaryIntAutomaton::getBaseConstants(bool only_non_periodic_constants) {
  bool *is_stack_member = new bool[this->dfa->ns];
  std::vector<bool> path;
  std::vector<int> constants;

  for (int i = 0; i < this->dfa->ns; i++) {
    is_stack_member[i] = false;
  }

  if (not isSinkState(this->dfa->s)) {
    getBaseConstants(this->dfa->s, is_stack_member, path, constants, only_non_periodic_constants);
  }

  delete[] is_stack_member;

  DVLOG(VLOG_LEVEL) << "base constants = [" << this->id << "]->getBaseConstants()";

  return constants;
}

/**
 * @returns populated constants, ignores the initial state whether is an accepted or not
 */
void BinaryIntAutomaton::getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants, bool only_non_periodic_constants) {
  is_stack_member[state] = true;

  int next_state = 0;
  char bit[2] = {'0', '1'};
  std::vector<char> exception = {'0'};
  std::vector<int> next_states;
  int l, r;
  bool is_periodic_constant = false;

  l = getNextState(state, exception);
  exception[0] = '1';
  r = getNextState(state, exception);

  is_periodic_constant = (is_stack_member[l] || is_stack_member[r]);

  if (only_non_periodic_constants and is_periodic_constant) { // it will skip the exploration of the rest because of cycle
    return;
  }

  for (int b = 0; b < 2; b++) {
    next_state = (b == 0) ? l : r;

    if ((not is_stack_member[next_state]) and (not isSinkState(next_state))) {
      path.push_back( b == 1);

      if (isAcceptingState(next_state)) {
        int c = 0;
        for (unsigned i = 0; i < path.size(); i++) {
          if (path[i]) {
            c += (1 << i);
          }
        }
        constants.push_back(c);
      }

      getBaseConstants(next_state, is_stack_member, path, constants, only_non_periodic_constants);
      path.pop_back();
    }
  }
  is_stack_member[state] = false;
}




} /* namespace Theory */
} /* namespace Vlab */
