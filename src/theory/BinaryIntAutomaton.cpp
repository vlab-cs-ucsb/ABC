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
     Automaton(other), formula (other.formula->clone()) {

}

BinaryIntAutomaton::~BinaryIntAutomaton() {
  delete formula;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::clone() const {
  BinaryIntAutomaton_ptr cloned_auto = new BinaryIntAutomaton(*this);
  DVLOG(VLOG_LEVEL) << cloned_auto->id << " = [" << this->id << "]->clone()";
  return cloned_auto;
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
      break;
    }
    case ArithmeticFormula::Type::GE: {
      break;
    }
    case ArithmeticFormula::Type::LT: {
      result_auto = BinaryIntAutomaton::makeLessThan(formula);
      break;
    }
    case ArithmeticFormula::Type::LE: {
      break;
    }
    default:
      break;
  }

  return result_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::complement() {
  BinaryIntAutomaton_ptr complement_auto = nullptr;
  DFA_ptr complement_dfa = dfaCopy(this->dfa);

  dfaNegation(complement_dfa);

  complement_auto = new BinaryIntAutomaton(complement_dfa, num_of_variables);
  complement_auto->setFormula(this->formula->negate());

  DVLOG(VLOG_LEVEL) << complement_auto->id << " = [" << this->id << "]->complement()";

  return complement_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::intersect(BinaryIntAutomaton_ptr other_auto) {
  DFA_ptr intersect_dfa = nullptr, minimized_dfa = nullptr;
  BinaryIntAutomaton_ptr intersect_auto = nullptr;

  if (not formula->isVariableOrderingSame(other_auto->formula)) {
    LOG(FATAL)<< "You cannot intersect binary automata with different variable orderings";
  }

  intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaAND);
  minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
  intersect_dfa = nullptr;

  intersect_auto = new BinaryIntAutomaton(minimized_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << intersect_auto->id << " = [" << this->id << "]->intersect(" << other_auto->id << ")";

  return intersect_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::union_(BinaryIntAutomaton_ptr other_auto) {
  DFA_ptr union_dfa = nullptr, minimized_dfa = nullptr;
  BinaryIntAutomaton_ptr union_auto = nullptr;

  if (not formula->isVariableOrderingSame(other_auto->formula)) {
    LOG(FATAL)<< "You cannot union binary automata with different variable orderings";
  }

  union_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaOR);
  minimized_dfa = dfaMinimize(union_dfa);
  dfaFree(union_dfa);
  union_dfa = nullptr;

  union_auto = new BinaryIntAutomaton(minimized_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << union_auto->id << " = [" << this->id << "]->union(" << other_auto->id << ")";

  return union_auto;
}

void BinaryIntAutomaton::setFormula(ArithmeticFormula_ptr formula) {
  this->formula = formula;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeEquality(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr equality_auto = nullptr;
  DFA_ptr equality_dfa = nullptr, tmp_dfa = nullptr;

  if ( not formula->optimize() ) {
    equality_dfa = dfaFalse();
    equality_auto = new BinaryIntAutomaton(equality_dfa, 0);
    equality_auto->setFormula(formula);
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
  delete[] indices;
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

  equality_auto = new BinaryIntAutomaton(equality_dfa, num_of_variables);
  equality_auto->setFormula(formula);

  DVLOG(VLOG_LEVEL) << equality_auto->id << " = makeEquality(" << *formula << ")";

  return equality_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeNotEquality(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr not_equal_auto = nullptr, tmp_auto = nullptr;

  tmp_auto = BinaryIntAutomaton::makeEquality(formula);
  not_equal_auto = tmp_auto->complement();
  delete tmp_auto; tmp_auto = nullptr;

  DVLOG(VLOG_LEVEL) << not_equal_auto->id << " = makeNotEquality(" << *formula << ")";

  return not_equal_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::makeLessThan(ArithmeticFormula_ptr formula) {
  BinaryIntAutomaton_ptr less_than_auto = nullptr;
  DFA_ptr less_than_dfa = nullptr, tmp_dfa = nullptr;

  formula->optimize();

  std::cout << "optimized: " << *formula << std::endl;

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


} /* namespace Theory */
} /* namespace Vlab */
