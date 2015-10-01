/*
 * IntAutomaton.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef THEORY_INTAUTOMATON_H_
#define THEORY_INTAUTOMATON_H_

#include "Automaton.h"

namespace Vlab {
namespace Theory {

class IntAutomaton;
typedef IntAutomaton* IntAutomaton_ptr;

/**
 * A compatible version with string automaton
 * (A string automaton with Sigma - {reserved words} transitions
 */
class IntAutomaton: public Automaton {
public:
  IntAutomaton(DFA_ptr);
  IntAutomaton(DFA_ptr, int num_of_variables);
  IntAutomaton(DFA_ptr, bool has_negative_1);
  IntAutomaton(DFA_ptr, bool has_negative_1, int num_of_variables);
  IntAutomaton(const IntAutomaton&);
  virtual ~IntAutomaton();

  virtual IntAutomaton_ptr clone() const;

  static IntAutomaton_ptr makePhi(int num_of_variables = IntAutomaton::DEFAULT_NUM_OF_VARIABLES,
            int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeZero(int num_of_variables = IntAutomaton::DEFAULT_NUM_OF_VARIABLES,
            int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeAnyInt(int num_of_variables = IntAutomaton::DEFAULT_NUM_OF_VARIABLES,
            int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeInt(int value, int num_of_variables =
            IntAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeIntLessThan(int value, int num_of_variables =
            IntAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeIntLessThanEqual(int value, int num_of_variables =
            IntAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeIntGreaterThan(int value, int num_of_variables =
            IntAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeIntGreaterThanEqual(int value, int num_of_variables =
            IntAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);
  static IntAutomaton_ptr makeIntRange(int start, int end, int num_of_variables =
            IntAutomaton::DEFAULT_NUM_OF_VARIABLES, int* variable_indices = IntAutomaton::DEFAULT_VARIABLE_INDICES);

  IntAutomaton_ptr complement();
  IntAutomaton_ptr union_(IntAutomaton_ptr other_auto);
  IntAutomaton_ptr intersect(IntAutomaton_ptr other_auto);
  IntAutomaton_ptr difference(IntAutomaton_ptr other_auto);

  IntAutomaton_ptr add(IntAutomaton_ptr other_auto);
  IntAutomaton_ptr concat(IntAutomaton_ptr other_auto);
  IntAutomaton_ptr substract(IntAutomaton_ptr other_auto);

  bool checkEquivalance(IntAutomaton_ptr other_auto);
  bool isEmptyLanguage();
  bool hasZero();
  bool isZero();
  bool isAcceptingSingleInt();

protected:
  bool has_negative_1;
//  bool is_only_minus_1;
  static int DEFAULT_NUM_OF_VARIABLES;
  static int* DEFAULT_VARIABLE_INDICES;
  static unsigned* DEFAULT_UNSIGNED_VARIABLE_INDICES;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_INTAUTOMATON_H_ */
