/*
 * BinaryIntAutomaton.h
 *
 *  Created on: Oct 16, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_BINARYINTAUTOMATON_H_
#define THEORY_BINARYINTAUTOMATON_H_

#include <algorithm>
#include <map>
#include <stack>
#include <vector>
#include <array>

#include "utils/Math.h"
#include "utils/List.h"
#include "Automaton.h"
#include "UnaryAutomaton.h"
#include "ArithmeticFormula.h"
#include "SemilinearSet.h"
#include "BinaryState.h"

namespace Vlab {
namespace Theory {

class BinaryIntAutomaton;
typedef BinaryIntAutomaton* BinaryIntAutomaton_ptr;

class BinaryIntAutomaton: public Automaton {
public:

  BinaryIntAutomaton();
  BinaryIntAutomaton(DFA_ptr, int num_of_variables);
  BinaryIntAutomaton(const BinaryIntAutomaton&);
  virtual ~BinaryIntAutomaton();

  virtual BinaryIntAutomaton_ptr clone() const;

  static BinaryIntAutomaton_ptr makePhi(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr);

  static BinaryIntAutomaton_ptr makeAutomaton(SemilinearSet_ptr semilinear_set, std::string var_name,
          ArithmeticFormula_ptr formula, bool add_leading_zeros = false);


  ArithmeticFormula_ptr getFormula();
  void setFormula(ArithmeticFormula_ptr formula);
  bool hasNegative1();
  BinaryIntAutomaton_ptr complement();
  BinaryIntAutomaton_ptr intersect(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr union_(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr difference(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr exists(std::string var_name);
  BinaryIntAutomaton_ptr getBinaryAutomatonFor(std::string var_name);
  BinaryIntAutomaton_ptr getPositiveValuesFor(std::string var_name);
  BinaryIntAutomaton_ptr getNegativeValuesFor(std::string var_name);
  BinaryIntAutomaton_ptr trimLeadingZeros();
  BinaryIntAutomaton_ptr addLeadingZeros();
  SemilinearSet_ptr getSemilinearSet();
  UnaryAutomaton_ptr toUnaryAutomaton();

protected:
  BinaryIntAutomaton(ArithmeticFormula_ptr formula);
  static BinaryIntAutomaton_ptr makeGraterThanOrEqualToZero(std::vector<int> indexes, int number_of_variables);
  static BinaryIntAutomaton_ptr makeEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeNotEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeLessThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeLessThanOrEqual(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeGreaterThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeGreaterThanOrEqual(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeTrimHelperAuto();
  static void compute_binary_states(std::vector<BinaryState_ptr>& binary_states,
          SemilinearSet_ptr semilinear_set);
  static void add_binary_state(std::vector<BinaryState_ptr>& binary_states,
          std::vector<int>& constants);
  static int add_binary_state(std::vector<BinaryState_ptr>& binary_states,
          int C, int R, BinaryState::Type t, int v, int b);
  static bool is_accepting_binary_state(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set);

  bool getCycleStatus(std::map<int, bool>& cycle_status);
  void getCycleStatus(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
            std::map<int, bool>& is_stack_member, std::map<int, bool>& cycle_status, int& time);
  bool getConstants(std::vector<int>& constants);
  bool getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
          std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::vector<int>& constants, int& time);
  void getConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants);
  void getConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path, std::vector<int>& constants);
  void getBaseConstants(std::vector<int>& constants);
  void getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants);

  struct StateIndices {
    // r suffixes are for the rejecting clone
    int i, ir; // state index
    int s, sr; // status: 0 not yet processed, 1 to be expanded, 2 done
  };
  ArithmeticFormula_ptr formula;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYINTAUTOMATON_H_ */
