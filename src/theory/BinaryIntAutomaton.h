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
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <iterator>
#include <map>
#include <sstream>
#include <stack>
#include <string>
#include <unordered_map>
#include <utility>
#include <vector>

#include <glog/logging.h>
#include <mona/bdd.h>
#include <mona/dfa.h>

#include "../utils/Cmd.h"
#include "../utils/List.h"
#include "ArithmeticFormula.h"
#include "Automaton.h"
#include "BinaryState.h"
#include "options/Theory.h"
#include "SemilinearSet.h"
#include "UnaryAutomaton.h"

namespace Vlab {
namespace Theory {

class BinaryIntAutomaton;
typedef BinaryIntAutomaton* BinaryIntAutomaton_ptr;

class BinaryIntAutomaton: public Automaton {
public:

  BinaryIntAutomaton(bool is_natural_number);
  BinaryIntAutomaton(DFA_ptr, int num_of_variables, bool is_natural_number);
  BinaryIntAutomaton(DFA_ptr, ArithmeticFormula_ptr formula, bool is_natural_number);
  BinaryIntAutomaton(const BinaryIntAutomaton&);
  virtual ~BinaryIntAutomaton();

  virtual BinaryIntAutomaton_ptr clone() const;
  // What about natural number parameter?
  virtual BinaryIntAutomaton_ptr MakeAutomaton(DFA_ptr dfa, Formula_ptr formula, const int number_of_variables);

  static BinaryIntAutomaton_ptr MakePhi(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeAnyInt(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeAutomaton(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeAutomaton(int value, std::string var_name,
          ArithmeticFormula_ptr formula, bool add_leading_zeros = false);
  static BinaryIntAutomaton_ptr MakeAutomaton(SemilinearSet_ptr semilinear_set, std::string var_name,
          ArithmeticFormula_ptr formula, bool add_leading_zeros = false);

  ArithmeticFormula_ptr GetFormula();
  void SetFormula(ArithmeticFormula_ptr formula);
  bool is_natural_number();
  bool HasNegative1();
  BinaryIntAutomaton_ptr Complement();
  BinaryIntAutomaton_ptr Intersect(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr Union(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr Difference(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr Exists(std::string var_name);
  BinaryIntAutomaton_ptr GetBinaryAutomatonFor(std::string var_name);
  BinaryIntAutomaton_ptr GetPositiveValuesFor(std::string var_name);
  BinaryIntAutomaton_ptr GetNegativeValuesFor(std::string var_name);
  BinaryIntAutomaton_ptr TrimLeadingZeros();
  BinaryIntAutomaton_ptr AddLeadingZeros();
  SemilinearSet_ptr GetSemilinearSet();
  UnaryAutomaton_ptr ToUnaryAutomaton();

  std::map<std::string, int> GetAnAcceptingIntForEachVar();

  BigInteger SymbolicCount(double bound, bool count_less_than_or_equal_to_bound = false) override;

protected:
  BinaryIntAutomaton(ArithmeticFormula_ptr formula);
  static BinaryIntAutomaton_ptr MakeIntGraterThanOrEqualToZero(std::vector<int> indexes, int number_of_variables);
  static BinaryIntAutomaton_ptr MakeEquality(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeIntEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr MakeNaturalNumberEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr MakeLessThan(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeIntLessThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr MakeNaturalNumberLessThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr MakeLessThanOrEqual(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeGreaterThan(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeGreaterThanOrEqual(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr MakeTrimHelperAuto(int var_index, int number_of_variables);
  static void ComputeBinaryStates(std::vector<BinaryState_ptr>& binary_states,
          SemilinearSet_ptr semilinear_set);
  static void AddBinaryState(std::vector<BinaryState_ptr>& binary_states,
          std::vector<int>& constants);
  static int AddBinaryState(std::vector<BinaryState_ptr>& binary_states,
          int C, int R, BinaryState::Type t, int v, int b);
  static bool is_accepting_binary_state(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set);

  void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) override;

  bool GetCycleStatus(std::map<int, bool>& cycle_status);
  void GetCycleStatus(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
            std::map<int, bool>& is_stack_member, std::map<int, bool>& cycle_status, int& time);
//  bool getConstants(std::vector<int>& constants);
//  bool getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
//          std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::vector<int>& constants, int& time);
  void GetConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants);
  void GetConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path, std::vector<int>& constants);
  void GetBaseConstants(std::vector<int>& constants, unsigned max_number_of_bit_limit = 15);
  void GetBaseConstants(int state, unsigned char *is_visited, std::vector<bool>& path, std::vector<int>& constants, unsigned max_number_of_bit_limit);
  //  void getBaseConstants2(std::vector<int>& constants);
  //  void getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants);

  void add_print_label(std::ostream& out) override;
  struct StateIndices {
    // r suffixes are for the rejecting clone
    int i, ir; // state index
    int s, sr; // status: 0 not yet processed, 1 to be expanded, 2 done
    StateIndices(): i{-1}, ir{-1}, s{0}, sr{0} {}
  };

  bool is_natural_number_;
  ArithmeticFormula_ptr formula_;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYINTAUTOMATON_H_ */
