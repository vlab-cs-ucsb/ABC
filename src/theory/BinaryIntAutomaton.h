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

#include <map>
#include <string>
#include <vector>

#include <boost/multiprecision/cpp_int.hpp>

#include "ArithmeticFormula.h"
#include "Automaton.h"
#include "BinaryState.h"
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
  BinaryIntAutomaton(const BinaryIntAutomaton&);
  virtual ~BinaryIntAutomaton();

  virtual BinaryIntAutomaton_ptr clone() const;

  static BinaryIntAutomaton_ptr makePhi(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeAnyInt(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeAutomaton(int value, std::string var_name,
          ArithmeticFormula_ptr formula, bool add_leading_zeros = false);
  static BinaryIntAutomaton_ptr makeAutomaton(SemilinearSet_ptr semilinear_set, std::string var_name,
          ArithmeticFormula_ptr formula, bool add_leading_zeros = false);

  ArithmeticFormula_ptr getFormula();
  void setFormula(ArithmeticFormula_ptr formula);
  bool hasNegative1();
  int getBddVarIndex(std::string var_name);
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

  std::map<std::string, int> getAnAcceptingIntForEachVar();

  boost::multiprecision::cpp_int Count(int bound, bool count_less_than_or_equal_to_bound = false, bool count_reserved_words = false) override;
  boost::multiprecision::cpp_int SymbolicCount(double bound, bool count_less_than_or_equal_to_bound = true) override;

protected:
  BinaryIntAutomaton(ArithmeticFormula_ptr formula);
  static BinaryIntAutomaton_ptr makeIntGraterThanOrEqualToZero(std::vector<int> indexes, int number_of_variables);
  static BinaryIntAutomaton_ptr makeEquality(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeIntEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeNaturalNumberEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeNotEquality(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeLessThan(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeIntLessThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeNaturalNumberLessThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeLessThanOrEqual(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeGreaterThan(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeGreaterThanOrEqual(ArithmeticFormula_ptr, bool is_natural_number);
  static BinaryIntAutomaton_ptr makeTrimHelperAuto(int var_index, int number_of_variables);
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
//  bool getConstants(std::vector<int>& constants);
//  bool getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
//          std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::vector<int>& constants, int& time);
  void getConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants);
  void getConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path, std::vector<int>& constants);
  void getBaseConstants(std::vector<int>& constants, unsigned max_number_of_bit_limit = 15);
  void getBaseConstants(int state, unsigned char *is_visited, std::vector<bool>& path, std::vector<int>& constants, unsigned max_number_of_bit_limit);
  //  void getBaseConstants2(std::vector<int>& constants);
  //  void getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants);

  struct StateIndices {
    // r suffixes are for the rejecting clone
    int i, ir; // state index
    int s, sr; // status: 0 not yet processed, 1 to be expanded, 2 done
    StateIndices(): i{-1}, ir{-1}, s{0}, sr{0} {}
  };

  bool is_natural_number;
  ArithmeticFormula_ptr formula;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYINTAUTOMATON_H_ */