/*
 * UnaryAutomaton.h
 *
 *  Created on: Nov 5, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_UNARYAUTOMATON_H_
#define THEORY_UNARYAUTOMATON_H_

#include <vector>
#include <map>

#include "Automaton.h"
#include "IntAutomaton.h"
#include "BinaryIntAutomaton.h"
#include "SemilinearSet.h"
#include "BinaryState.h"

namespace Vlab {
namespace Theory {
class UnaryAutomaton;

typedef UnaryAutomaton* UnaryAutomaton_ptr;

class UnaryAutomaton: public Automaton {
public:
  UnaryAutomaton(const UnaryAutomaton&);
  virtual ~UnaryAutomaton();

  virtual UnaryAutomaton_ptr clone() const;

  static UnaryAutomaton_ptr makeAutomaton(IntAutomaton_ptr);
  static UnaryAutomaton_ptr makeAutomaton(BinaryIntAutomaton_ptr);

  SemilinearSet_ptr getSemilinearSet();
  IntAutomaton_ptr toIntAutomaton(bool add_minus_one = false);
  BinaryIntAutomaton_ptr toBinaryIntAutomaton(std::string var_name, ArithmeticFormula_ptr formula, bool add_minus_one = false);

protected:
  UnaryAutomaton(DFA_ptr);
  BinaryIntAutomaton_ptr toBinaryIntAutomaton(int var_index = 0, int number_of_variables = 1);

  void compute_binary_states(std::vector<BinaryState_ptr>& binary_states, SemilinearSet_ptr semilinear_set);
  void add_binary_state(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants);
  int add_binary_state(std::vector<BinaryState_ptr>& binary_states, int C, int R, BinaryState::Type t, int v, int b);
  char get_binary_status(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set);

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_UNARYAUTOMATON_H_ */
