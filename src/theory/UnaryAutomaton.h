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
#include "SemilinearSet.h"
#include "BinaryState.h"
#include "ArithmeticFormula.h"

namespace Vlab {
namespace Theory {

class UnaryAutomaton;
typedef UnaryAutomaton* UnaryAutomaton_ptr;

class IntAutomaton;
typedef IntAutomaton* IntAutomaton_ptr;

class BinaryIntAutomaton;
typedef BinaryIntAutomaton* BinaryIntAutomaton_ptr;

class UnaryAutomaton: public Automaton {
public:
  UnaryAutomaton(DFA_ptr);
  UnaryAutomaton(const UnaryAutomaton&);
  virtual ~UnaryAutomaton();

  virtual UnaryAutomaton_ptr clone() const;

  static UnaryAutomaton_ptr makePhi();
  static UnaryAutomaton_ptr makeAutomaton(SemilinearSet_ptr semilinear_set);

  SemilinearSet_ptr getSemilinearSet();
  IntAutomaton_ptr toIntAutomaton(int number_of_variables, bool add_minus_one = false);
  BinaryIntAutomaton_ptr toBinaryIntAutomaton(std::string var_name, ArithmeticFormula_ptr formula, bool add_minus_one = false);

protected:

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_UNARYAUTOMATON_H_ */
