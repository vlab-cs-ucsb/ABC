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

#include <iostream>
#include <iterator>
#include <map>
#include <string>
#include <queue>
#include <vector>

#include <glog/logging.h>
//#include <mona/dfa.h>

#include "ArithmeticFormula.h"
#include "Automaton.h"
#include "SemilinearSet.h"

namespace Vlab {
namespace Theory {

class UnaryAutomaton;
typedef UnaryAutomaton* UnaryAutomaton_ptr;

class IntAutomaton;
using IntAutomaton_ptr = IntAutomaton*;

class BinaryIntAutomaton;
using BinaryIntAutomaton_ptr = BinaryIntAutomaton* ;

class StringAutomaton;
using StringAutomaton_ptr = StringAutomaton*;

class UnaryAutomaton: public Automaton {
public:
  UnaryAutomaton(DFA_ptr);
  UnaryAutomaton(const UnaryAutomaton&);
  virtual ~UnaryAutomaton();

  virtual UnaryAutomaton_ptr clone() const;

  static UnaryAutomaton_ptr MakePhi();
  static UnaryAutomaton_ptr MakeAutomaton(SemilinearSet_ptr semilinear_set);

  SemilinearSet_ptr getSemilinearSet();
  IntAutomaton_ptr toIntAutomaton(int number_of_variables, bool add_minus_one = false);
  BinaryIntAutomaton_ptr toBinaryIntAutomaton(std::string var_name, ArithmeticFormula_ptr formula, bool add_minus_one = false);
  StringAutomaton_ptr toStringAutomaton();

protected:
  void decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) override;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_UNARYAUTOMATON_H_ */
