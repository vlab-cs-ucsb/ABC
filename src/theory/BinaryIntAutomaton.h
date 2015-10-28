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

#include "Automaton.h"
#include "ArithmeticFormula.h"

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

  static BinaryIntAutomaton_ptr makePhi(ArithmeticFormula_ptr formula);
  static BinaryIntAutomaton_ptr makeAutomaton(ArithmeticFormula_ptr);

  ArithmeticFormula_ptr getFormula();
  void setFormula(ArithmeticFormula_ptr formula);
  BinaryIntAutomaton_ptr complement();
  BinaryIntAutomaton_ptr intersect(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr union_(BinaryIntAutomaton_ptr);
  BinaryIntAutomaton_ptr difference(BinaryIntAutomaton_ptr);


protected:
  BinaryIntAutomaton(ArithmeticFormula_ptr formula);
  static BinaryIntAutomaton_ptr makeEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeNotEquality(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeLessThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeLessThanOrEqual(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeGreaterThan(ArithmeticFormula_ptr);
  static BinaryIntAutomaton_ptr makeGreaterThanOrEqual(ArithmeticFormula_ptr);

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
