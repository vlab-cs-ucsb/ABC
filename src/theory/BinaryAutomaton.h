/*
 * BinaryAutomaton.h
 *
 *  Created on: Oct 16, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_BINARYAUTOMATON_H_
#define THEORY_BINARYAUTOMATON_H_

#include "Automaton.h"

namespace Vlab {
namespace Theory {

class BinaryAutomaton: public Automaton {
public:
  BinaryAutomaton(Automaton::Type type);
  virtual ~BinaryAutomaton();
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYAUTOMATON_H_ */
