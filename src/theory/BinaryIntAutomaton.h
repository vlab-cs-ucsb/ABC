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

#include "BinaryAutomaton.h"

namespace Vlab {
namespace Theory {

class BinaryIntAutomaton: public BinaryAutomaton {
public:
  BinaryIntAutomaton();
  virtual ~BinaryIntAutomaton();
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_BINARYINTAUTOMATON_H_ */
