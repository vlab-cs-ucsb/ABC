/*
 * SemilinearSet.h
 *
 *  Created on: Nov 5, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef THEORY_SEMILINEARSET_H_
#define THEORY_SEMILINEARSET_H_

#include <ostream>
#include <sstream>
#include <vector>

namespace Vlab {
namespace Theory {

class SemilinearSet {
public:
  SemilinearSet();
  virtual ~SemilinearSet();

  std::string str() const;

  int getCycleHead();
  void setCycleHead(int value);
  int getPeriod();
  void setPeriod(int value);
  std::vector<int>& getConstants();
  std::vector<int>& getPeriodicConstants();
  void addConstant(int value);
  void addPeriodicConstant(int value);
  int getNumberOfConstants();
  int getNumberOfPeriodicConstants();

  friend std::ostream& operator<<(std::ostream& os, const SemilinearSet& semilinear_set);
protected:
  int C;
  int R;

  std::vector<int> constants;
  std::vector<int> periodic_constants;
};

typedef SemilinearSet* SemilinearSet_ptr;

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_SEMILINEARSET_H_ */
