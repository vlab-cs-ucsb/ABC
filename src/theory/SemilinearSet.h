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

#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "../utils/List.h"
#include "../utils/Math.h"

namespace Vlab {
namespace Theory {

class SemilinearSet;
typedef SemilinearSet* SemilinearSet_ptr;

class SemilinearSet {
public:
  SemilinearSet();
  SemilinearSet(SemilinearSet& other);
  virtual ~SemilinearSet();

  SemilinearSet_ptr clone();
  std::string str() const;

  int get_cycle_head();
  void set_cycle_head(int value);
  int get_period();
  void set_period(int value);
  std::vector<int>& get_constants();
  void set_constants(std::vector<int>& constants);
  std::vector<int>& get_periodic_constants();
  void set_periodic_constants(std::vector<int>& periodic_constants);
  void add_constant(int value);
  void add_periodic_constant(int value);
  int get_number_of_constants();
  int get_number_of_periodic_constants();
  SemilinearSet_ptr Merge(SemilinearSet_ptr other);
  bool is_empty_set();
  bool has_only_constants();
  bool has_constants();
  void clear();

  friend std::ostream& operator<<(std::ostream& os, const SemilinearSet& semilinear_set);
protected:
  int C;
  int R;

  std::vector<int> constants;
  std::vector<int> periodic_constants;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_SEMILINEARSET_H_ */
