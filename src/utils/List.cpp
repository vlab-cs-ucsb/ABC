/*
 * List.cpp
 *
 *  Created on: Nov 17, 2015
 *      Author: baki
 */

#include "List.h"

namespace Vlab {
namespace Util {
namespace List {

void sort_and_remove_duplicate (std::vector<int>& values) {
  std::sort(values.begin(), values.end());
  auto last = std::unique(values.begin(), values.end());
  values.erase(last, values.end());
}

} /* namespace List */
} /* namespace Util */
} /* namespace Vlab */
