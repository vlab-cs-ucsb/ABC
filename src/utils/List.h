/*
 * List.h
 *
 *  Created on: Nov 17, 2015
 *      Author: baki
 */

#ifndef SRC_UTILS_LIST_H_
#define SRC_UTILS_LIST_H_

#include <vector>
#include <set>
#include <algorithm>

namespace Vlab {
namespace Util {
namespace List {

void sort_and_remove_duplicate (std::vector<int>& values);

template <class ItA, class ItB>
bool has_intersection(ItA a_begin, ItA a_end, ItB b_begin, ItB b_end) {
  while (a_begin != a_end and b_begin != b_end) {
    if (*a_begin == *b_begin) {
      return true;
    } else if (*a_begin < *b_begin) {
      a_begin = std::lower_bound(++a_begin, a_end, *b_begin);
    } else {
      b_begin = std::lower_bound(++b_begin, b_end, *a_begin);
    }
  }
  return false;
}

} /* namespace List */
} /* namespace Util */
} /* namespace Vlab */

#endif /* SRC_UTILS_LIST_H_ */
