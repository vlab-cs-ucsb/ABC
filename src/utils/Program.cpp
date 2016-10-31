/*
 * Program.cpp
 *
 *  Created on: Jul 20, 2016
 *      Author: baki
 */

#include "Program.h"

namespace Vlab {
namespace Util {
namespace Program {

void big_for_loop(std::vector<int> bounds, std::function<void(int& index)> loop_body) {
  const int depth = bounds.size();
  int level = 0;
  std::vector<int> indexes (depth, 1);
  int count = 0;
  while (level < depth) {
    int bound = bounds[level];
    if (level == 0) { // inner most loop
      for(int i = 0; i < bound; ++i) {
        loop_body(i);
      }
      ++level; // continue to outer loop
    } else if (indexes[level] < bound) {
      ++indexes[level];
      --level; // descent into inner loop
    } else {
      indexes[level] = 0;
      ++level;
    }
  }
}

} /* namespace Program */
} /* namespace Util */
} /* namespace Vlab */
