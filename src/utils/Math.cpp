/*
 * Math.cpp
 *
 *  Created on: Nov 16, 2015
 *      Author: baki
 */

#include "Math.h"

namespace Vlab {
namespace Util {
namespace Math {

int gcd(int x, int y) {
  if (x == 0) {
    return std::abs(y);
  }
  int c;
  while (y != 0) {
    c = x % y;
    x = y;
    y = c;
  }
  return std::abs(x);
}

int lcm(int x, int y) {
  return x * y / gcd(x, y);
}

} /* namespace Math */
} /* namespace Util */
} /* namespace Vlab */
