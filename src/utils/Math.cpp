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

Matrix multiply_matrix(Matrix& x, Matrix& y) {
  unsigned r = x[0].size();
  unsigned c = y.size();

  Matrix result(r, std::vector<boost::multiprecision::cpp_int> (c, 0));
  for (unsigned i = 0; i < r; ++i) {
    for (unsigned j = 0; j < c; ++j) {
      for (unsigned k = 0; k < r; ++k) {
        result[i][j] += x[i][k] * y[k][j];
      }
    }
  }

  return result;
}

} /* namespace Math */
} /* namespace Util */
} /* namespace Vlab */
