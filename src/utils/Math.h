/*
 * Math.h
 *
 *  Created on: Nov 16, 2015
 *      Author: baki
 */

#ifndef SRC_UTILS_MATH_H_
#define SRC_UTILS_MATH_H_

#include <cstdlib>
#include <vector>

#include <boost/multiprecision/cpp_int.hpp>

namespace Vlab {
namespace Util {
namespace Math {
using Matrix = std::vector<std::vector<boost::multiprecision::cpp_int>>;

int gcd(int x, int y);
int lcm(int x, int y);
Matrix multiply_matrix(Matrix& x, Matrix& y);

} /* namespace Math */
} /* namespace Util */
} /* namespace Vlab */

#endif /* SRC_UTILS_MATH_H_ */
