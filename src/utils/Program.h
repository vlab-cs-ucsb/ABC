/*
 * Program.h
 *
 *  Created on: Jul 20, 2016
 *      Author: baki
 */

#ifndef SRC_UTILS_PROGRAM_H_
#define SRC_UTILS_PROGRAM_H_

#include <vector>
#include <functional>

#include "../boost/multiprecision/cpp_int.hpp"
#include "../Eigen/SparseCore"
#include "Math.h"

namespace Vlab {
namespace Util {
namespace Program {

void big_for_loop(std::vector<int> bounds, std::function<void(int& index)> loop_body);

void serialize(std::ostream& ar, Eigen::SparseMatrix<Theory::BigInteger>& sparse_matrix);

void deserialize(std::istream& ar, Eigen::SparseMatrix<Theory::BigInteger>& sparse_matrix);

} /* namespace Program */
} /* namespace Util */
} /* namespace Vlab */

#endif /* SRC_UTILS_PROGRAM_H_ */
