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
#include "../cereal/archives/binary.hpp"
#include "Math.h"

namespace Vlab {
namespace Util {
namespace Program {

void big_for_loop(std::vector<int> bounds, std::function<void(int& index)> loop_body);

template<class Archive>
void save(Archive& ar, const Theory::BigInteger& big_integer) {

  bool s = big_integer.sign();
  ar(s);
  std::size_t c = big_integer.backend().size();
  ar(c);
  ar(cereal::binary_data(big_integer.backend().limbs(), c * sizeof(boost::multiprecision::limb_type)));
}

template<class Archive>
void load(Archive& ar, Theory::BigInteger& big_integer) {
  bool s;
  ar(s);
  std::size_t c;
  ar(c);
  big_integer.backend().resize(c, c);
  ar(cereal::binary_data(big_integer.backend().limbs(), c * sizeof(boost::multiprecision::limb_type)));
  if(s != big_integer.sign()) {
      big_integer.backend().negate();
  }
  big_integer.backend().normalize();
}

template<class Archive>
void save(Archive& ar, const Eigen::SparseMatrix<Theory::BigInteger>& sparse_matrix) {
  ar(sparse_matrix.rows());
  ar(sparse_matrix.cols());
  ar(sparse_matrix.outerSize());
  ar(sparse_matrix.innerSize());
  ar(sparse_matrix.nonZeros());
  ar(cereal::binary_data(sparse_matrix.outerIndexPtr(), sparse_matrix.outerSize() * sizeof(int)));
  ar(cereal::binary_data(sparse_matrix.innerIndexPtr(), sparse_matrix.innerSize() * sizeof(int)));
  for (Eigen::Index i = 0; i < sparse_matrix.nonZeros(); ++i) {
    save(ar, sparse_matrix.valuePtr()[i]);
  }

}

template<class Archive>
void load(Archive& ar, Eigen::SparseMatrix<Theory::BigInteger>& sparse_matrix) {
  Eigen::Index rows = 0, cols = 0, non_zeros = 0, outer_size = 0, inner_size = 0;
  ar(rows);
  ar(cols);
  ar(outer_size);
  ar(inner_size);
  ar(non_zeros);
  sparse_matrix.resize(rows, cols);
  sparse_matrix.resizeNonZeros(non_zeros);
  ar(cereal::binary_data(sparse_matrix.outerIndexPtr(), sparse_matrix.outerSize() * sizeof(int)));
  ar(cereal::binary_data(sparse_matrix.innerIndexPtr(), sparse_matrix.innerSize() * sizeof(int)));
  for (Eigen::Index i = 0; i < non_zeros; ++i) {
    load(ar, sparse_matrix.valuePtr()[i]);
  }
  sparse_matrix.makeCompressed();
  sparse_matrix.finalize();
}

} /* namespace Program */
} /* namespace Util */
} /* namespace Vlab */

#endif /* SRC_UTILS_PROGRAM_H_ */
