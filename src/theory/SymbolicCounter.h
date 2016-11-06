/*
 * SymbolicCounter.h
 *
 *  Created on: Oct 31, 2016
 *      Author: baki
 */

#ifndef SRC_THEORY_SYMBOLICCOUNTER_H_
#define SRC_THEORY_SYMBOLICCOUNTER_H_

#include <ostream>
#include <sstream>
#include <string>

#include <glog/logging.h>

#include "../utils/Serialize.h"

namespace Vlab {
namespace Theory {

class SymbolicCounter {
 public:
  enum class Type
    : int {
      STRING, UNARYINT, BINARYINT, BINARYUNSIGNEDINT
  };
  SymbolicCounter();
  virtual ~SymbolicCounter();

  Type type();
  void set_type(const Type t);
  unsigned long get_bound();
  void set_bound(const unsigned long bound);
  Eigen::SparseVector<BigInteger> get_initialization_vector() const;
  void set_initialization_vector(const Eigen::SparseVector<BigInteger>& initialization_vector);
  Eigen::SparseMatrix<BigInteger> get_transition_count_matrix() const;
  void set_transition_count_matrix(const Eigen::SparseMatrix<BigInteger>& transition_count_matrix);

  BigInteger Count(const unsigned long bound);
  BigInteger CountbyMatrixMultiplication(const unsigned long bound);

  template <class Archive>
  void save(Archive& ar) const {
    ar(static_cast<int>(type_));
    ar(bound_);
    Util::Serialize::save(ar, initialization_vector_);
    Util::Serialize::save(ar, transition_count_matrix_);
  }

  template <class Archive>
  void load(Archive& ar) {
    int type = 0;
    ar(type);
    type_ = static_cast<Type>(type);
    ar(bound_);
    Util::Serialize::load(ar, initialization_vector_);
    Util::Serialize::load(ar, transition_count_matrix_);
  }

  std::string str() const;
  friend std::ostream& operator<<(std::ostream& os, const SymbolicCounter& sc);
protected:
  Type type_;
  unsigned long bound_;
  Eigen::SparseVector<BigInteger> initialization_vector_;
  Eigen::SparseMatrix<BigInteger> transition_count_matrix_;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_SYMBOLICCOUNTER_H_ */
