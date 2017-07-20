/*
 * StringEncoding.h
 *
 *  Created on: May 12, 2017
 *      Author: baki
 */

#ifndef SRC_THEORY_STRINGENCODING_H_
#define SRC_THEORY_STRINGENCODING_H_

namespace Vlab {
namespace Theory {

/**
 * TODO add an encoding class for all types
 * 1- can be added a base encoding
 * 2- encoding describes how we map alphabet used in automata to bdd transitions
 */
class StringEncoding {
 public:
  StringEncoding();
  StringEncoding(int alphabet_size);
 private:
  int alphabet_size_;
  int number_of_bdd_variables_;
  int* bdd_variable_indices_;

};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_STRINGENCODING_H_ */
