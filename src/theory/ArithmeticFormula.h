/*
 * ArithmeticFormula.h
 *
 *  Created on: Oct 23, 2015
 *      Author: baki
 */

#ifndef SRC_THEORY_ARITHMETICFORMULA_H_
#define SRC_THEORY_ARITHMETICFORMULA_H_

#include <cmath>
#include <cstdlib>
#include <map>
#include <string>
#include <sstream>
#include <utility>
#include <vector>

#include <glog/logging.h>

#include "../utils/Math.h"

namespace Vlab {
namespace Theory {

class ArithmeticFormula;
typedef ArithmeticFormula* ArithmeticFormula_ptr;

class ArithmeticFormula {
public:
  enum class Type :
          int {
            NONE = 0, EQ, NOTEQ, GT, GE, LT, LE, INTERSECT, UNION, VAR
          };
  ArithmeticFormula();
  ArithmeticFormula(std::map<std::string, int>& coeff_map, std::vector<int>& coeffs);
  virtual ~ArithmeticFormula();

  ArithmeticFormula(const ArithmeticFormula&);
  ArithmeticFormula_ptr clone() const;

  std::string str() const;
  void set_type(Type type);
  ArithmeticFormula::Type get_type() const;
  int get_number_of_variables() const;
  std::vector<int>& get_coefficients();
  std::map<std::string, int>& get_coefficient_index_map();
  int get_variable_index(std::string);
  int get_variable_coefficient(std::string);
  void set_variable_coefficient(std::string, int coeff);
  int get_constant();
  void set_constant(int constant);
  bool is_constant();
  bool IsVariableOrderingSame(ArithmeticFormula_ptr other_formula);
  void MergeCoefficients(ArithmeticFormula_ptr other_formula);
  void reset_coefficients(int value = 0);

  ArithmeticFormula_ptr Substract(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr NegateOperation();
  ArithmeticFormula_ptr Multiply(int value);
  ArithmeticFormula_ptr Add(ArithmeticFormula_ptr);

  bool Simplify();
  int CountOnes(unsigned long n);

  friend std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula);

protected:
  ArithmeticFormula::Type type_;
  int constant_;
  std::map<std::string, int> coeff_index_map_;
  std::vector<int> coefficients_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_ARITHMETICFORMULA_H_ */
