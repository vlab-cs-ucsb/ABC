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
#include <locale>
#include <map>
#include <sstream>
#include <string>
#include <vector>
#include <utility>

#include <glog/logging.h>
#include <boost/multiprecision/cpp_int.hpp>

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
  virtual ~ArithmeticFormula();

  ArithmeticFormula(const ArithmeticFormula&);
  ArithmeticFormula_ptr clone() const;

  std::string str() const;
  void set_type(Type type);
  ArithmeticFormula::Type get_type() const;
  int get_number_of_variables() const;
  std::map<std::string, int> get_variable_coefficient_map() const;
  void set_variable_coefficient_map(std::map<std::string, int>& coefficient_map);
  int get_variable_coefficient(std::string) const;
  void set_variable_coefficient(std::string, int coeff);
  void add_variable(std::string, int);
  std::vector<int> get_coefficients() const;
  int get_constant() const;
  void set_constant(int constant);
  bool is_constant() const;
  void reset_coefficients(int value = 0);
  int get_variable_index(std::string) const;

  ArithmeticFormula_ptr Add(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr Subtract(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr Multiply(int value);
  ArithmeticFormula_ptr negate();

  bool Simplify();
  int CountOnes(unsigned long n);
  void merge_variables(ArithmeticFormula_ptr other);

  friend std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula);

protected:
  ArithmeticFormula::Type type_;
  int constant_;
  std::map<std::string, int> variable_coefficient_map_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_ARITHMETICFORMULA_H_ */
