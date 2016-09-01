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
  std::map<std::string, int>& get_var_coeff_map();
  int get_variable_index(std::string) const;
  int get_variable_coefficient(std::string);
  void set_variable_coefficient(std::string, int coeff);
  int get_constant();
  void set_constant(int constant);
  bool is_constant();
  void reset_coefficients(int value = 0);

  void add_variable(std::string, int);
  std::map<std::string, int> get_variable_trackmap();
  void set_variable_trackmap(std::map<std::string, int> trackmap);
  void create_coeff_vec();
  std::vector<int> get_coefficients();

  ArithmeticFormula_ptr Subtract(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr NegateOperation();
  ArithmeticFormula_ptr Multiply(int value);
  ArithmeticFormula_ptr Add(ArithmeticFormula_ptr);

  bool Simplify();

  friend std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula);

protected:
  ArithmeticFormula::Type type_;
  int constant_;
  std::vector<int> coefficients_;
  std::map<std::string, int> var_coeff_map_;
  std::map<std::string, int> trackmap_handle_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_ARITHMETICFORMULA_H_ */
