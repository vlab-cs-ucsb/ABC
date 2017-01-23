/*
 * StringFormula.h
 *
 *  Created on: Jan 22, 2017
 *      Author: baki
 */

#ifndef SRC_THEORY_STRINGFORMULA_H_
#define SRC_THEORY_STRINGFORMULA_H_

#include <cmath>
#include <cstdlib>
#include <locale>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
#include <utility>

#include <glog/logging.h>

#include "../smt/ast.h"

namespace Vlab {
namespace Theory {

class StringFormula;
using StringFormula_ptr = StringFormula*;

class StringFormula {
 public:
  enum class Type : int {
    NONE = 0, EQ, NOTEQ, GT, GE, LT, LE, DIFFERENCE, VAR,
        STRING_CONSTANT, REGEX_CONSTANT, EQ_NO_LAMBDA, EQ_ONLY_LAMBDA,
        BEGINS, NOTBEGINS, CONCAT_VAR_CONSTANT, INTERSECT, UNION, NONRELATIONAL
  };

  StringFormula();
  virtual ~StringFormula();

  StringFormula(const StringFormula&);
  StringFormula_ptr clone() const;

  std::string str() const;
  void set_type(Type type);
  StringFormula::Type get_type() const;
  int get_number_of_variables() const;
  std::map<std::string, int> get_variable_coefficient_map() const;
  void set_variable_coefficient_map(std::map<std::string, int>& coefficient_map);
  int get_variable_coefficient(std::string) const;
  void set_variable_coefficient(std::string, int coeff);
  void add_variable(std::string, int);
  void remove_variable(std::string);
  std::vector<int> get_coefficients() const;
  std::string get_constant() const;
  void set_constant(std::string constant);
  bool is_constant() const;
  void reset_param_orders(int value = 0);
  int get_variable_index(const std::string) const;
  int get_variable_index(const int param_index) const;

  bool has_relation_to_mixed_term(const std::string var_name) const;
  void add_relation_to_mixed_term(const std::string var_name, const StringFormula::Type relation, const SMT::Term_ptr term);
  std::pair<StringFormula::Type, SMT::Term_ptr> get_relation_to_mixed_term(const std::string var_name) const;
  bool UpdateMixedConstraintRelations();

  StringFormula_ptr Add(StringFormula_ptr);
  StringFormula_ptr Subtract(StringFormula_ptr);
  StringFormula_ptr Multiply(int value);
  StringFormula_ptr negate();

  bool Simplify();
  int CountOnes(unsigned long n) const;
  void merge_variables(StringFormula_ptr other);

  friend std::ostream& operator<<(std::ostream& os, const StringFormula& formula);

protected:
  bool get_var_names_if_equality_of_two_vars(std::string &v1, std::string &v2);

  StringFormula::Type type_;
  std::string constant_;
  /**
   * Track order is the sort order
   * Mapped value is the parameter order in the constraint
   */
  std::map<std::string, int> variable_order_map_;

  // TODO a quick solution for a restricted set of cases in mixed constraints
  // generalize it as much as possible
  std::map<std::string, std::pair<StringFormula::Type, SMT::Term_ptr>> mixed_terms_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_STRINGFORMULA_H_ */
