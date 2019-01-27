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
#include <cereal/types/map.hpp>

#include "Formula.h"
#include "../smt/ast.h"
#include "../utils/Math.h"

namespace Vlab {
namespace Theory {

class ArithmeticFormula;
using ArithmeticFormula_ptr = ArithmeticFormula*;

class ArithmeticFormula : public Formula {
public:
  enum class Type :
          int {
            NONE = 0, EQ, NOTEQ, GT, GE, LT, LE, INTERSECT, UNION, VAR, BOOL, NE
          };
  ArithmeticFormula();
  virtual ~ArithmeticFormula();

  ArithmeticFormula(const ArithmeticFormula&);
  virtual ArithmeticFormula_ptr clone() const;

  template <class Archive>
  void save(Archive& ar) const {
    ar(type_);
    ar(variable_coefficient_map_);
    //ar(boolean_variable_value_map_);
  }

  template <class Archive>
  void load(Archive& ar) {
    ar(type_);
    ar(variable_coefficient_map_);
    //ar(boolean_variable_value_map_);
  }

  virtual std::string str() const;

  virtual ArithmeticFormula_ptr Intersect(Formula_ptr);
	virtual ArithmeticFormula_ptr Union(Formula_ptr);
	virtual ArithmeticFormula_ptr Complement();

	void AddBoolean(std::string);
	std::map<std::string,bool> GetBooleans() const;

  void SetType(Type type);
  ArithmeticFormula::Type GetType() const;
  int GetConstant() const;
  void SetConstant(int constant);
  bool IsConstant() const;

  bool HasRelationToMixedTerm(const std::string var_name) const;
  void AddRelationToMixedTerm(const std::string var_name, const ArithmeticFormula::Type relation, const SMT::Term_ptr term);
  std::pair<ArithmeticFormula::Type, SMT::Term_ptr> GetRelationToMixedTerm(const std::string var_name) const;
  bool UpdateMixedConstraintRelations();

  ArithmeticFormula_ptr Add(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr Subtract(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr Multiply(int value);
  ArithmeticFormula_ptr negate();

  bool Simplify() override;
  int CountOnes(unsigned long n) const;
  virtual void MergeVariables(Formula_ptr);

  friend std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula);

protected:
  bool GetVarNamesIfEqualityOfTwoVars(std::string &v1, std::string &v2);

  ArithmeticFormula::Type type_;
  std::map<std::string, bool> boolean_variable_value_map_;
  int constant_;

  // TODO a quick solution for a restricted set of cases in mixed constraints
  // generalize it as much as possible
  std::map<std::string, std::pair<ArithmeticFormula::Type, SMT::Term_ptr>> mixed_terms_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_ARITHMETICFORMULA_H_ */
