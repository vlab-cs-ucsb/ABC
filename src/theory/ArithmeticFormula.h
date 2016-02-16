/*
 * ArithmeticFormula.h
 *
 *  Created on: Oct 23, 2015
 *      Author: baki
 */

#ifndef SRC_THEORY_ARITHMETICFORMULA_H_
#define SRC_THEORY_ARITHMETICFORMULA_H_

#include <vector>
#include <map>
#include <string>
#include <sstream>
#include <cmath>

#include <glog/logging.h>

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
  void setType(Type type);
  ArithmeticFormula::Type getType() const;
  int getNumberOfVariables() const;
  std::vector<int>& getCoefficients();
  std::map<std::string, int>& getCoefficientIndexMap();
  int getVariableIndex(std::string);
  int getVariableCoefficient(std::string);
  void setVariableCoefficient(std::string, int coeff);
  int getConstant();
  void setConstant(int constant);
  bool isConstant();
  bool isVariableOrderingSame(ArithmeticFormula_ptr other_formula);
  void mergeCoefficients(ArithmeticFormula_ptr other_formula);
  void resetCoefficients(int value = 0);

  ArithmeticFormula_ptr substract(ArithmeticFormula_ptr);
  ArithmeticFormula_ptr negateOperation();
  ArithmeticFormula_ptr multiply(int value);
  ArithmeticFormula_ptr add(ArithmeticFormula_ptr);

  bool simplify();
  int countOnes(unsigned long n);

  class Name {
  public:
    static const std::string NONE;
    static const std::string EQ;
    static const std::string NOTEQ;
    static const std::string GT;
    static const std::string GE;
    static const std::string LT;
    static const std::string LE;
    static const std::string INTERSECT;
    static const std::string UNION;
    static const std::string VAR;
  };

  friend std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula);

protected:
  int gcd(int x , int y);


  ArithmeticFormula::Type type;
  int constant;
  std::map<std::string, int> coeff_index_map;
  std::vector<int> coefficients;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_ARITHMETICFORMULA_H_ */
