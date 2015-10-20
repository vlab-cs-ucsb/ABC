/*
 * ArithmeticFormula.cpp
 *
 *  Created on: Oct 23, 2015
 *      Author: baki
 */

#include "ArithmeticFormula.h"

namespace Vlab {
namespace Theory {


const int ArithmeticFormula::VLOG_LEVEL = 15;

const std::string ArithmeticFormula::Name::NONE = "none";
const std::string ArithmeticFormula::Name::EQ = "=";
const std::string ArithmeticFormula::Name::NOTEQ = "!=";
const std::string ArithmeticFormula::Name::GT = ">";
const std::string ArithmeticFormula::Name::GE = ">=";
const std::string ArithmeticFormula::Name::LT = "<";
const std::string ArithmeticFormula::Name::LE = "<=";

ArithmeticFormula::ArithmeticFormula() :
      type(Type::NONE), constant(0) {
}

ArithmeticFormula::ArithmeticFormula(std::map<std::string, int>& coeff_map, std::vector<int>& coeffs) :
      type(Type::NONE), constant(0) {
  coeff_index_map = coeff_map;
  coefficients = coeffs;
}

ArithmeticFormula::~ArithmeticFormula() {
}

ArithmeticFormula::ArithmeticFormula(const ArithmeticFormula& other) :
      type(other.type), constant(other.constant),
      coeff_index_map(other.coeff_index_map),
      coefficients(other.coefficients) {

}

ArithmeticFormula_ptr ArithmeticFormula::clone() const {
  return new ArithmeticFormula(*this);
}

std::string ArithmeticFormula::str() const {
  std::stringstream ss;
  std::vector<std::string> variable_names(coefficients.size());
  for (auto& pair : coeff_index_map) {
    variable_names[pair.second] = pair.first;
  }

  for (unsigned i = 0; i < coefficients.size(); i++) {
    if (coefficients[i] > 0) {
      if (i > 0) {
        ss << " + ";
      }
      if (coefficients[i] > 1) {
        ss << coefficients[i];
      }
      ss << variable_names[i];
    } else if (coefficients[i] < 0) {
      ss << " -";
      if (i > 0) {
        ss << " ";
      }
      if (coefficients[i] > 1) {
        ss << std::abs(coefficients[i]);
      }
      ss << variable_names[i];
    }
  }

  if (constant > 0) {
    ss << " + " << constant;
  } else if (constant < 0) {
    ss << " - " << std::abs(constant);
  }

  ss << " ";

  switch (type) {
    case Type::EQ:
      ss << Name::EQ;
      break;
    case Type::NOTEQ:
      ss << Name::NOTEQ;
      break;
    case Type::GT:
      ss << Name::GT;
      break;
    case Type::GE:
      ss << Name::GE;
      break;
    case Type::LT:
      ss << Name::LT;
      break;
    case Type::LE:
      ss << Name::LE;
      break;
    default:
      break;
  }

  ss << " " << 0;

  return ss.str();
}

void ArithmeticFormula::setType(Type type) {
  this->type = type;
}

ArithmeticFormula::Type ArithmeticFormula::getType() const {
  return type;
}

std::vector<int>& ArithmeticFormula::getCoefficients() {
  return coefficients;
}

int ArithmeticFormula::getVariableCoefficient(std::string variable_name) {
  auto iter = coeff_index_map.find(variable_name);
  if (iter == coeff_index_map.end()) {
    return 0;
  }
  return coefficients[iter->second];
}

void ArithmeticFormula::setVariableCoefficient(std::string variable_name, int coeff) {
  coefficients[coeff_index_map[variable_name]] = coeff;
}

int ArithmeticFormula::getConstant() {
  return constant;
}

void ArithmeticFormula::setConstant(int constant) {
  this->constant = constant;
}

bool ArithmeticFormula::isConstant() {
  for (auto& coeff : coefficients) {
    if ( coeff != 0) {
      return false;
    }
  }
  return true;
}

bool ArithmeticFormula::isVariableOrderingSame(ArithmeticFormula_ptr other_formula) {
  if (coeff_index_map.size() not_eq other_formula->coeff_index_map.size()) {
    return false;
  }

  for (auto& pair : coeff_index_map) {
    auto other_pair = other_formula->coeff_index_map.find(pair.first);
    if (other_pair == other_formula->coeff_index_map.end()) {
      return false;
    } else if (pair.second != other_pair->second) {
      return false;
    }
  }

  return true;
}

/**
 * Updates coefficients and coefficient map based on other formula
 */
void ArithmeticFormula::mergeCoefficients(ArithmeticFormula_ptr other_formula) {
  std::map<std::string, int> merged_coeff_index_map = other_formula->coeff_index_map;
  std::vector<int> merged_coefficients (merged_coeff_index_map.size()); // all zeros

  for (auto& pair : coeff_index_map) {
    auto it = merged_coeff_index_map.find(pair.first);
    if (it == merged_coeff_index_map.end()) {
      merged_coefficients.push_back(coefficients[pair.second]);
      merged_coeff_index_map[pair.first] = merged_coefficients.size() - 1;
    } else {
      merged_coefficients[it->second] = coefficients[pair.second];
    }
  }

  coeff_index_map = merged_coeff_index_map;
  coefficients = merged_coefficients;
}

ArithmeticFormula_ptr ArithmeticFormula::substract(ArithmeticFormula_ptr other_formula) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);
  if (not result->isVariableOrderingSame(other_formula)) {
    result->mergeCoefficients(other_formula);
  }

  for (auto& pair : other_formula->coeff_index_map) {
    auto it = result->coeff_index_map.find(pair.first);
    if (it != result->coeff_index_map.end()) {
      result->coefficients[it->second] = result->coefficients[it->second] - other_formula->coefficients[pair.second];
    }
  }
  result->constant = constant - other_formula->constant;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::negate() {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);
  switch (type) {
    case Type::EQ:
      result->type = Type::NOTEQ;
      break;
    case Type::NOTEQ:
      result->type = Type::EQ;
      break;
    case Type::GT:
      result->type = Type::LE;
      break;
    case Type::GE:
      result->type = Type::LT;
      break;
    case Type::LT:
      result->type = Type::GE;
      break;
    case Type::LE:
      result->type = Type::GT;
      break;
    default:
      break;
  }
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::multiply(int value) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);
  for (auto& coeff : result->coefficients) {
    coeff = value * coeff;
  }
  result->constant = value * constant;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::add(ArithmeticFormula_ptr other_formula) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);

  if (not result->isVariableOrderingSame(other_formula)) {
    result->mergeCoefficients(other_formula);
  }

  for (auto& pair : other_formula->coeff_index_map) {
    auto it = result->coeff_index_map.find(pair.first);
    if (it != result->coeff_index_map.end()) {
      result->coefficients[it->second] = result->coefficients[it->second] + other_formula->coefficients[pair.second];
    }
  }
  result->constant = result->constant + other_formula->constant;
  return result;
}

/**
 * @returns false if formula is not satisfiable during optimization
 */
bool ArithmeticFormula::optimize() {
  int gcd_value = 1;

  if (coefficients.size() == 0) {
    return true; // no optimization required
  }

  gcd_value = coefficients[0];

  for (int c : coefficients) {
    gcd_value = gcd(gcd_value, c);
  }

  for (int& c : coefficients) {
    c = c / gcd_value;
  }

  switch (type) {
    case Type::EQ: {
      if (constant % gcd_value == 0) {
        constant = constant / gcd_value;
      } else {
        return false;
      }
      break;
    }
    case Type::LT: {
      constant = constant + gcd_value - 1;
      if (constant >= 0) {
        constant = constant / gcd_value;
      } else {
        constant = (constant + 1) / gcd_value - 1;
      }
      break;
    }
    default: {

      break;
    }
  }

  return true;
}

int ArithmeticFormula::countOnes(unsigned long n) {
  int ones = 0;
  for (auto& c : coefficients) {
    if (n & 1) {
      ones += c;
    }
    n >>= 1;
  }
  return ones;
}

std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula) {
  return os << formula.str();
}

int ArithmeticFormula::gcd(int x , int y) {
  int c;
  while (y != 0) {
    c = x % y;
    x = y;
    y = c;
  }
  if (x > 0)
    return x;
  else
    return -x;
}



} /* namespace Theory */
} /* namespace Vlab */
