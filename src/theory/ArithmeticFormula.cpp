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
const std::string ArithmeticFormula::Name::INTERSECT = "&";
const std::string ArithmeticFormula::Name::UNION = "|";

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

  auto char_remover = []( char ch ) {
    return std::isspace<char>( ch, std::locale::classic() ) or ch == '"' or ch == ';';
  };

  for (auto& pair : coeff_index_map) {
    std::string name = pair.first;
    if (pair.first.find("len") != std::string::npos) {
      name = "len_term";
    } else if (pair.first.find("lastIndexOf") != std::string::npos or
            pair.first.find("indexOf") != std::string::npos) {
      name = "index_term";
    }
    variable_names[pair.second] = name;
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
      if (i > 0) {
        ss << " - ";
      } else {
        ss << "-";
      }
      int abs_value = std::abs(coefficients[i]);
      if (abs_value > 1) {
        ss << abs_value;
      }
      ss << variable_names[i];
    }
  }

  if (constant > 0) {
    ss << " + " << constant;
  } else if (constant < 0) {
    ss << " - " << std::abs(constant);
  }

  if (type == Type::INTERSECT or type == Type::UNION) {
    std::string separator = "";
    for (auto& pair : coeff_index_map) {
      ss << separator << pair.first;
      separator = ", ";
    }
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
    case Type::INTERSECT:
      ss << Name::INTERSECT;
      break;
    case Type::UNION:
      ss << Name::UNION;
      break;
    default:
      break;
  }
  if (type != Type::INTERSECT and type != Type::UNION) {
    ss << " " << 0;
  }


  return ss.str();
}

void ArithmeticFormula::setType(Type type) {
  this->type = type;
}

ArithmeticFormula::Type ArithmeticFormula::getType() const {
  return type;
}

int ArithmeticFormula::getNumberOfVariables() const {
  return coeff_index_map.size();
}

std::vector<int>& ArithmeticFormula::getCoefficients() {
  return coefficients;
}

std::map<std::string, int>& ArithmeticFormula::getCoefficientIndexMap() {
  return coeff_index_map;
}

int ArithmeticFormula::getVariableIndex(std::string variable_name) {
  auto it = coeff_index_map.find(variable_name);
  if (it != coeff_index_map.end()) {
    return it->second;
  }
  LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  return -1;
}

int ArithmeticFormula::getVariableCoefficient(std::string variable_name) {
  auto iter = coeff_index_map.find(variable_name);
  if (iter == coeff_index_map.end()) {
    return 0;
  }
  return coefficients[iter->second];
}

void ArithmeticFormula::setVariableCoefficient(std::string variable_name, int coeff) {
  auto it = coeff_index_map.find(variable_name);
  if (it == coeff_index_map.end()) {
    coefficients.push_back(coeff);
    coeff_index_map[variable_name] = coefficients.size() - 1;
  } else {
    coefficients[coeff_index_map[variable_name]] = coeff;
  }
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

void ArithmeticFormula::resetCoefficients(int value) {
  for (auto& c : coefficients) {
    c = value;
  }
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
  result->constant = result->constant - other_formula->constant;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::negateOperation() {
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
 * @returns false if formula is not satisfiable and catched by simplification
 */
bool ArithmeticFormula::simplify() {
  if (coefficients.size() == 0) {
    return true;
  }

  int gcd_value = coefficients[0];

  for (int c : coefficients) {
    gcd_value = gcd(gcd_value, c);
  }

  if (gcd_value == 0) {
    return true;
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
      if (constant >= 0) {
        constant = constant / gcd_value;
      } else {
        constant = std::floor((double)constant/gcd_value);
      }
      break;
    }
    default:
      LOG(FATAL)<< "Simplification is only done after converting into '=' or '<' equation";
      break;
  }

  for (int& c : coefficients) {
    c = c / gcd_value;
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
  if (x == 0) {
    return std::abs(y);
  }
  int c;
  while (y != 0) {
    c = x % y;
    x = y;
    y = c;
  }
  return std::abs(x);
}



} /* namespace Theory */
} /* namespace Vlab */
