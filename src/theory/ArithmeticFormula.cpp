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

ArithmeticFormula::ArithmeticFormula() :
      type_(Type::NONE), constant_(0) {
}

ArithmeticFormula::ArithmeticFormula(std::map<std::string, int>& coeff_map, std::vector<int>& coeffs) :
      type_(Type::NONE), constant_(0) {
  coeff_index_map_ = coeff_map;
  coefficients_ = coeffs;
}

ArithmeticFormula::~ArithmeticFormula() {
}

ArithmeticFormula::ArithmeticFormula(const ArithmeticFormula& other) :
      type_(other.type_), constant_(other.constant_),
      coeff_index_map_(other.coeff_index_map_),
      coefficients_(other.coefficients_) {

}

ArithmeticFormula_ptr ArithmeticFormula::clone() const {
  return new ArithmeticFormula(*this);
}

std::string ArithmeticFormula::str() const {
  std::stringstream ss;
  std::vector<std::string> variable_names(coefficients_.size());

  auto char_remover = []( char ch ) {
    return std::isspace<char>( ch, std::locale::classic() ) or ch == '"' or ch == ';';
  };

  for (auto& pair : coeff_index_map_) {
    std::string name = pair.first;
    if (pair.first.find("len") != std::string::npos) {
      name = "len_term";
    } else if (pair.first.find("lastIndexOf") != std::string::npos or
            pair.first.find("indexOf") != std::string::npos) {
      name = "index_term";
    }
    variable_names[pair.second] = name;
  }
  bool print_sign = false;
  for (unsigned i = 0; i < coefficients_.size(); i++) {
    if (coefficients_[i] > 0) {
      if (i > 0 and print_sign) {
        ss << " + ";
      }
      if (coefficients_[i] > 1) {
        ss << coefficients_[i];
      }
      ss << variable_names[i];
      print_sign = true;
    } else if (coefficients_[i] < 0) {
      if (i > 0 and print_sign) {
        ss << " - ";
      } else {
        ss << "-";
      }
      int abs_value = std::abs(coefficients_[i]);
      if (abs_value > 1) {
        ss << abs_value;
      }
      ss << variable_names[i];
      print_sign = true;
    }
  }

  if (constant_ > 0) {
    ss << " + " << constant_;
  } else if (constant_ < 0) {
    ss << " - " << std::abs(constant_);
  }

  if (type_ == Type::INTERSECT or type_ == Type::UNION) {
    std::string separator = "";
    for (auto& pair : coeff_index_map_) {
      ss << separator << pair.first;
      separator = ", ";
    }
  }

  ss << " ";

  switch (type_) {
    case Type::EQ:
      ss << "=";
      break;
    case Type::NOTEQ:
      ss << "!=";
      break;
    case Type::GT:
      ss << ">";
      break;
    case Type::GE:
      ss << ">=";
      break;
    case Type::LT:
      ss << "<";
      break;
    case Type::LE:
      ss << "<=";
      break;
    case Type::INTERSECT:
      ss << "&";
      break;
    case Type::UNION:
      ss << "|";
      break;
    case Type::VAR:
      ss << "<var>";
      break;
    default:
      ss << "none";
      break;
  }
  if (type_ != Type::INTERSECT and type_ != Type::UNION and type_ != Type::VAR) {
    ss << " " << 0;
  }

  return ss.str();
}

void ArithmeticFormula::set_type(Type type) {
  this->type_ = type;
}

ArithmeticFormula::Type ArithmeticFormula::get_type() const {
  return type_;
}

int ArithmeticFormula::get_number_of_variables() const {
  return coeff_index_map_.size();
}

std::vector<int>& ArithmeticFormula::get_coefficients() {
  return coefficients_;
}

std::map<std::string, int>& ArithmeticFormula::get_coefficient_index_map() {
  return coeff_index_map_;
}

int ArithmeticFormula::get_variable_index(std::string variable_name) {
  auto it = coeff_index_map_.find(variable_name);
  if (it != coeff_index_map_.end()) {
    return it->second;
  }
  LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  return -1;
}

int ArithmeticFormula::get_variable_coefficient(std::string variable_name) {
  auto iter = coeff_index_map_.find(variable_name);
  if (iter == coeff_index_map_.end()) {
    return 0;
  }
  return coefficients_[iter->second];
}

void ArithmeticFormula::set_variable_coefficient(std::string variable_name, int coeff) {
  auto it = coeff_index_map_.find(variable_name);
  if (it == coeff_index_map_.end()) {
    coefficients_.push_back(coeff);
    coeff_index_map_[variable_name] = coefficients_.size() - 1;
  } else {
    coefficients_[coeff_index_map_[variable_name]] = coeff;
  }
}

int ArithmeticFormula::get_constant() {
  return constant_;
}

void ArithmeticFormula::set_constant(int constant) {
  this->constant_ = constant;
}

bool ArithmeticFormula::is_constant() {
  for (auto& coeff : coefficients_) {
    if ( coeff != 0) {
      return false;
    }
  }
  return true;
}

bool ArithmeticFormula::IsVariableOrderingSame(ArithmeticFormula_ptr other_formula) {
  if (coeff_index_map_.size() not_eq other_formula->coeff_index_map_.size()) {
    return false;
  }

  for (auto& pair : coeff_index_map_) {
    auto other_pair = other_formula->coeff_index_map_.find(pair.first);
    if (other_pair == other_formula->coeff_index_map_.end()) {
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
void ArithmeticFormula::MergeCoefficients(ArithmeticFormula_ptr other_formula) {
  std::map<std::string, int> merged_coeff_index_map = other_formula->coeff_index_map_;
  std::vector<int> merged_coefficients (merged_coeff_index_map.size()); // all zeros

  for (auto& pair : coeff_index_map_) {
    auto it = merged_coeff_index_map.find(pair.first);
    if (it == merged_coeff_index_map.end()) {
      merged_coefficients.push_back(coefficients_[pair.second]);
      merged_coeff_index_map[pair.first] = merged_coefficients.size() - 1;
    } else {
      merged_coefficients[it->second] = coefficients_[pair.second];
    }
  }

  coeff_index_map_ = merged_coeff_index_map;
  coefficients_ = merged_coefficients;
}

void ArithmeticFormula::reset_coefficients(int value) {
  for (auto& c : coefficients_) {
    c = value;
  }
}

ArithmeticFormula_ptr ArithmeticFormula::Substract(ArithmeticFormula_ptr other_formula) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);
  if (not result->IsVariableOrderingSame(other_formula)) {
    result->MergeCoefficients(other_formula);
  }

  for (auto& pair : other_formula->coeff_index_map_) {
    auto it = result->coeff_index_map_.find(pair.first);
    if (it != result->coeff_index_map_.end()) {
      result->coefficients_[it->second] = result->coefficients_[it->second] - other_formula->coefficients_[pair.second];
    }
  }
  result->constant_ = result->constant_ - other_formula->constant_;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::NegateOperation() {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);
  switch (type_) {
    case Type::EQ:
      result->type_ = Type::NOTEQ;
      break;
    case Type::NOTEQ:
      result->type_ = Type::EQ;
      break;
    case Type::GT:
      result->type_ = Type::LE;
      break;
    case Type::GE:
      result->type_ = Type::LT;
      break;
    case Type::LT:
      result->type_ = Type::GE;
      break;
    case Type::LE:
      result->type_ = Type::GT;
      break;
    default:
      break;
  }
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::Multiply(int value) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);
  for (auto& coeff : result->coefficients_) {
    coeff = value * coeff;
  }
  result->constant_ = value * constant_;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::Add(ArithmeticFormula_ptr other_formula) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);

  if (not result->IsVariableOrderingSame(other_formula)) {
    result->MergeCoefficients(other_formula);
  }

  for (auto& pair : other_formula->coeff_index_map_) {
    auto it = result->coeff_index_map_.find(pair.first);
    if (it != result->coeff_index_map_.end()) {
      result->coefficients_[it->second] = result->coefficients_[it->second] + other_formula->coefficients_[pair.second];
    }
  }
  result->constant_ = result->constant_ + other_formula->constant_;
  return result;
}

/**
 * @returns false if formula is not satisfiable and catched by simplification
 */
bool ArithmeticFormula::Simplify() {
  if (coefficients_.size() == 0) {
    return true;
  }

  int gcd_value = coefficients_[0];

  for (int c : coefficients_) {
    gcd_value = Util::Math::gcd(gcd_value, c);
  }

  if (gcd_value == 0) {
    return true;
  }

  switch (type_) {
    case Type::EQ: {
      if (constant_ % gcd_value == 0) {
        constant_ = constant_ / gcd_value;
      } else {
        return false;
      }
      break;
    }
    case Type::LT: {
      if (constant_ >= 0) {
        constant_ = constant_ / gcd_value;
      } else {
        constant_ = std::floor((double)constant_/gcd_value);
      }
      break;
    }
    default:
      LOG(FATAL)<< "Simplification is only done after converting into '=' or '<' equation";
      break;
  }

  for (int& c : coefficients_) {
    c = c / gcd_value;
  }

  return true;
}

int ArithmeticFormula::CountOnes(unsigned long n) {
  int ones = 0;
  for (auto& c : coefficients_) {
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

} /* namespace Theory */
} /* namespace Vlab */
