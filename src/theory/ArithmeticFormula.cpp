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

ArithmeticFormula::ArithmeticFormula()
    : type_(Type::NONE),
      constant_(0) {
}

ArithmeticFormula::~ArithmeticFormula() {
}

ArithmeticFormula::ArithmeticFormula(const ArithmeticFormula& other)
    : type_(other.type_),
      constant_(other.constant_) {
  this->variable_coefficient_map_ = other.variable_coefficient_map_;
}

ArithmeticFormula_ptr ArithmeticFormula::clone() const {
  return new ArithmeticFormula(*this);
}

std::string ArithmeticFormula::str() const {
  std::stringstream ss;

  for (auto& el : variable_coefficient_map_) {
    const int coefficient = el.second;
    if (coefficient > 0) {
      ss << " + ";
      if (coefficient > 1) {
        ss << coefficient;
      }
      ss << el.first;
    } else if (coefficient < 0) {
      ss << " - ";
      if (coefficient < -1) {
        ss << std::abs(coefficient);
      }
      ss << el.first;
    } else {
      if (type_ == Type::INTERSECT or type_ == Type::UNION) {
        ss << " " << el.first;
      }
    }
  }

  if (constant_ > 0) {
    ss << " + " << constant_;
  } else if (constant_ < 0) {
    ss << " - " << std::abs(constant_);
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

  ss << " " << 0;
  return ss.str();
}

void ArithmeticFormula::set_type(Type type) {
  this->type_ = type;
}

ArithmeticFormula::Type ArithmeticFormula::get_type() const {
  return type_;
}

int ArithmeticFormula::get_number_of_variables() const {
  return variable_coefficient_map_.size();
}

std::map<std::string, int> ArithmeticFormula::get_variable_coefficient_map() const {
  return variable_coefficient_map_;
}

void ArithmeticFormula::set_variable_coefficient_map(std::map<std::string, int>& coefficient_map) {
  variable_coefficient_map_ = coefficient_map;
}

int ArithmeticFormula::get_variable_coefficient(std::string variable_name) const {
  auto it = variable_coefficient_map_.find(variable_name);
  if (it == variable_coefficient_map_.end()) {
    LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  }
  return it->second;
}


void ArithmeticFormula::set_variable_coefficient(std::string variable_name, int coeff) {
  auto it = variable_coefficient_map_.find(variable_name);
  if (it == variable_coefficient_map_.end()) {
    LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  }
  it->second = coeff;
}

int ArithmeticFormula::get_constant() const {
  return constant_;
}

void ArithmeticFormula::set_constant(int constant) {
  this->constant_ = constant;
}

bool ArithmeticFormula::is_constant() const {
  for (const auto& el : variable_coefficient_map_) {
    if (el.second != 0) {
      return false;
    }
  }
  return true;
}

void ArithmeticFormula::reset_coefficients(int value) {
  for (auto& el : variable_coefficient_map_) {
    el.second = value;
  }
}

void ArithmeticFormula::add_variable(std::string name, int coefficient) {
  if(variable_coefficient_map_.find(name) != variable_coefficient_map_.end()) {
    LOG(FATAL) << "Variable has already been added! : " << name;
  }
  variable_coefficient_map_[name] = coefficient;
}

std::vector<int> ArithmeticFormula::get_coefficients() const {
  std::vector<int> coefficients;
  for (const auto& el : variable_coefficient_map_) {
    coefficients.push_back(el.second);
  }
  return coefficients;
}

int ArithmeticFormula::get_variable_index(std::string variable_name) const {
  auto it = variable_coefficient_map_.find(variable_name);
  if (it != variable_coefficient_map_.end()) {
    return std::distance(variable_coefficient_map_.begin(), it);
  }
  LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  return -1;
}

ArithmeticFormula_ptr ArithmeticFormula::Add(ArithmeticFormula_ptr other_formula) {
  auto result = new ArithmeticFormula(*this);

  for (const auto& el : other_formula->variable_coefficient_map_) {
    auto it = result->variable_coefficient_map_.find(el.first);
    if (it != result->variable_coefficient_map_.end()) {
      it->second = it->second + el.second;
    } else {
      result->variable_coefficient_map_.insert(el);
    }
  }
  result->constant_ = result->constant_ + other_formula->constant_;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::Subtract(ArithmeticFormula_ptr other_formula) {
  auto result = new ArithmeticFormula(*this);
  for (const auto& el : other_formula->variable_coefficient_map_) {
    auto it = result->variable_coefficient_map_.find(el.first);
    if (it != result->variable_coefficient_map_.end()) {
      it->second = it->second - el.second;
    } else {
      result->variable_coefficient_map_[el.first] = -el.second;
    }
  }
  result->constant_ = result->constant_ - other_formula->constant_;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::Multiply(int value) {
  auto result = new ArithmeticFormula(*this);
  for (auto& coeff : result->variable_coefficient_map_) {
    coeff.second = value * coeff.second;
  }
  result->constant_ = value * constant_;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::negate() {
  auto result = new ArithmeticFormula(*this);
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

/**
 * @returns false if formula is not satisfiable and catched by simplification
 */
bool ArithmeticFormula::Simplify() {
  if (variable_coefficient_map_.size() == 0) {
    return true;
  }

  int gcd_value = variable_coefficient_map_.begin()->second;

  for (const auto& el : variable_coefficient_map_) {
    gcd_value = Util::Math::gcd(gcd_value, el.second);
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
        constant_ = std::floor((double) constant_ / gcd_value);
      }
      break;
    }
    default:
      LOG(FATAL)<< "Simplification is only done after converting into '=' or '<' equation";
      break;
  }

  for (auto& c : variable_coefficient_map_) {
    c.second = c.second / gcd_value;
  }

  return true;
}

std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula) {
  return os << formula.str();
}

} /* namespace Theory */
} /* namespace Vlab */
