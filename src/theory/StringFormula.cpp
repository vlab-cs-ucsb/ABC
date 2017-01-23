/*
 * StringFormula.cpp
 *
 *  Created on: Jan 22, 2017
 *      Author: baki
 */

#include "StringFormula.h"

namespace Vlab {
namespace Theory {

using namespace SMT;


const int StringFormula::VLOG_LEVEL = 15;

StringFormula::StringFormula()
    : type_(Type::NONE),
      constant_(0) {
}

StringFormula::~StringFormula() {
}

StringFormula::StringFormula(const StringFormula& other)
    : type_(other.type_),
      constant_(other.constant_) {
  this->variable_order_map_ = other.variable_order_map_;
  this->mixed_terms_ = other.mixed_terms_;
}

StringFormula_ptr StringFormula::clone() const {
  return new StringFormula(*this);
}

std::string StringFormula::str() const {
  std::stringstream ss;

  for (auto& el : variable_order_map_) {
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

//  if (constant_ > 0) {
//    ss << " + " << constant_;
//  } else if (constant_ < 0) {
//    ss << " - " << std::abs(constant_);
//  }

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

void StringFormula::set_type(Type type) {
  this->type_ = type;
}

StringFormula::Type StringFormula::get_type() const {
  return type_;
}

int StringFormula::get_number_of_variables() const {
  return variable_order_map_.size();
}

std::map<std::string, int> StringFormula::get_variable_coefficient_map() const {
  return variable_order_map_;
}

void StringFormula::set_variable_coefficient_map(std::map<std::string, int>& coefficient_map) {
  variable_order_map_ = coefficient_map;
}

int StringFormula::get_variable_coefficient(std::string variable_name) const {
  auto it = variable_order_map_.find(variable_name);
  if (it == variable_order_map_.end()) {
    LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  }
  return it->second;
}

void StringFormula::set_variable_coefficient(std::string variable_name, int coeff) {
  auto it = variable_order_map_.find(variable_name);
  if (it == variable_order_map_.end()) {
    LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  }
  it->second = coeff;
}

std::string StringFormula::get_constant() const {
  return constant_;
}

void StringFormula::set_constant(std::string constant) {
  this->constant_ = constant;
}

bool StringFormula::is_constant() const {
  for (const auto& el : variable_order_map_) {
    if (el.second != 0) {
      return false;
    }
  }
  return true;
}

void StringFormula::reset_param_orders(int value) {
  for (auto& el : variable_order_map_) {
    el.second = value;
  }
}

void StringFormula::add_variable(std::string name, int position) {
  if (variable_order_map_.find(name) != variable_order_map_.end()) {
    LOG(FATAL)<< "Variable has already been added! : " << name;
  }
  variable_order_map_[name] = position;
}

std::vector<int> StringFormula::get_coefficients() const {
  std::vector<int> coefficients;
  for (const auto& el : variable_order_map_) {
    coefficients.push_back(el.second);
  }
  return coefficients;
}

int StringFormula::get_variable_index(const std::string variable_name) const {
  auto it = variable_order_map_.find(variable_name);
  if (it != variable_order_map_.end()) {
    return std::distance(variable_order_map_.begin(), it);
  }
  LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  return -1;
}

int StringFormula::get_variable_index(const int param_index) const {
  for (auto it = variable_order_map_.begin(); it != variable_order_map_.end(); ++it) {
    if (it->second == param_index) {
      return std::distance(variable_order_map_.begin(), it);
    }
  }

  LOG(FATAL)<< "Formula does not have param: " << param_index << ", " << *this;
  return -1;
}

bool StringFormula::has_relation_to_mixed_term(const std::string var_name) const {
  auto it = mixed_terms_.find(var_name);
  return it != mixed_terms_.end();
}

void StringFormula::add_relation_to_mixed_term(const std::string var_name, const StringFormula::Type relation, const Term_ptr term) {
  mixed_terms_[var_name] = {relation, term};
}

std::pair<StringFormula::Type, Term_ptr> StringFormula::get_relation_to_mixed_term(const std::string var_name) const {
  auto it = mixed_terms_.find(var_name);
  if (it == mixed_terms_.end()) {
    LOG(FATAL) << "Variable '" << var_name << "' does not have a relation to a mixed term";
  }
  return it->second;
}

bool StringFormula::UpdateMixedConstraintRelations() {
  if (mixed_terms_.empty()) {
    return false;
  }
  std::string v1, v2;
  if (get_var_names_if_equality_of_two_vars(v1, v2)) {
    auto it = mixed_terms_.find(v1);
    if (it == mixed_terms_.end()) {
      auto rel_pair = mixed_terms_[v2];
      rel_pair.first = Type::EQ;
      mixed_terms_[v1] = rel_pair;
    } else {
      auto rel_pair = it->second;
      rel_pair.first = Type::EQ;
      mixed_terms_[v2] = rel_pair;
    }
    return true;
  }
  return false;
}

StringFormula_ptr StringFormula::Add(StringFormula_ptr other_formula) {
  auto result = new StringFormula(*this);
//
//  for (const auto& el : other_formula->variable_order_map_) {
//    auto it = result->variable_order_map_.find(el.first);
//    if (it != result->variable_order_map_.end()) {
//      it->second = it->second + el.second;
//    } else {
//      result->variable_order_map_.insert(el);
//    }
//  }
//  result->constant_ = result->constant_ + other_formula->constant_;
//
//  result->mixed_terms_.insert(other_formula->mixed_terms_.begin(), other_formula->mixed_terms_.end());
  return result;
}

StringFormula_ptr StringFormula::Subtract(StringFormula_ptr other_formula) {
  auto result = new StringFormula(*this);
//  for (const auto& el : other_formula->variable_order_map_) {
//    auto it = result->variable_order_map_.find(el.first);
//    if (it != result->variable_order_map_.end()) {
//      it->second = it->second - el.second;
//    } else {
//      result->variable_order_map_[el.first] = -el.second;
//    }
//  }
//  result->constant_ = result->constant_ - other_formula->constant_;
//
//  result->mixed_terms_.insert(other_formula->mixed_terms_.begin(), other_formula->mixed_terms_.end());
  return result;
}

StringFormula_ptr StringFormula::Multiply(int value) {
  auto result = new StringFormula(*this);
//  for (auto& coeff : result->variable_order_map_) {
//    coeff.second = value * coeff.second;
//  }
//  result->constant_ = value * constant_;
  return result;
}

StringFormula_ptr StringFormula::negate() {
  auto result = new StringFormula(*this);
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
bool StringFormula::Simplify() {
  if (variable_order_map_.size() == 0) {
    return true;
  }

  return true;
}

int StringFormula::CountOnes(unsigned long n) const {
  int ones = 0;
  for (const auto& el : variable_order_map_) {
    if (el.second != 0) {
      if (n & 1) {
        ones += el.second;
      }
      n >>= 1;
    }
  }
  return ones;
}

void StringFormula::merge_variables(const StringFormula_ptr other) {
  for (auto& el : other->variable_order_map_) {
    if (variable_order_map_.find(el.first) == variable_order_map_.end()) {
      variable_order_map_[el.first] = 0;
    }
  }
}

bool StringFormula::get_var_names_if_equality_of_two_vars(std::string &v1, std::string &v2) {
  if (type_ not_eq Type::EQ) {
    return false;
  }
  v1.clear();
  v2.clear();
  int active_vars = 0;
  for (auto& el : variable_order_map_) {
    if (el.second != 0) {
      ++active_vars;
      if (el.second == 1) {
        v1 = el.first;
      } else if (el.second == -1) {
        v2 = el.first;
      }
      if (active_vars > 2) {
        return false;
      }
    }
  }

  return ((active_vars == 2) and !v1.empty() and !v2.empty());
}

std::ostream& operator<<(std::ostream& os, const StringFormula& formula) {
  return os << formula.str();
}

} /* namespace Theory */
} /* namespace Vlab */
