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
  this->trackmap_handle_ = other.trackmap_handle_;
  this->var_coeff_map_ = other.var_coeff_map_;
  this->coefficients_ = other.coefficients_;
}

ArithmeticFormula_ptr ArithmeticFormula::clone() const {
  return new ArithmeticFormula(*this);
}

std::string ArithmeticFormula::str() const {
  std::stringstream ss;
  std::vector<std::string> variable_names(trackmap_handle_.size(),"");

  auto char_remover = []( char ch ) {
    return std::isspace<char>( ch, std::locale::classic() ) or ch == '"' or ch == ';';
  };

  for (auto& pair : var_coeff_map_) {
    std::string name = pair.first;
    if (pair.first.find("len") != std::string::npos) {
      name = "len_term";
    } else if (pair.first.find("lastIndexOf") != std::string::npos or pair.first.find("indexOf") != std::string::npos) {
      name = "index_term";
    }
    variable_names[get_variable_index(name)] = name;
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
    for (auto& pair : var_coeff_map_) {
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
  if(trackmap_handle_.empty()) {
    return var_coeff_map_.size();
  } else {
    return trackmap_handle_.size();
  }
}

std::map<std::string, int>& ArithmeticFormula::get_var_coeff_map() {
  return var_coeff_map_;
}

int ArithmeticFormula::get_variable_index(std::string variable_name) const {
  auto it = trackmap_handle_.find(variable_name);
  if (it != trackmap_handle_.end()) {
    return it->second;
  }
  LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
  return -1;
}

int ArithmeticFormula::get_variable_coefficient(std::string variable_name) {
  auto iter = var_coeff_map_.find(variable_name);
  if (iter == var_coeff_map_.end()) {
    return 0;
  }
  return iter->second;
}

void ArithmeticFormula::set_variable_coefficient(std::string variable_name, int coeff) {
  var_coeff_map_[variable_name] = coeff;
}

int ArithmeticFormula::get_constant() {
  return constant_;
}

void ArithmeticFormula::set_constant(int constant) {
  this->constant_ = constant;
}

bool ArithmeticFormula::is_constant() {
  for (auto& coeff : var_coeff_map_) {
    if (coeff.second != 0) {
      return false;
    }
  }
  return true;
}

void ArithmeticFormula::reset_coefficients(int value) {
  for (auto& c : var_coeff_map_) {
    c.second = value;
  }
  create_coeff_vec();
}

void ArithmeticFormula::add_variable(std::string name, int coefficient) {
  if(var_coeff_map_.find(name) != var_coeff_map_.end()) {
    LOG(FATAL) << "Variable has already been added yo!";
  }
  var_coeff_map_[name] = coefficient;
}

std::map<std::string, int> ArithmeticFormula::get_variable_trackmap() {
  return this->trackmap_handle_;
}

void ArithmeticFormula::set_variable_trackmap(std::map<std::string, int> trackmap) {
  this->trackmap_handle_ = trackmap;
  create_coeff_vec();
}

void ArithmeticFormula::create_coeff_vec() {
  coefficients_ = std::vector<int>(trackmap_handle_.size(),0);
  for(auto it : var_coeff_map_) {
    int track = trackmap_handle_[it.first];
    coefficients_[track] = it.second;
  }
}

std::vector<int> ArithmeticFormula::get_coefficients() {
  return coefficients_;
}

ArithmeticFormula_ptr ArithmeticFormula::Subtract(ArithmeticFormula_ptr other_formula) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);

  for (auto& pair : other_formula->var_coeff_map_) {
    auto it = result->var_coeff_map_.find(pair.first);
    if (it != result->var_coeff_map_.end()) {
      result->var_coeff_map_[it->first] = result->var_coeff_map_[it->first] - other_formula->var_coeff_map_[pair.first];
    } else {
      result->var_coeff_map_[pair.first] = -1 * pair.second;
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
  for (auto& coeff : result->var_coeff_map_) {
    coeff.second = value * coeff.second;
  }
  result->constant_ = value * constant_;
  return result;
}

ArithmeticFormula_ptr ArithmeticFormula::Add(ArithmeticFormula_ptr other_formula) {
  ArithmeticFormula_ptr result = new ArithmeticFormula(*this);

  for (auto& pair : other_formula->var_coeff_map_) {
    auto it = result->var_coeff_map_.find(pair.first);
    if (it != result->var_coeff_map_.end()) {
      result->var_coeff_map_[it->first] = result->var_coeff_map_[it->first] + other_formula->var_coeff_map_[pair.first];
    } else {
      result->var_coeff_map_.insert(pair);
    }
  }
  result->constant_ = result->constant_ + other_formula->constant_;
  return result;
}

/**
 * @returns false if formula is not satisfiable and catched by simplification
 */
bool ArithmeticFormula::Simplify() {
  if (var_coeff_map_.size() == 0) {
    LOG(INFO) << "Returning!";
    return true;
  }

  int gcd_value = var_coeff_map_.begin()->second;

  for (auto c : var_coeff_map_) {
    gcd_value = Util::Math::gcd(gcd_value, c.second);
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

  for (auto& c : var_coeff_map_) {
    c.second = c.second / gcd_value;
  }

  create_coeff_vec();

  return true;
}

std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula) {
  return os << formula.str();
}

} /* namespace Theory */
} /* namespace Vlab */
