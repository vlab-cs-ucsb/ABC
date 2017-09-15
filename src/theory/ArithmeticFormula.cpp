/*
 * ArithmeticFormula.cpp
 *
 *  Created on: Oct 23, 2015
 *      Author: baki
 */

#include "ArithmeticFormula.h"

namespace Vlab {
namespace Theory {

using namespace SMT;

const int ArithmeticFormula::VLOG_LEVEL = 15;

ArithmeticFormula::ArithmeticFormula()
    : type_(Type::NONE),
      constant_(0) {
}

ArithmeticFormula::~ArithmeticFormula() {
}

ArithmeticFormula::ArithmeticFormula(const ArithmeticFormula& other)
    : Formula(other),
    	type_(other.type_),
      constant_(other.constant_) {
  this->variable_coefficient_map_ = other.variable_coefficient_map_;
  this->boolean_variable_value_map_ = other.boolean_variable_value_map_;
  this->mixed_terms_ = other.mixed_terms_;
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

ArithmeticFormula_ptr ArithmeticFormula::Intersect(Formula_ptr other) {
	ArithmeticFormula_ptr intersect_formula = this->clone();
	intersect_formula->ResetCoefficients(0);
	intersect_formula->SetType(ArithmeticFormula::Type::INTERSECT);
	return intersect_formula;
}

ArithmeticFormula_ptr ArithmeticFormula::Union(Formula_ptr other) {
	ArithmeticFormula_ptr union_formula = this->clone();
	union_formula->ResetCoefficients(0);
	union_formula->SetType(ArithmeticFormula::Type::UNION);
	return union_formula;
}

ArithmeticFormula_ptr ArithmeticFormula::Complement() {
	ArithmeticFormula_ptr result = this->clone();
	switch (result->type_) {
		case ArithmeticFormula::Type::EQ:
			result->type_ = ArithmeticFormula::Type::NOTEQ;
			break;
		case ArithmeticFormula::Type::NOTEQ:
			result->type_ = ArithmeticFormula::Type::EQ;
			break;
		case ArithmeticFormula::Type::GT:
			result->type_ = ArithmeticFormula::Type::LE;
			break;
		case ArithmeticFormula::Type::GE:
			result->type_ = ArithmeticFormula::Type::LT;
			break;
		case ArithmeticFormula::Type::LT:
			result->type_ = ArithmeticFormula::Type::GE;
			break;
		case ArithmeticFormula::Type::LE:
			result->type_ = ArithmeticFormula::Type::GT;
			break;
		default:
			break;
	}
	return result;
}

void ArithmeticFormula::AddBoolean(std::string name) {
	if(boolean_variable_value_map_.find(name) != boolean_variable_value_map_.end()) {
		LOG(FATAL) << "Boolean has already been added! : " << name;
	}
	boolean_variable_value_map_[name] = true;
}

std::map<std::string,bool> ArithmeticFormula::GetBooleans() const {
	return boolean_variable_value_map_;
}


void ArithmeticFormula::SetType(Type type) {
  this->type_ = type;
}

ArithmeticFormula::Type ArithmeticFormula::GetType() const {
  return type_;
}

int ArithmeticFormula::GetConstant() const {
  return constant_;
}

void ArithmeticFormula::SetConstant(int constant) {
  this->constant_ = constant;
}

bool ArithmeticFormula::IsConstant() const {
  for (const auto& el : variable_coefficient_map_) {
    if (el.second != 0) {
      return false;
    }
  }
  return true;
}

bool ArithmeticFormula::HasRelationToMixedTerm(const std::string var_name) const {
  auto it = mixed_terms_.find(var_name);
  return it != mixed_terms_.end();
}

void ArithmeticFormula::AddRelationToMixedTerm(const std::string var_name, const ArithmeticFormula::Type relation, const Term_ptr term) {
  mixed_terms_[var_name] = {relation, term};
}

std::pair<ArithmeticFormula::Type, Term_ptr> ArithmeticFormula::GetRelationToMixedTerm(const std::string var_name) const {
  auto it = mixed_terms_.find(var_name);
  if (it == mixed_terms_.end()) {
    LOG(FATAL) << "Variable '" << var_name << "' does not have a relation to a mixed term";
  }
  return it->second;
}

bool ArithmeticFormula::UpdateMixedConstraintRelations() {
  if (mixed_terms_.empty()) {
    return false;
  }
  std::string v1, v2;
  if (GetVarNamesIfEqualityOfTwoVars(v1, v2)) {
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

  result->mixed_terms_.insert(other_formula->mixed_terms_.begin(), other_formula->mixed_terms_.end());
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

  result->mixed_terms_.insert(other_formula->mixed_terms_.begin(), other_formula->mixed_terms_.end());
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
    case Type::BOOL: {
			// should be reachable only if var is bool
			if(result->boolean_variable_value_map_.size() != 1) {
				LOG(FATAL) << "can't negate variable! dont know how";
			}
			auto it = result->boolean_variable_value_map_.begin();
			result->boolean_variable_value_map_[it->first] = !result->boolean_variable_value_map_[it->first];
			break;
		}
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
    case Type::EQ:
    case Type::NOTEQ: {
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
      LOG(FATAL)<< "Simplification is only done after converting into '=', '!=', or '<' equation";
      break;
    }

  for (auto& c : variable_coefficient_map_) {
    c.second = c.second / gcd_value;
  }

  return true;
}

int ArithmeticFormula::CountOnes(unsigned long n) const {
  int ones = 0;
  for (const auto& el : variable_coefficient_map_) {
    if (el.second != 0) {
      if (n & 1) {
        ones += el.second;
      }
      n >>= 1;
    }
  }
  return ones;
}

void ArithmeticFormula::MergeVariables(Formula_ptr formula) {
	auto other = static_cast<ArithmeticFormula_ptr>(formula);

	if(other == nullptr) {
		LOG(FATAL) << "failed cast in MergeVariables, both not arithmetic formulas";
	}

  for (auto& el : other->variable_coefficient_map_) {
    if (variable_coefficient_map_.find(el.first) == variable_coefficient_map_.end()) {
      variable_coefficient_map_[el.first] = 0;
    }
  }
  mixed_terms_.insert(other->mixed_terms_.begin(), other->mixed_terms_.end());
}

bool ArithmeticFormula::GetVarNamesIfEqualityOfTwoVars(std::string &v1, std::string &v2) {
  if (type_ not_eq Type::EQ) {
    return false;
  }
  v1.clear();
  v2.clear();
  int active_vars = 0;
  for (auto& el : variable_coefficient_map_) {
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

std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula) {
  return os << formula.str();
}

} /* namespace Theory */
} /* namespace Vlab */
