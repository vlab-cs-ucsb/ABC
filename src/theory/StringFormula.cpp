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
    : type_(Type::NONE) {
}

StringFormula::~StringFormula() {
}

StringFormula::StringFormula(const StringFormula& other)
    : Formula(other),
    	type_(other.type_),
      constant_(other.constant_),
      constant2_(other.constant2_) {
  this->mixed_terms_ = other.mixed_terms_;
}

StringFormula_ptr StringFormula::clone() const {
  return new StringFormula(*this);
}

std::string StringFormula::str() const {
  std::stringstream ss;

  for (auto& el : variable_coefficient_map_) {
    const int coefficient = el.second;
    if (coefficient > 0) {
      ss << "(";
      ss << coefficient;
      ss << ",";
      ss << el.first;
      ss << ") ";
    } else if (type_ == Type::INTERSECT or type_ == Type::UNION) {
      ss << el.first << " " ;
    }
  }

  ss << constant_ << " - ";
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
    case Type::DIFFERENCE:
      ss << "diff";
      break;
    case Type::STRING_CONSTANT:
      ss << "string const";
      break;
    case Type::REGEX_CONSTANT:
      ss << "re.const";
      break;
    case Type::INTEGER_CONSTANT:
      ss << "integer constant";
      break;
    case Type::EQ_NO_LAMBDA:
      ss << "= no lambda";
      break;
    case Type::EQ_ONLY_LAMBDA:
      ss << "= eq only lambda";
      break;
    case Type::BEGINS:
      ss << "begins";
      break;
    case Type::NOTBEGINS:
      ss << "!begins";
      break;
    case Type::CONCAT_VAR_CONSTANT:
      ss << "concat var const";
      break;
    case Type::NONRELATIONAL:
      ss << "non-relational";
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
    case Type::CHARAT:
      ss << "charAt";
      break;
    case Type::EQ_CHARAT:
      ss << "= charAt";
      break;
    case Type::NOTEQ_CHARAT:
      ss << "!= charAt";
      break;
    default:
      ss << "none";
      break;
  }

  ss << ".";
  return ss.str();
}

StringFormula_ptr StringFormula::Intersect(Formula_ptr other) {
	StringFormula_ptr intersect_formula = this->clone();
	//intersect_formula->MergeVariables(other);
	intersect_formula->ResetCoefficients(0);
	intersect_formula->SetType(StringFormula::Type::INTERSECT);
	return intersect_formula;
}

StringFormula_ptr StringFormula::Union(Formula_ptr other) {
	StringFormula_ptr union_formula = this->clone();
	//union_formula->MergeVariables(other);
	union_formula->ResetCoefficients(0);
	union_formula->SetType(StringFormula::Type::UNION);
	return union_formula;
}

StringFormula_ptr StringFormula::Complement() {
	StringFormula_ptr result = this->clone();
	switch (result->type_) {
		case StringFormula::Type::EQ:
			result->type_ = StringFormula::Type::NOTEQ;
			break;
		case StringFormula::Type::NOTEQ:
			result->type_ = StringFormula::Type::EQ;
			break;
		case StringFormula::Type::GT:
			result->type_ = StringFormula::Type::LE;
			break;
		case StringFormula::Type::GE:
			result->type_ = StringFormula::Type::LT;
			break;
		case StringFormula::Type::LT:
			result->type_ = StringFormula::Type::GE;
			break;
		case StringFormula::Type::LE:
			result->type_ = StringFormula::Type::GT;
			break;
    case StringFormula::Type::EQ_CHARAT:
      result->type_ = StringFormula::Type::NOTEQ_CHARAT;
      break;
    case StringFormula::Type::NOTEQ_CHARAT:
      result->type_ = StringFormula::Type::EQ_CHARAT;
		default:
			break;
	}
	return result;
}

void StringFormula::SetType(Type type) {
  this->type_ = type;
}

StringFormula::Type StringFormula::GetType() const {
  return type_;
}

std::string StringFormula::GetConstant() const {
  return constant_;
}

std::string StringFormula::GetConstant2() const {
  return constant2_;
}

void StringFormula::SetConstant(std::string constant) {
  this->constant_ = constant;
}

void StringFormula::SetConstant2(std::string constant) {
  this->constant2_ = constant;
}

bool StringFormula::IsConstant() const {
  for (const auto& el : variable_coefficient_map_) {
    if (el.second != 0) {
      return false;
    }
  }
  return true;
}

bool StringFormula::HasRelationToMixedTerm(const std::string var_name) const {
  auto it = mixed_terms_.find(var_name);
  return it != mixed_terms_.end();
}

void StringFormula::AddRelationToMixedTerm(const std::string var_name, const StringFormula::Type relation, const Term_ptr term) {
  mixed_terms_[var_name] = {relation, term};
}

std::pair<StringFormula::Type, Term_ptr> StringFormula::GetRelationToMixedTerm(const std::string var_name) const {
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

int StringFormula::CountOnes(unsigned long n) const {
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

void StringFormula::MergeVariables(Formula_ptr other) {
  if(other == nullptr) {
    return;
  }
  for (auto& el : other->GetVariableCoefficientMap()) {
    if (variable_coefficient_map_.find(el.first) == variable_coefficient_map_.end()) {
      variable_coefficient_map_[el.first] = 0;
    }
  }
}

bool StringFormula::GetVarNamesIfEqualityOfTwoVars(std::string &v1, std::string &v2) {
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

std::ostream& operator<<(std::ostream& os, const StringFormula& formula) {
  return os << formula.str();
}

} /* namespace Theory */
} /* namespace Vlab */
