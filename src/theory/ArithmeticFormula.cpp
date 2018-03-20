/*
 * ArithmeticFormula.cpp
 *
 *  Created on: Oct 23, 2015
 *      Author: baki
 */

#include "ArithmeticFormula.h"

namespace Vlab
{
  namespace Theory
  {

    using namespace SMT;

    const int ArithmeticFormula::VLOG_LEVEL = 15;

    ArithmeticFormula::ArithmeticFormula()
        : type_(Type::NONE),
          constant_(0)
    {
    }

    ArithmeticFormula::~ArithmeticFormula()
    {
    }

    ArithmeticFormula::ArithmeticFormula(const ArithmeticFormula& other)
        : type_(other.type_),
          constant_(other.constant_)
    {
      this->variable_coefficient_map_ = other.variable_coefficient_map_;
      this->mixed_terms_ = other.mixed_terms_;
    }

    ArithmeticFormula_ptr ArithmeticFormula::clone() const
    {
      return new ArithmeticFormula(*this);
    }

    std::string ArithmeticFormula::str() const
    {
      std::stringstream ss;

      for (auto& el : variable_coefficient_map_)
      {
        const int coefficient = el.second;
        if (coefficient > 0)
        {
          ss << " + ";
          if (coefficient > 1)
          {
            ss << coefficient;
          }
          ss << el.first;
        }
        else if (coefficient < 0)
        {
          ss << " - ";
          if (coefficient < -1)
          {
            ss << std::abs(coefficient);
          }
          ss << el.first;
        }
        else
        {
          if (type_ == Type::INTERSECT or type_ == Type::UNION)
          {
            ss << " " << el.first;
          }
        }
      }

      if (constant_ > 0)
      {
        ss << " + " << constant_;
      }
      else if (constant_ < 0)
      {
        ss << " - " << std::abs(constant_);
      }

      ss << " ";

      switch (type_)
      {
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

    void ArithmeticFormula::set_type(Type type)
    {
      this->type_ = type;
    }

    ArithmeticFormula::Type ArithmeticFormula::get_type() const
    {
      return type_;
    }

    int ArithmeticFormula::get_number_of_variables() const
    {
      return variable_coefficient_map_.size();
    }

    std::map<std::string, int> ArithmeticFormula::get_variable_coefficient_map() const
    {
      return variable_coefficient_map_;
    }

    void ArithmeticFormula::set_variable_coefficient_map(std::map<std::string, int>& coefficient_map)
    {
      variable_coefficient_map_ = coefficient_map;
    }

    int ArithmeticFormula::get_variable_coefficient(std::string variable_name) const
    {
      auto it = variable_coefficient_map_.find(variable_name);
      if (it == variable_coefficient_map_.end())
      {
        LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
      }
      return it->second;
    }

    void ArithmeticFormula::set_variable_coefficient(std::string variable_name, int coeff)
    {
      auto it = variable_coefficient_map_.find(variable_name);
      if (it == variable_coefficient_map_.end())
      {
        LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
      }
      it->second = coeff;
    }

    int ArithmeticFormula::get_constant() const
    {
      return constant_;
    }

    void ArithmeticFormula::set_constant(int constant)
    {
      this->constant_ = constant;
    }

    bool ArithmeticFormula::is_constant() const
    {
      for (const auto& el : variable_coefficient_map_)
      {
        if (el.second != 0)
        {
          return false;
        }
      }
      return true;
    }

    void ArithmeticFormula::reset_coefficients(int value)
    {
      for (auto& el : variable_coefficient_map_)
      {
        el.second = value;
      }
    }

    void ArithmeticFormula::add_variable(std::string name, int coefficient)
    {
      if (variable_coefficient_map_.find(name) != variable_coefficient_map_.end())
      {
        LOG(FATAL)<< "Variable has already been added! : " << name;
      }
      variable_coefficient_map_[name] = coefficient;
    }

    std::vector<int> ArithmeticFormula::get_coefficients() const
    {
      std::vector<int> coefficients;
      for (const auto& el : variable_coefficient_map_)
      {
        coefficients.push_back(el.second);
      }
      return coefficients;
    }

    int ArithmeticFormula::get_variable_index(std::string variable_name) const
    {
      auto it = variable_coefficient_map_.find(variable_name);
      if (it != variable_coefficient_map_.end())
      {
        return std::distance(variable_coefficient_map_.begin(), it);
      }
      LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << *this;
      return -1;
    }

    std::string ArithmeticFormula::get_variable_at_index(const std::size_t index) const
    {
      if (index >= variable_coefficient_map_.size())
      {
        LOG(FATAL)<< "Index out of range";
      }
      auto it = variable_coefficient_map_.begin();
      std::advance(it, index);
      return it->first;
    }

    bool ArithmeticFormula::has_relation_to_mixed_term(const std::string var_name) const
    {
      auto it = mixed_terms_.find(var_name);
      return it != mixed_terms_.end();
    }

    void ArithmeticFormula::add_relation_to_mixed_term(const std::string var_name,
                                                       const ArithmeticFormula::Type relation, const Term_ptr term)
    {
      mixed_terms_[var_name] =
      { relation, term};
    }

    std::pair<ArithmeticFormula::Type, Term_ptr> ArithmeticFormula::get_relation_to_mixed_term(
        const std::string var_name) const
    {
      auto it = mixed_terms_.find(var_name);
      if (it == mixed_terms_.end())
      {
        LOG(FATAL)<< "Variable '" << var_name << "' does not have a relation to a mixed term";
      }
      return it->second;
    }

    bool ArithmeticFormula::UpdateMixedConstraintRelations()
    {
      if (mixed_terms_.empty())
      {
        return false;
      }
      std::string v1, v2;
      if (get_var_names_if_equality_of_two_vars(v1, v2))
      {
        auto it = mixed_terms_.find(v1);
        if (it == mixed_terms_.end())
        {
          auto rel_pair = mixed_terms_[v2];
          rel_pair.first = Type::EQ;
          mixed_terms_[v1] = rel_pair;
        }
        else
        {
          auto rel_pair = it->second;
          rel_pair.first = Type::EQ;
          mixed_terms_[v2] = rel_pair;
        }
        return true;
      }
      return false;
    }

    ArithmeticFormula_ptr ArithmeticFormula::Add(ArithmeticFormula_ptr other_formula)
    {
      auto result = new ArithmeticFormula(*this);

      for (const auto& el : other_formula->variable_coefficient_map_)
      {
        auto it = result->variable_coefficient_map_.find(el.first);
        if (it != result->variable_coefficient_map_.end())
        {
          it->second = it->second + el.second;
        }
        else
        {
          result->variable_coefficient_map_.insert(el);
        }
      }
      result->constant_ = result->constant_ + other_formula->constant_;

      result->mixed_terms_.insert(other_formula->mixed_terms_.begin(), other_formula->mixed_terms_.end());
      return result;
    }

    ArithmeticFormula_ptr ArithmeticFormula::Subtract(ArithmeticFormula_ptr other_formula)
    {
      auto result = new ArithmeticFormula(*this);
      for (const auto& el : other_formula->variable_coefficient_map_)
      {
        auto it = result->variable_coefficient_map_.find(el.first);
        if (it != result->variable_coefficient_map_.end())
        {
          it->second = it->second - el.second;
        }
        else
        {
          result->variable_coefficient_map_[el.first] = -el.second;
        }
      }
      result->constant_ = result->constant_ - other_formula->constant_;

      result->mixed_terms_.insert(other_formula->mixed_terms_.begin(), other_formula->mixed_terms_.end());
      return result;
    }

    ArithmeticFormula_ptr ArithmeticFormula::Multiply(int value)
    {
      auto result = new ArithmeticFormula(*this);
      for (auto& coeff : result->variable_coefficient_map_)
      {
        coeff.second = value * coeff.second;
      }
      result->constant_ = value * constant_;
      return result;
    }

    ArithmeticFormula_ptr ArithmeticFormula::negate()
    {
      auto result = new ArithmeticFormula(*this);
      switch (type_)
      {
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

    ArithmeticFormula_ptr ArithmeticFormula::ToConstantVariableFormula(const std::string var_name, const int value) const
    {
      ArithmeticFormula_ptr result = this->clone();
      result->reset_coefficients();
      result->set_variable_coefficient(var_name, 1);
      result->set_constant(-value);
      result->set_type(ArithmeticFormula::Type::EQ);
      return result;
    }

    ArithmeticFormula_ptr ArithmeticFormula::ToLessThanEquivalentFormula()
    {
      ArithmeticFormula_ptr result = nullptr;
      switch (type_)
      {
        case Type::EQ:
        case Type::NOTEQ:
          LOG(FATAL)<< "Call not supported for the current type.";
          break;
          case Type::GT:
          result = this->Multiply(-1);
          break;
          case Type::GE:
          result = this->Multiply(-1);
          result->set_constant(this->get_constant() - 1);
          break;
          case Type::LE:
          result = this->clone();
          result->set_constant(this->get_constant() - 1);
          break;
          case Type::LT:
          result = this->clone();
          break;
          default:
          break;
        }
      result->type_ = Type::LT;
      return result;
    }

    const ArithmeticFormula::CoefficientInfo ArithmeticFormula::GetCoefficientInfo() const
    {
      CoefficientInfo info;

      for (const auto& el : variable_coefficient_map_)
      {
        int c = el.second;
        info.coefficients_.push_back(el.second);
        if (c > 0)
        {
          info.maximum_sum_of_coefficients_ += c;
        }
        else if (c < 0)
        {
          info.minimum_sum_of_coefficients_ += c;
        }
        else
        {
          ++info.number_of_zero_coefficients_;
        }
      }

      if (info.maximum_sum_of_coefficients_ < this->constant_)
      {
        info.maximum_sum_of_coefficients_ = this->constant_;
      }
      else if (info.minimum_sum_of_coefficients_ > this->constant_)
      {
        info.minimum_sum_of_coefficients_ = this->constant_;
      }

      info.constant_ = this->constant_;
      return info;
    }

    /**
     * @returns false if formula is not satisfiable and catched by simplification
     */
    bool ArithmeticFormula::Simplify()
    {
      if (variable_coefficient_map_.size() == 0)
      {
        return true;
      }

      int gcd_value = variable_coefficient_map_.begin()->second;

      for (const auto& el : variable_coefficient_map_)
      {
        gcd_value = Util::Math::gcd(gcd_value, el.second);
      }

      if (gcd_value == 0)
      {
        return true;
      }

      switch (type_)
      {
        case Type::EQ:
        case Type::NOTEQ: {
          if (constant_ % gcd_value == 0)
          {
            constant_ = constant_ / gcd_value;
          }
          else
          {
            return false;
          }
          break;
        }
        case Type::LT: {
          if (constant_ >= 0)
          {
            constant_ = constant_ / gcd_value;
          }
          else
          {
            constant_ = std::floor((double) constant_ / gcd_value);
          }
          break;
        }
        default:
          LOG(FATAL)<< "Simplification is only done after converting into '=', '!=', or '<' equation";
          break;
        }

      for (auto& c : variable_coefficient_map_)
      {
        c.second = c.second / gcd_value;
      }

      return true;
    }

    int ArithmeticFormula::CountOnes(unsigned long n) const
    {
      int ones = 0;
      for (const auto& el : variable_coefficient_map_)
      {
        if (el.second != 0)
        {
          if (n & 1)
          {
            ones += el.second;
          }
          n >>= 1;
        }
      }
      return ones;
    }

    void ArithmeticFormula::merge_variables(const ArithmeticFormula_ptr other)
    {
      for (auto& el : other->variable_coefficient_map_)
      {
        if (variable_coefficient_map_.find(el.first) == variable_coefficient_map_.end())
        {
          variable_coefficient_map_[el.first] = 0;
        }
      }
      mixed_terms_.insert(other->mixed_terms_.begin(), other->mixed_terms_.end());
    }

    bool ArithmeticFormula::get_var_names_if_equality_of_two_vars(std::string &v1, std::string &v2)
    {
      if (type_ not_eq Type::EQ)
      {
        return false;
      }
      v1.clear();
      v2.clear();
      int active_vars = 0;
      for (auto& el : variable_coefficient_map_)
      {
        if (el.second != 0)
        {
          ++active_vars;
          if (el.second == 1)
          {
            v1 = el.first;
          }
          else if (el.second == -1)
          {
            v2 = el.first;
          }
          if (active_vars > 2)
          {
            return false;
          }
        }
      }

      return ((active_vars == 2) and !v1.empty() and !v2.empty());
    }

    std::ostream& operator<<(std::ostream& os, const ArithmeticFormula& formula)
    {
      return os << formula.str();
    }

  } /* namespace Theory */
} /* namespace Vlab */
