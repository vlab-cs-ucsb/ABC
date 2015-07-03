/*
 * Value.cpp
 *
 *  Created on: Jul 1, 2015
 *      Author: baki
 */

#include "Value.h"

namespace Vlab {
namespace Solver {

const int Value::VLOG_LEVEL = 15;

const std::string Value::Name::NONE = "none";
const std::string Value::Name::BOOL_CONSTANT = "Bool Constant";
const std::string Value::Name::INT_CONSTANT = "Int Constant";
const std::string Value::Name::STRING_CONSTANT = "String Constant";
const std::string Value::Name::BOOL_AUTOMATON = "Bool Automaton";
const std::string Value::Name::INT_AUTOMATON = "Int Automaton";
const std::string Value::Name::INTBOOL_AUTOMATON = "IntBool Automaton";
const std::string Value::Name::STRING_AUTOMATON = "String Automaton";

Value::Value()
        : type(Type::NONE) {
}

Value::Value(Type type, bool data)
        : type(type), bool_constant(data) {
}

Value::Value(Type type, int data)
        : type(type), int_constant(data) {
}

Value::Value(Type type, Theory::BoolAutomaton_ptr data)
        : type(type), bool_automaton(data) {
}

Value::Value(Type type, Theory::IntAutomaton_ptr data)
        : type(type), int_automaton(data) {
}

Value::Value(Type type, Theory::IntBoolAutomaton_ptr data)
        : type(type), intbool_automaton(data) {
}

Value::Value(Type type, Theory::StringAutomaton_ptr data)
        : type(type), string_automaton(data) {
}

Value::Value(const Value& other)
        : type(other.type) {
  switch (other.type) {
  case Type::NONE:
    break;
  case Type::BOOl_CONSTANT:
    bool_constant = other.bool_constant;
    break;
  case Type::INT_CONSTANT:
    int_constant = other.int_constant;
    break;
  case Type::BOOL_AUTOMATON:
    bool_automaton = other.bool_automaton->clone();
    break;
  case Type::INT_AUTOMATON:
    int_automaton = other.int_automaton->clone();
    break;
  case Type::INTBOOL_AUTOMATON:
    intbool_automaton = other.intbool_automaton->clone();
    break;
  case Type::STRING_AUTOMATON:
    string_automaton = other.string_automaton->clone();
    break;
  default:
    LOG(FATAL) << "value type is not supported";
    break;
  }
}

Value_ptr Value::clone() const {
  return new Value(*this);
}

Value::~Value() {
  switch (type) {
  case Type::BOOL_AUTOMATON:
    delete bool_automaton; bool_automaton = nullptr;
    break;
  case Type::INT_AUTOMATON:
    delete int_automaton; int_automaton = nullptr;
    break;
  case Type::INTBOOL_AUTOMATON:
    delete intbool_automaton; intbool_automaton = nullptr;
    break;
  case Type::STRING_AUTOMATON:
    delete string_automaton; string_automaton = nullptr;
    break;
  default:
    break;
  }
}

  std::string  Value::str() const {
    std::stringstream ss;

    switch (type) {
    case Type::NONE:
      ss << Name::NONE;
      break;
    case Type::BOOl_CONSTANT:
      ss << Name::BOOL_CONSTANT << " : " << bool_constant;
      break;
    case Type::INT_CONSTANT:
      ss << Name::INT_CONSTANT << " : " << int_constant;
      break;
    case Type::BOOL_AUTOMATON:
      ss << Name::BOOL_AUTOMATON << " : " << " please print automaton";
      break;
    case Type::INT_AUTOMATON:
      ss << Name::INT_AUTOMATON << " : " << " please print automaton";
      break;
    case Type::INTBOOL_AUTOMATON:
      ss << Name::INTBOOL_AUTOMATON << " : " << " please print automaton";
      break;
    case Type::STRING_AUTOMATON:
      ss << Name::STRING_AUTOMATON << " : " << " please print automaton";
      break;
    default:
      LOG(FATAL) << "value type is not supported";
      break;
    }

    return ss.str();
  }

  void Value::setType(Type type) {
    this->type = type;
  }

  Value::Type  Value::getType()  const {
    return type;
  }

  void Value::set(bool data) {
    bool_constant = data;
  }

  void Value::set(int data) {
    int_constant = data;
  }

  void Value::set(Theory::BoolAutomaton_ptr data) {
    bool_automaton = data;
  }

  void Value::set(Theory::IntAutomaton_ptr data) {
    int_automaton = data;
  }

  void Value::set(Theory::IntBoolAutomaton_ptr data) {
    intbool_automaton = data;
  }

  void Value::set(Theory::StringAutomaton_ptr data) {
    string_automaton = data;
  }

  bool Value::getBoolConstant() const {
    return bool_constant;
  }

  int Value::getIntConstant() const {
    return int_constant;
  }

  Theory::BoolAutomaton_ptr Value::getBoolAutomaton() const {
    return bool_automaton;
  }

  Theory::IntAutomaton_ptr Value::getIntAutomaton() const {
    return int_automaton;
  }

  Theory::IntBoolAutomaton_ptr Value::getIntBoolAutomaton() const {
    return intbool_automaton;
  }

  Theory::StringAutomaton_ptr Value::getStringAutomaton() const {
    return string_automaton;
  }

  Value_ptr Value::union_(Value_ptr other_value) const {
    Value_ptr union_value = nullptr;
    LOG(FATAL) << "implement me";
    return union_value;
  }

  Value_ptr Value::intersect(Value_ptr other_value) const {
    Value_ptr intersection_value = nullptr;
    LOG(FATAL) << "implement me";
    // here handle the case where one side is constant and the other side is automaton
    return intersection_value;
  }

  bool Value::isSatisfiable() {
    bool is_satisfiable = false;
    switch (type) {
    case Type::NONE:
      break;
    case Type::BOOl_CONSTANT:
      is_satisfiable = bool_constant;
      break;
    case Type::INT_CONSTANT:
      is_satisfiable = true;
      break;
    case Type::BOOL_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    case Type::INT_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    case Type::INTBOOL_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    case Type::STRING_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    default:
      LOG(FATAL) << "value type is not supported";
      break;
    }
    return is_satisfiable;
  }

  std::ostream& operator<<(std::ostream& os, const Value& value) {
    return os << value.str();
  }

} /* namespace Solver */
} /* namespace Vlab */

