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
    if (Type::STRING_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
      intersection_value = new Value(Type::STRING_AUTOMATON,
          string_automaton->intersect(other_value->string_automaton));
    } else if (Type::INT_AUTOMATON == type and Type::INT_AUTOMATON == other_value->type) {
      intersection_value = new Value(Type::INT_AUTOMATON,
          int_automaton->intersect(other_value->int_automaton));
    } else if (Type::INT_CONSTANT == type and Type::INT_CONSTANT == other_value->type) {
      if (this->int_constant == other_value->int_constant) {
        intersection_value = this->clone();
      } else {
        intersection_value = new Value(Type::INT_AUTOMATON, Theory::IntAutomaton::makePhi());
      }
    } else if (Type::INT_CONSTANT == type and Type::INT_AUTOMATON == other_value->type) {
      intersection_value = new Value(Value::Type::INT_AUTOMATON,
              other_value->int_automaton->intersect(int_constant));
    } else if (Type::INT_AUTOMATON == type and Type::INT_CONSTANT == other_value->type) {
      intersection_value = new Value(Value::Type::INT_AUTOMATON,
              int_automaton->intersect(other_value->int_constant));
    } else {
      LOG(FATAL) << "cannot intersect types (implement me): " << *this << " & " << *other_value;
    }
    return intersection_value;
  }

  Value_ptr Value::complement() const {
    Value_ptr complement_value = nullptr;
    switch (type) {
      case Type::STRING_AUTOMATON : {
        complement_value = new Value(Type::STRING_AUTOMATON,
                string_automaton->complement());
        break;
      }
      case Type::INT_AUTOMATON : {
        complement_value = new Value(Type::INT_AUTOMATON,
                int_automaton->complement());
        break;
      }
      case Type::INT_CONSTANT : {
        Theory::IntAutomaton_ptr int_auto = Theory::IntAutomaton::makeInt(int_constant);
        complement_value = new Value(Type::INT_AUTOMATON,
                int_auto->complement());
        delete int_auto;
        break;
      }
      case Type::BOOl_CONSTANT : {
        complement_value = new Value(Type::BOOl_CONSTANT,
                not bool_constant);
        break;
      }
      default:
        LOG(FATAL) << "implement me" << *this;
        break;
    }
    return complement_value;
  }

  Value_ptr Value::difference(Value_ptr other_value) const {
    Value_ptr difference_value = nullptr;
    if (Type::STRING_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
      difference_value = new Value(Type::STRING_AUTOMATON,
          string_automaton->difference(other_value->string_automaton));
    } else if (Type::INT_AUTOMATON == type and Type::INT_AUTOMATON == other_value->type) {
      difference_value = new Value(Type::INT_AUTOMATON,
          int_automaton->difference(other_value->int_automaton));
    } else if (Type::INT_CONSTANT == type and Type::INT_CONSTANT == other_value->type) {
      if (this->int_constant != other_value->int_constant) {
        difference_value = this->clone();
      } else {
        difference_value = new Value(Type::INT_AUTOMATON, Theory::IntAutomaton::makePhi());
      }
    } else if (Type::INT_CONSTANT == type and Type::INT_AUTOMATON == other_value->type) {
      Theory::IntAutomaton_ptr int_auto = Theory::IntAutomaton::makeInt(int_constant);
      Theory::IntAutomaton_ptr intersect_auto = other_value->int_automaton->intersect(int_auto);
      delete int_auto;
      if (intersect_auto->isEmptyLanguage()) {
        difference_value = this->clone();
      } else {
        difference_value = new Value(Type::INT_AUTOMATON, Theory::IntAutomaton::makePhi());
      }
      delete intersect_auto;
    } else if (Type::INT_AUTOMATON == type and Type::INT_CONSTANT == other_value->type) {
      int_automaton->difference(other_value->int_constant);
    } else {
      LOG(FATAL) << "cannot difference types (implement me): " << *this << " & " << *other_value;
    }
    return difference_value;
  }

  Value_ptr Value::concat(Value_ptr other_value) const {
    Value_ptr concat_value = nullptr;
    if (Type::STRING_AUTOMATON == type and type == other_value->type) {
      concat_value = new Value(Type::STRING_AUTOMATON,
          string_automaton->concat(other_value->string_automaton));
    } else {
      LOG(FATAL) << "cannot concatenate values";
    }
    return concat_value;
  }

  Value_ptr Value::plus(Value_ptr other_value) const {
    Value_ptr result = nullptr;
    if (Value::Type::INT_CONSTANT == this->getType()) {
      if (Value::Type::INT_CONSTANT == other_value->getType()) {
        result = new Value(Value::Type::INT_CONSTANT,
                this->getIntConstant() + other_value->getIntConstant());
      } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
        if (other_value->getIntAutomaton()->isAcceptingSingleInt()) {
          result = new Value(Value::Type::INT_CONSTANT,
                  this->getIntConstant() + other_value->getIntAutomaton()->getAnAcceptingInt());
        } else {
          result = new Value(Value::Type::INT_AUTOMATON,
                  other_value->getIntAutomaton()->plus(this->getIntConstant()));
        }
      } else {
        LOG(FATAL) << "Unexpected right parameter: " << *other_value;
      }
    } else if (Value::Type::INT_AUTOMATON == this->getType()) {
      if (Value::Type::INT_CONSTANT == other_value->getType()) {
        if (this->getIntAutomaton()->isAcceptingSingleInt()) {
          result = new Value(Value::Type::INT_CONSTANT,
                  this->getIntAutomaton()->getAnAcceptingInt() + other_value->getIntConstant());
        } else {
          result = new Value(Value::Type::INT_AUTOMATON,
                  this->getIntAutomaton()->plus(other_value->getIntConstant()));
        }
      } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
        if (this->getIntAutomaton()->isAcceptingSingleInt() and
                other_value->getIntAutomaton()->isAcceptingSingleInt()) {
          result = new Value(Value::Type::INT_CONSTANT,
                  (this->getIntAutomaton()->getAnAcceptingInt()
                          + other_value->getIntAutomaton()->getAnAcceptingInt()));
        } else {
          result = new Value(Value::Type::INT_AUTOMATON,
                  this->getIntAutomaton()->plus(other_value->getIntAutomaton()));
        }
      } else {
        LOG(FATAL) << "Unexpected right parameter: " << *other_value;
      }
    } else {
      LOG(FATAL) << "Unexpected left parameter: " << *this;
    }
    return result;
  }

  Value_ptr Value::minus(Value_ptr other_value) const {
    Value_ptr result = nullptr;
    if (Value::Type::INT_CONSTANT == this->getType()) {
      if (Value::Type::INT_CONSTANT == other_value->getType()) {
        result = new Value(Value::Type::INT_CONSTANT,
                this->getIntConstant() - other_value->getIntConstant());
      } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
        if (other_value->getIntAutomaton()->isAcceptingSingleInt()) {
          result = new Value(Value::Type::INT_CONSTANT,
                  this->getIntConstant() - other_value->getIntAutomaton()->getAnAcceptingInt());
        } else {
          result = new Value(Value::Type::INT_AUTOMATON,
                  other_value->getIntAutomaton()->substractFrom(this->getIntConstant()));
        }
      } else {
        LOG(FATAL) << "Unexpected right parameter: " << *other_value;
      }
    } else if (Value::Type::INT_AUTOMATON == this->getType()) {
      if (Value::Type::INT_CONSTANT == other_value->getType()) {
        if (this->getIntAutomaton()->isAcceptingSingleInt()) {
          result = new Value(Value::Type::INT_CONSTANT,
                  this->getIntAutomaton()->getAnAcceptingInt() - other_value->getIntConstant());
        } else {
          result = new Value(Value::Type::INT_AUTOMATON,
                  this->getIntAutomaton()->minus(other_value->getIntConstant()));
        }
      } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
        if (this->getIntAutomaton()->isAcceptingSingleInt() and
                other_value->getIntAutomaton()->isAcceptingSingleInt()) {
          result = new Value(Value::Type::INT_CONSTANT,
                  (this->getIntAutomaton()->getAnAcceptingInt()
                          - other_value->getIntAutomaton()->getAnAcceptingInt()));
        } else {
          result = new Value(Value::Type::INT_AUTOMATON,
                  this->getIntAutomaton()->minus(other_value->getIntAutomaton()));
        }
      } else {
        LOG(FATAL) << "Unexpected right parameter: " << *other_value;
      }
    } else {
      LOG(FATAL) << "Unexpected left parameter: " << *this;
    }
    return result;
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
      is_satisfiable = not int_automaton->isEmptyLanguage();
      break;
    case Type::INTBOOL_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    case Type::STRING_AUTOMATON:
      is_satisfiable = not string_automaton->isEmptyLanguage();
      break;
    default:
      LOG(FATAL) << "value type is not supported";
      break;
    }
    return is_satisfiable;
  }

  bool Value::isSingleValue() {
    bool is_single_value = false;
    switch (type) {
    case Type::NONE:
      break;
    case Type::BOOl_CONSTANT:
    case Type::INT_CONSTANT:
      is_single_value = true;
      break;
    case Type::BOOL_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    case Type::INT_AUTOMATON:
      is_single_value = int_automaton->isAcceptingSingleInt();
      break;
    case Type::INTBOOL_AUTOMATON:
      LOG(FATAL) << "implement me";
      break;
    case Type::STRING_AUTOMATON:
      is_single_value = string_automaton->isAcceptingSingleString();
      break;
    default:
      LOG(FATAL) << "value type is not supported";
      break;
    }
    return is_single_value;
  }

  std::string Value::getASatisfyingExample() {
    std::stringstream ss;
    switch (type) {
    case Type::NONE:
      break;
    case Type::BOOl_CONSTANT:
      if (bool_constant) {
        ss << "true";
      } else {
        ss << "false";
      }
      break;
    case Type::INT_CONSTANT:
      ss << int_constant;
      break;
    case Type::BOOL_AUTOMATON:
      LOG(ERROR) << "bool automaton not supported";
      break;
    case Type::INT_AUTOMATON:
      ss << int_automaton->getAnAcceptingInt();
      break;
    case Type::INTBOOL_AUTOMATON:
      LOG(ERROR) << "implement me";
      break;
    case Type::STRING_AUTOMATON:
      ss << string_automaton->getAnAcceptingString();
      break;
    default:
      LOG(ERROR) << "value type is not supported";
      break;
    }

    return ss.str();
  }

  std::ostream& operator<<(std::ostream& os, const Value& value) {
    return os << value.str();
  }

} /* namespace Solver */
} /* namespace Vlab */

