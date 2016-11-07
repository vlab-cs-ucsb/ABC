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
const std::string Value::Name::BINARYINT_AUTOMATON = "Binary Int Automaton";
const std::string Value::Name::STRING_AUTOMATON = "String Automaton";
const std::string Value::Name::MULTITRACK_AUTOMATON = "MultiTrack Automaton";

Value::Value()
    : type(Type::NONE) {
}

Value::Value(bool data)
    : type(Type::BOOL_CONSTANT),
      bool_constant(data) {
}

Value::Value(int data)
    : type(Type::INT_CONSTANT),
      int_constant(data) {
}

Value::Value(Theory::BoolAutomaton_ptr data)
    : type(Type::BOOL_AUTOMATON),
      bool_automaton(data) {
}

Value::Value(Theory::IntAutomaton_ptr data)
    : type(Type::INT_AUTOMATON),
      int_automaton(data) {
}

Value::Value(Theory::BinaryIntAutomaton_ptr data)
    : type(Type::BINARYINT_AUTOMATON),
      binaryint_automaton(data) {
}

Value::Value(Theory::StringAutomaton_ptr data)
    : type(Type::STRING_AUTOMATON),
      string_automaton(data) {
}

Value::Value(Theory::MultiTrackAutomaton_ptr data)
    : type(Type::MULTITRACK_AUTOMATON),
      multitrack_automaton(data) {
}

Value::Value(const Value& other)
    : type(other.type) {
  switch (other.type) {
    case Type::NONE:
      break;
    case Type::BOOL_CONSTANT:
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
    case Type::BINARYINT_AUTOMATON:
      binaryint_automaton = other.binaryint_automaton->clone();
      break;
    case Type::STRING_AUTOMATON:
      string_automaton = other.string_automaton->clone();
      break;
    case Type::MULTITRACK_AUTOMATON:
      multitrack_automaton = other.multitrack_automaton->clone();
      break;
    default:
      LOG(FATAL)<< "value type is not supported";
      break;
    }
  }

Value_ptr Value::clone() const {
  return new Value(*this);
}

Value::~Value() {
  switch (type) {
    case Type::BOOL_AUTOMATON:
      delete bool_automaton;
      bool_automaton = nullptr;
      break;
    case Type::INT_AUTOMATON:
      delete int_automaton;
      int_automaton = nullptr;
      break;
    case Type::BINARYINT_AUTOMATON:
      delete binaryint_automaton;
      binaryint_automaton = nullptr;
      break;
    case Type::STRING_AUTOMATON:
      delete string_automaton;
      string_automaton = nullptr;
      break;
    case Type::MULTITRACK_AUTOMATON:
      delete multitrack_automaton;
      multitrack_automaton = nullptr;
      break;
    default:
      break;
  }
}

std::string Value::str() const {
  std::stringstream ss;
  switch (type) {
    case Type::NONE:
      ss << Name::NONE;
      break;
    case Type::BOOL_CONSTANT:
      ss << Name::BOOL_CONSTANT << " : " << std::boolalpha << bool_constant;
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
    case Type::STRING_AUTOMATON:
      ss << Name::STRING_AUTOMATON << " : " << " please print automaton";
      break;
    case Type::MULTITRACK_AUTOMATON:
      ss << Name::MULTITRACK_AUTOMATON << " : " << " please print automaton";
      break;
    case Type::BINARYINT_AUTOMATON:
      ss << Name::BINARYINT_AUTOMATON << " : " << " please print automaton";
      break;
    default:
      LOG(FATAL)<< "value type is not supported";
      break;
    }

  return ss.str();
}

void Value::setType(Type type) {
  this->type = type;
}

Value::Type Value::getType() const {
  return type;
}

void Value::setData(bool data) {
  bool_constant = data;
}

void Value::setData(int data) {
  int_constant = data;
}

void Value::setData(Theory::BoolAutomaton_ptr data) {
  bool_automaton = data;
}

void Value::setData(Theory::IntAutomaton_ptr data) {
  int_automaton = data;
}

void Value::setData(Theory::StringAutomaton_ptr data) {
  string_automaton = data;
}

void Value::setData(Theory::MultiTrackAutomaton_ptr data) {
  multitrack_automaton = data;
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

Theory::BinaryIntAutomaton_ptr Value::getBinaryIntAutomaton() const {
  return binaryint_automaton;
}

Theory::StringAutomaton_ptr Value::getStringAutomaton() const {
  return string_automaton;
}

Theory::MultiTrackAutomaton_ptr Value::getMultiTrackAutomaton() const {
  return multitrack_automaton;
}

Value_ptr Value::union_(Value_ptr other_value) const {

  Value_ptr union_value = nullptr;
  if(other_value == nullptr) {
    union_value = this->clone();
  } else if (Type::STRING_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
    union_value = new Value(string_automaton->union_(other_value->string_automaton));
  } else if (Type::MULTITRACK_AUTOMATON == type and Type::MULTITRACK_AUTOMATON == other_value->type) {
    union_value = new Value(multitrack_automaton->union_(other_value->multitrack_automaton));
  } else if (Type::BINARYINT_AUTOMATON == type and Type::BINARYINT_AUTOMATON == other_value->type) {
    union_value = new Value(binaryint_automaton->Union(other_value->binaryint_automaton));
  } else if (Type::INT_AUTOMATON == type and Type::INT_AUTOMATON == other_value->type) {
    union_value = new Value(int_automaton->union_(other_value->int_automaton));
  } else if (Type::INT_CONSTANT == type and Type::INT_CONSTANT == other_value->type) {
    union_value = new Value(Theory::IntAutomaton::makeInts( { this->int_constant, other_value->int_constant }));
  } else if (Type::INT_CONSTANT == type and Type::INT_AUTOMATON == other_value->type) {
    union_value = new Value(other_value->int_automaton->union_(int_constant));
  } else if (Type::INT_AUTOMATON == type and Type::INT_CONSTANT == other_value->type) {
    union_value = new Value(int_automaton->union_(other_value->int_constant));
  } else {
    LOG(FATAL)<< "cannot union_ types (implement me): " << *this << " | " << *other_value;
  }
  return union_value;
}

Value_ptr Value::intersect(Value_ptr other_value) const {
  Value_ptr intersection_value = nullptr;
  if (Type::STRING_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
    intersection_value = new Value(string_automaton->intersect(other_value->string_automaton));
  } else if (Type::MULTITRACK_AUTOMATON == type and Type::MULTITRACK_AUTOMATON == other_value->type) {
    intersection_value = new Value(multitrack_automaton->intersect(other_value->multitrack_automaton));
  } else if (Type::BINARYINT_AUTOMATON == type and Type::BINARYINT_AUTOMATON == other_value->type) {
    intersection_value = new Value(binaryint_automaton->Intersect(other_value->binaryint_automaton));
  } else if (Type::INT_AUTOMATON == type and Type::INT_AUTOMATON == other_value->type) {
    intersection_value = new Value(int_automaton->intersect(other_value->int_automaton));
  } else if (Type::INT_CONSTANT == type and Type::INT_CONSTANT == other_value->type) {
    if (this->int_constant == other_value->int_constant) {
      intersection_value = this->clone();
    } else {
      intersection_value = new Value(Theory::IntAutomaton::makePhi());
    }
  } else if (Type::INT_CONSTANT == type and Type::INT_AUTOMATON == other_value->type) {
    intersection_value = new Value(other_value->int_automaton->intersect(int_constant));
  } else if (Type::INT_AUTOMATON == type and Type::INT_CONSTANT == other_value->type) {
    intersection_value = new Value(int_automaton->intersect(other_value->int_constant));
  } else if (Type::MULTITRACK_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
    intersection_value = new Value(multitrack_automaton->intersect(other_value->multitrack_automaton));
  } else if (Type::STRING_AUTOMATON == type and Type::MULTITRACK_AUTOMATON == other_value->type) {
    LOG(FATAL) << " string intersect multitrack, implement me " << *this << " & " << *other_value;
  } else {
    LOG(FATAL) << "cannot intersect types (implement me): " << *this << " & " << *other_value;
  }
  return intersection_value;
}

Value_ptr Value::complement() const {
  Value_ptr complement_value = nullptr;
  switch (type) {
    case Type::STRING_AUTOMATON: {
      complement_value = new Value(string_automaton->complement());
      break;
    }
    case Type::MULTITRACK_AUTOMATON: {
      complement_value = new Value(multitrack_automaton->complement());
    }
    case Type::BINARYINT_AUTOMATON: {
      complement_value = new Value(binaryint_automaton->Complement());
      break;
    }
    case Type::INT_AUTOMATON: {
      complement_value = new Value(int_automaton->complement());
      break;
    }
    case Type::INT_CONSTANT: {
      Theory::IntAutomaton_ptr int_auto = Theory::IntAutomaton::makeInt(int_constant);
      complement_value = new Value(int_auto->complement());
      delete int_auto;
      break;
    }
    case Type::BOOL_CONSTANT: {
      complement_value = new Value(not bool_constant);
      break;
    }
    default:
      LOG(FATAL)<< "implement me" << *this;
      break;
    }
  return complement_value;
}

Value_ptr Value::difference(Value_ptr other_value) const {
  Value_ptr difference_value = nullptr;
  if (Type::STRING_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
    difference_value = new Value(string_automaton->difference(other_value->string_automaton));
  } else if (Type::MULTITRACK_AUTOMATON == type and Type::MULTITRACK_AUTOMATON == other_value->type) {
    difference_value = new Value(multitrack_automaton->difference(other_value->multitrack_automaton));
  } else if (Type::BINARYINT_AUTOMATON == type and Type::BINARYINT_AUTOMATON == other_value->type) {
    difference_value = new Value(binaryint_automaton->Difference(other_value->binaryint_automaton));
  } else if (Type::INT_AUTOMATON == type and Type::INT_AUTOMATON == other_value->type) {
    difference_value = new Value(int_automaton->difference(other_value->int_automaton));
  } else if (Type::INT_CONSTANT == type and Type::INT_CONSTANT == other_value->type) {
    if (this->int_constant != other_value->int_constant) {
      difference_value = this->clone();
    } else {
      difference_value = new Value(Theory::IntAutomaton::makePhi());
    }
  } else if (Type::INT_CONSTANT == type and Type::INT_AUTOMATON == other_value->type) {
    Theory::IntAutomaton_ptr int_auto = Theory::IntAutomaton::makeInt(int_constant);
    Theory::IntAutomaton_ptr intersect_auto = other_value->int_automaton->intersect(int_auto);
    delete int_auto;
    if (intersect_auto->isEmptyLanguage()) {
      difference_value = this->clone();
    } else {
      difference_value = new Value(Theory::IntAutomaton::makePhi());
    }
    delete intersect_auto;
  } else if (Type::INT_AUTOMATON == type and Type::INT_CONSTANT == other_value->type) {
    int_automaton->difference(other_value->int_constant);
  } else if (Type::MULTITRACK_AUTOMATON == type and Type::STRING_AUTOMATON == other_value->type) {
    LOG(FATAL)<< " multitrack difference string, implement me " << *this << " & " << *other_value;
  } else if (Type::STRING_AUTOMATON == type and Type::MULTITRACK_AUTOMATON == other_value->type) {
    LOG(FATAL) << " string difference multitrack, implement me " << *this << " & " << *other_value;
  } else {
    LOG(FATAL) << "cannot difference types (implement me): " << *this << " & " << *other_value;
  }
  return difference_value;
}

Value_ptr Value::concat(Value_ptr other_value) const {
  Value_ptr concat_value = nullptr;
  if (Type::STRING_AUTOMATON == type and type == other_value->type) {
    concat_value = new Value(string_automaton->concat(other_value->string_automaton));
  } else {
    LOG(FATAL)<< "cannot concatenate values";
  }
  return concat_value;
}

Value_ptr Value::plus(Value_ptr other_value) const {
  Value_ptr result = nullptr;
  if (Value::Type::INT_CONSTANT == this->getType()) {
    if (Value::Type::INT_CONSTANT == other_value->getType()) {
      result = new Value(this->getIntConstant() + other_value->getIntConstant());
    } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
      if (other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntConstant() + other_value->getIntAutomaton()->getAnAcceptingInt());
      } else {
        result = new Value(other_value->getIntAutomaton()->plus(this->getIntConstant()));
      }
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *other_value;
    }
  } else if (Value::Type::INT_AUTOMATON == this->getType()) {
    if (Value::Type::INT_CONSTANT == other_value->getType()) {
      if (this->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntAutomaton()->getAnAcceptingInt() + other_value->getIntConstant());
      } else {
        result = new Value(this->getIntAutomaton()->plus(other_value->getIntConstant()));
      }
    } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
      if (this->getIntAutomaton()->isAcceptingSingleInt() and
          other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value((this->getIntAutomaton()->getAnAcceptingInt()
                + other_value->getIntAutomaton()->getAnAcceptingInt()));
      } else {
        result = new Value(this->getIntAutomaton()->plus(other_value->getIntAutomaton()));
      }
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *other_value;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *this;
  }
  return result;
}

Value_ptr Value::times(Value_ptr other_value) const {
  Value_ptr result = nullptr;
  if (Value::Type::INT_CONSTANT == this->getType()) {
    if (Value::Type::INT_CONSTANT == other_value->getType()) {
      result = new Value(this->getIntConstant() * other_value->getIntConstant());
    } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
      if (other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntConstant() * other_value->getIntAutomaton()->getAnAcceptingInt());
      } else {
        result = new Value(other_value->getIntAutomaton()->times(this->getIntConstant()));
      }
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *other_value;
    }
  } else if (Value::Type::INT_AUTOMATON == this->getType()) {
    if (Value::Type::INT_CONSTANT == other_value->getType()) {
      if (this->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntAutomaton()->getAnAcceptingInt() * other_value->getIntConstant());
      } else {
        result = new Value(this->getIntAutomaton()->times(other_value->getIntConstant()));
      }
    } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
      if (this->getIntAutomaton()->isAcceptingSingleInt() and
          other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value((this->getIntAutomaton()->getAnAcceptingInt()
                * other_value->getIntAutomaton()->getAnAcceptingInt()));
      } else if(this->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(other_value->getIntAutomaton()->times(this->getIntConstant()));
      } else if(other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntAutomaton()->times(other_value->getIntConstant()));
      } else {
        LOG(FATAL)<< "Multiplication is supported only for Linear Integer Arithmetic where all parameters must be constants except one.";
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
      result = new Value(this->getIntConstant() - other_value->getIntConstant());
    } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
      if (other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntConstant() - other_value->getIntAutomaton()->getAnAcceptingInt());
      } else {
        result = new Value(other_value->getIntAutomaton()->substractFrom(this->getIntConstant()));
      }
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *other_value;
    }
  } else if (Value::Type::INT_AUTOMATON == this->getType()) {
    if (Value::Type::INT_CONSTANT == other_value->getType()) {
      if (this->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value(this->getIntAutomaton()->getAnAcceptingInt() - other_value->getIntConstant());
      } else {
        result = new Value(this->getIntAutomaton()->minus(other_value->getIntConstant()));
      }
    } else if (Value::Type::INT_AUTOMATON == other_value->getType()) {
      if (this->getIntAutomaton()->isAcceptingSingleInt() and
          other_value->getIntAutomaton()->isAcceptingSingleInt()) {
        result = new Value((this->getIntAutomaton()->getAnAcceptingInt()
                - other_value->getIntAutomaton()->getAnAcceptingInt()));
      } else {
        result = new Value(this->getIntAutomaton()->minus(other_value->getIntAutomaton()));
      }
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *other_value;
    }
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *this;
  }
  return result;
}

bool Value::is_satisfiable() {
  bool is_satisfiable = false;
  switch (type) {
    case Type::NONE:
      break;
    case Type::BOOL_CONSTANT:
      is_satisfiable = bool_constant;
      break;
    case Type::INT_CONSTANT:
      is_satisfiable = true;
      break;
    case Type::BOOL_AUTOMATON:
      LOG(FATAL)<< "implement me";
      break;
      case Type::INT_AUTOMATON:
      is_satisfiable = not int_automaton->isEmptyLanguage();
      break;
      case Type::BINARYINT_AUTOMATON:
      is_satisfiable = not binaryint_automaton->isEmptyLanguage();
      break;
      case Type::STRING_AUTOMATON:
      is_satisfiable = not string_automaton->isEmptyLanguage();
      break;
      case Type::MULTITRACK_AUTOMATON:
      is_satisfiable = not multitrack_automaton->isEmptyLanguage();
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
    case Type::BOOL_CONSTANT:
    case Type::INT_CONSTANT:
      is_single_value = true;
      break;
    case Type::BOOL_AUTOMATON:
      LOG(FATAL)<< "implement me";
      break;
      case Type::INT_AUTOMATON:
      is_single_value = int_automaton->isAcceptingSingleInt();
      break;
      case Type::BINARYINT_AUTOMATON:
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
    case Type::BOOL_CONSTANT:
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
      LOG(ERROR)<< "bool automaton not supported";
      break;
      case Type::INT_AUTOMATON:
      ss << int_automaton->getAnAcceptingInt();
      break;
      case Type::BINARYINT_AUTOMATON:
      LOG(ERROR) << "implement me";
      ss << "------";
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

