/*
 * Value.h
 *
 *  Created on: Jul 1, 2015
 *      Author: baki
 */

#ifndef SOLVER_VALUE_H_
#define SOLVER_VALUE_H_

#include <string>
#include <sstream>

#include <glog/logging.h>
#include "BoolAutomaton.h"
#include "IntAutomaton.h"
#include "IntBoolAutomaton.h"
#include "StringAutomaton.h"

namespace Vlab {
namespace Solver {

class Value;
typedef Value* Value_ptr;

class Value {
public:
  enum class Type
    : int {
      NONE = 0, BOOl_CONSTANT, INT_CONSTANT, STRING_CONSTANT, // not represented here as a data, can refer to singleton automaton
    BOOL_AUTOMATON,
    INT_AUTOMATON,
    INTBOOL_AUTOMATON,
    STRING_AUTOMATON
  };

  Value();
  Value(Type type, bool data);
  Value(Type type, int data);
  Value(Type type, Theory::BoolAutomaton_ptr data);
  Value(Type type, Theory::IntAutomaton_ptr data);
  Value(Type type, Theory::IntBoolAutomaton_ptr data);
  Value(Type type, Theory::StringAutomaton_ptr data);
  Value(const Value&);
  Value_ptr clone() const;
  virtual ~Value();

  std::string str() const;
  void setType(Type type);
  Value::Type getType() const;

  void set(bool data);
  void set(int data);
  void set(Theory::BoolAutomaton_ptr data);
  void set(Theory::IntAutomaton_ptr data);
  void set(Theory::IntBoolAutomaton_ptr data);
  void set(Theory::StringAutomaton_ptr data);

  bool getBoolConstant() const;
  int getIntConstant() const;
  Theory::BoolAutomaton_ptr getBoolAutomaton() const;
  Theory::IntAutomaton_ptr getIntAutomaton() const;
  Theory::IntBoolAutomaton_ptr getIntBoolAutomaton() const;
  Theory::StringAutomaton_ptr getStringAutomaton() const;

  Value_ptr union_(Value_ptr other_value) const;
  Value_ptr intersect(Value_ptr other_value) const;
  Value_ptr complement() const;
  Value_ptr difference(Value_ptr other_value) const;

  Value_ptr concat(Value_ptr other_value) const;

  bool isSatisfiable();

  class Name {
  public:
    static const std::string NONE;
    static const std::string BOOL_CONSTANT;
    static const std::string INT_CONSTANT;
    static const std::string STRING_CONSTANT;
    static const std::string BOOL_AUTOMATON;
    static const std::string INT_AUTOMATON;
    static const std::string INTBOOL_AUTOMATON;
    static const std::string STRING_AUTOMATON;
  };

  friend std::ostream& operator<<(std::ostream& os, const Value& value);
private:
  Value::Type type;

  union {
    bool bool_constant;
    int int_constant;
    Theory::BoolAutomaton_ptr bool_automaton;
    Theory::IntAutomaton_ptr int_automaton;
    Theory::IntBoolAutomaton_ptr intbool_automaton;
    Theory::StringAutomaton_ptr string_automaton;
  };

  static const int VLOG_LEVEL;

};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_VALUE_H_ */
