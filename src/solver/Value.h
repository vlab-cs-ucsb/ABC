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

#include "../theory/BoolAutomaton.h"
#include "../theory/IntAutomaton.h"
#include "../theory/BinaryIntAutomaton.h"
#include "../theory/StringAutomaton.h"
#include "../theory/MultiTrackAutomaton.h"

namespace Vlab {
namespace Solver {

class Value;
using Value_ptr = Value*;

class Value {
 public:
  enum class Type
    : int {
      NONE = 0,
    BOOl_CONSTANT,
    INT_CONSTANT,
    STRING_CONSTANT,  // not represented here as a data, can refer to singleton automaton
    BOOL_AUTOMATON,
    INT_AUTOMATON,
    BINARYINT_AUTOMATON,
    STRING_AUTOMATON,
    MULTITRACK_AUTOMATON
  };

  Value();
  Value(bool data);
  Value(int data);
  Value(Theory::BoolAutomaton_ptr data);
  Value(Theory::IntAutomaton_ptr data);
  Value(Theory::BinaryIntAutomaton_ptr data);
  Value(Theory::StringAutomaton_ptr data);
  Value(Theory::MultiTrackAutomaton_ptr data);
  Value(const Value&);
  Value_ptr clone() const;
  virtual ~Value();

  std::string str() const;
  void setType(Type type);
  Value::Type getType() const;

  void setData(bool data);
  void setData(int data);
  void setData(Theory::BoolAutomaton_ptr data);
  void setData(Theory::IntAutomaton_ptr data);
  void setData(Theory::BinaryIntAutomaton_ptr data);
  void setData(Theory::StringAutomaton_ptr data);
  void setData(Theory::MultiTrackAutomaton_ptr data);

  bool getBoolConstant() const;
  int getIntConstant() const;
  Theory::BoolAutomaton_ptr getBoolAutomaton() const;
  Theory::IntAutomaton_ptr getIntAutomaton() const;
  Theory::BinaryIntAutomaton_ptr getBinaryIntAutomaton() const;
  Theory::StringAutomaton_ptr getStringAutomaton() const;
  Theory::MultiTrackAutomaton_ptr getMultiTrackAutomaton() const;

  Value_ptr union_(Value_ptr other_value) const;
  Value_ptr intersect(Value_ptr other_value) const;
  Value_ptr complement() const;
  Value_ptr difference(Value_ptr other_value) const;

  Value_ptr concat(Value_ptr other_value) const;
  Value_ptr plus(Value_ptr other_value) const;
  Value_ptr times(Value_ptr other_value) const;
  Value_ptr minus(Value_ptr other_value) const;

  bool isSatisfiable();bool isSingleValue();
  std::string getASatisfyingExample();

  class Name {
   public:
    static const std::string NONE;
    static const std::string BOOL_CONSTANT;
    static const std::string INT_CONSTANT;
    static const std::string STRING_CONSTANT;
    static const std::string BOOL_AUTOMATON;
    static const std::string INT_AUTOMATON;
    static const std::string BINARYINT_AUTOMATON;
    static const std::string STRING_AUTOMATON;
    static const std::string MULTITRACK_AUTOMATON;
  };

  friend std::ostream& operator<<(std::ostream& os, const Value& value);
 private:
  Value::Type type;

  union {
    bool bool_constant;
    int int_constant;
    Theory::BoolAutomaton_ptr bool_automaton;
    Theory::IntAutomaton_ptr int_automaton;
    Theory::BinaryIntAutomaton_ptr binaryint_automaton;
    Theory::StringAutomaton_ptr string_automaton;
    Theory::MultiTrackAutomaton_ptr multitrack_automaton;
  };

  static const int VLOG_LEVEL;

};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_VALUE_H_ */
