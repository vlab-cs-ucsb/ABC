/*
 * RegularExpression.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef UTILS_REGULAREXPRESSION_H_
#define UTILS_REGULAREXPRESSION_H_

#include <stdexcept>
#include <cstdint>
#include <cstdlib>
#include <sstream>
#include <string>

#include <glog/logging.h>

namespace Vlab {
namespace Util {

class RegularExpression;
typedef RegularExpression* RegularExpression_ptr;

class RegularExpression {
public:
  RegularExpression();
  RegularExpression(std::string regex);
  RegularExpression(std::string regex, int syntax_flags);
  virtual ~RegularExpression();

  /**
   * Syntax flag, enables intersection (<tt>&amp;</tt>).
   */
  static int const INTERSECTION = 0x0001;

  /**
   * Syntax flag, enables complement (<tt>~</tt>).
   */
  static int const COMPLEMENT = 0x0002;

  /**
   * Syntax flag, enables empty language (<tt>#</tt>).
   */
  static int const EMPTY = 0x0004;

  /**
   * Syntax flag, enables anystring (<tt>@</tt>).
   */
  static int const ANYSTRING = 0x0008;

  /**
   * Syntax flag, enables named automata (<tt>&lt;</tt>identifier<tt>&gt;</tt>).
   */
  static int const AUTOMATON = 0x0010;

  /**
   * Syntax flag, enables numerical intervals (<tt>&lt;<i>n</i>-<i>m</i>&gt;</tt>).
   */
  static int const INTERVAL = 0x0020;

  /**
   * Syntax flag, enables all optional RegularExpression syntax.
   */
  static int const ALL = 0xffff;


  /**
   * Syntax flag, enables no optional RegularExpression syntax.
   */
  static int const NONE = 0x0000;

  enum class Type : int {
    NONE = 0,
            UNION,
            CONCATENATION,
            INTERSECTION,
            OPTIONAL,
            REPEAT_STAR,
            REPEAT_PLUS,
            REPEAT_MIN,
            REPEAT_MINMAX,
            COMPLEMENT,
            CHAR,
            CHAR_RANGE,
            ANYCHAR,
            EMPTY,
            STRING,
            ANYSTRING,
            AUTOMATON,
            INTERVAL
  };

  //    StrangerAutomaton_ptr toAutomaton();
  std::string toString() const;
  void simplify();
  void copy(RegularExpression_ptr e);
  static RegularExpression_ptr makeUnion(RegularExpression_ptr exp1, RegularExpression_ptr exp2);
  static RegularExpression_ptr makeConcatenation(RegularExpression_ptr exp1, RegularExpression_ptr exp2);
  static RegularExpression_ptr makeIntersection(RegularExpression_ptr exp1, RegularExpression_ptr exp2);
  static RegularExpression_ptr makeOptional(RegularExpression_ptr exp);
  static RegularExpression_ptr makeRepeatStar(RegularExpression_ptr exp);
  static RegularExpression_ptr makeRepeatPlus(RegularExpression_ptr exp);
  static RegularExpression_ptr makeRepeat(RegularExpression_ptr exp, unsigned long min);
  static RegularExpression_ptr makeRepeat(RegularExpression_ptr exp, unsigned long min, unsigned long max);
  static RegularExpression_ptr makeComplement(RegularExpression_ptr exp);
  static RegularExpression_ptr makeChar(char c);
  static RegularExpression_ptr makeCharRange(char from, char to);
  static RegularExpression_ptr makeAnyChar();
  static RegularExpression_ptr makeEmpty();
  static RegularExpression_ptr makeString(std::string s);
  static RegularExpression_ptr makeAnyString();
  static RegularExpression_ptr makeAutomaton(std::string s);
  static RegularExpression_ptr makeInterval(unsigned long min, unsigned long max, unsigned digits);
  RegularExpression_ptr parseUnionExp();
  RegularExpression_ptr parseInterExp();
  RegularExpression_ptr parseConcatExp();
  RegularExpression_ptr parseRepeatExp();
  RegularExpression_ptr parseComplExp();
  RegularExpression_ptr parseCharClassExp();
  RegularExpression_ptr parseCharClasses();
  RegularExpression_ptr parseCharClass();
  RegularExpression_ptr parseSimpleExp();
  char parseCharExp();

  Type getType();
  RegularExpression_ptr getExpr1();
  RegularExpression_ptr getExpr2();
  unsigned long getMin();
  unsigned long getMax();
  char getChar();
  char getFrom();
  char getTo();
  std::string getS();


  friend std::ostream& operator<<(std::ostream& os, const RegularExpression& regex);
private:

  static RegularExpression_ptr makeString(RegularExpression_ptr exp1, RegularExpression_ptr exp2);
  void init(std::string s, int syntax_flags);
  bool peek(std::string s);
  bool match(char c);
  bool more();
  char next();
  bool check(int flag);

  RegularExpression_ptr exp1;
  RegularExpression_ptr exp2;
  unsigned long min;
  unsigned long max;
  unsigned digits;
  int flags;
  char c;
  char from, to;
  std::string regex_string;
  std::string s;
  std::string::size_type pos;
  Type type;

  static const int VLOG_LEVEL;
};

} /* namespace Util */
} /* namespace Vlab */

#endif /* UTILS_REGULAREXPRESSION_H_ */
