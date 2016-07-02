/*
 * RegularExpression.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 *
 *  Original source is a Java file: https://github.com/cs-au-dk/dk.brics.automaton/blob/master/src/dk/brics/automaton/RegExp.java
 * dk.brics.automaton
 *
 * Copyright (c) 2001-2011 Anders Moeller
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
  /**
   * Syntax flag, enables intersection (<tt>&amp;</tt>).
   */
  static int const INTERSECTION;

  /**
   * Syntax flag, enables complement (<tt>~</tt>).
   */
  static int const COMPLEMENT;

  /**
   * Syntax flag, enables empty language (<tt>#</tt>).
   */
  static int const EMPTY;

  /**
   * Syntax flag, enables anystring (<tt>@</tt>).
   */
  static int const ANYSTRING;

  /**
   * Syntax flag, enables named automata (<tt>&lt;</tt>identifier<tt>&gt;</tt>).
   */
  static int const AUTOMATON;

  /**
   * Syntax flag, enables numerical intervals (<tt>&lt;<i>n</i>-<i>m</i>&gt;</tt>).
   */
  static int const INTERVAL;

  /**
   * Syntax flag, enables all optional RegularExpression syntax.
   */
  static int const ALL;

  /**
   * Syntax flag, enables no optional RegularExpression syntax.
   */
  static int const NONE;

  /**
   * Syntax flag, used as a default combinations of the flag
   * Enables all except AUTOMATON and INTERVAL
   */
  static int DEFAULT;

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

  RegularExpression();
  RegularExpression(std::string regex);
  RegularExpression(std::string regex, int syntax_flags);
  RegularExpression(const RegularExpression&);
  virtual ~RegularExpression();

  bool is_constant_string() const;
  std::string get_constant_string() const;
  std::string str() const;
  RegularExpression_ptr clone() const;
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

  Type type();
  RegularExpression_ptr get_expr1();
  RegularExpression_ptr get_expr2();
  unsigned long get_min();
  unsigned long get_max();
  char get_character();
  char get_from_character();
  char get_to_character();
  std::string get_string();

  friend std::ostream& operator<<(std::ostream& os, const RegularExpression& regex);
private:

  static RegularExpression_ptr concat_constants(RegularExpression_ptr exp1, RegularExpression_ptr exp2);
  void parse();
  bool peek(std::string s);
  bool match(char c);
  bool more();
  char next();
  bool check(int flag);

  Type type_;
  int flags_;
  char character_;
  char from_char_;
  char to_char_;
  unsigned digits_;
  unsigned long min_;
  unsigned long max_;
  std::string::size_type pos_;
  RegularExpression_ptr exp1_;
  RegularExpression_ptr exp2_;
  std::string string_;
  std::string input_regex_string_;

  static const int VLOG_LEVEL;
};

} /* namespace Util */
} /* namespace Vlab */

#endif /* UTILS_REGULAREXPRESSION_H_ */
