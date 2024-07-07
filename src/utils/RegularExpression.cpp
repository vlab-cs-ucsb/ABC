/*
 * RegularExpression.cpp
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

#include <iostream>
#include "RegularExpression.h"

namespace Vlab {
namespace Util {

const int RegularExpression::VLOG_LEVEL = 10;

const int RegularExpression::INTERSECTION = 0x0001;
const int RegularExpression::COMPLEMENT = 0x0002;
const int RegularExpression::EMPTY = 0x0004;
const int RegularExpression::ANYSTRING = 0x0008;
const int RegularExpression::AUTOMATON = 0x0010;
const int RegularExpression::INTERVAL = 0x0020;
const int RegularExpression::ALL = 0xffff;
const int RegularExpression::NONE = 0x0000;
int RegularExpression::DEFAULT = 0x000f;

bool RegularExpression::escape_ = true;

RegularExpression::RegularExpression()
    : type_(Type::NONE),
      flags_(DEFAULT),
      character_('\0'),
      from_char_('\0'),
      to_char_('\0'),
      digits_(0),
      min_(0),
      max_(0),
      pos_(0),
      exp1_(nullptr),
      exp2_(nullptr),
      string_(""),
      input_regex_string_("") {

}

RegularExpression::RegularExpression(std::string regex)
    : type_(Type::NONE),
      flags_(DEFAULT),
      character_('\0'),
      from_char_('\0'),
      to_char_('\0'),
      digits_(0),
      min_(0),
      max_(0),
      pos_(0),
      exp1_(nullptr),
      exp2_(nullptr),
      string_(""),
      input_regex_string_(regex) {
  parse();
}

RegularExpression::RegularExpression(std::string regex, int syntax_flags)
    : type_(Type::NONE),
      flags_(syntax_flags),
      character_('\0'),
      from_char_('\0'),
      to_char_('\0'),
      digits_(0),
      min_(0),
      max_(0),
      pos_(0),
      exp1_(nullptr),
      exp2_(nullptr),
      string_(""),
      input_regex_string_(regex) {
  parse();
}

RegularExpression::RegularExpression(const RegularExpression& other)
    : type_ { other.type_ },
      flags_(other.flags_),
      character_(other.character_),
      from_char_(other.from_char_),
      to_char_(other.to_char_),
      digits_(other.digits_),
      min_(other.min_),
      max_(other.max_),
      pos_(other.pos_),
      exp1_(nullptr),
      exp2_(nullptr),
      string_(other.string_),
      input_regex_string_(other.input_regex_string_) {

  if (other.exp1_) {
    exp1_ = other.exp1_->clone();
  }

  if (other.exp2_) {
    exp2_ = other.exp2_->clone();
  }

}

RegularExpression::~RegularExpression() {
  delete exp1_;
  exp1_ = nullptr;
  delete exp2_;
  exp2_ = nullptr;
}


/*
 * EMPTY means empty language. should not be treated as "constant"
 */
bool RegularExpression::is_constant_string() const {
  // return (type_ == Type::STRING or type_ == Type::CHAR or type_ == Type::EMPTY);
  return (type_ == Type::STRING or type_ == Type::CHAR);
}

std::string RegularExpression::constant_str() const {
  std::stringstream ss;
  switch (type_) {
    case Type::CHAR: {
      ss << character_;
    }
      ;
      break;
    // case Type::EMPTY:
    //   ss << "";
    //   break;
    case Type::STRING: {
      ss << string_;
    }
      ;
      break;
    default:

      break;
  }
  return ss.str();
}

std::string RegularExpression::str() const {
  std::stringstream ss;
  switch (type_) {
    case Type::UNION:
      ss << '(' << *exp1_ << '|' << *exp2_ << ')';
      break;
    case Type::CONCATENATION:
      ss << *exp1_ << *exp2_;
      break;
    case Type::INTERSECTION:
      ss << '(' << *exp1_ << '&' << *exp2_ << ')';
      break;
    case Type::OPTIONAL:
      if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR or exp1_->type_ == Type::EMPTY) {
        ss << *exp1_ << "?";
      } else {
        ss << '(' << *exp1_ << ")?";
      }
      break;
    case Type::REPEAT_STAR:
      if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR or exp1_->type_ == Type::EMPTY) {
        ss << *exp1_ << "*";
      } else {
        ss << '(' << *exp1_ << ")*";
      }
      break;
    case Type::REPEAT_PLUS:
      if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR or exp1_->type_ == Type::EMPTY) {
        ss << *exp1_ << "+";
      } else {
        ss << '(' << *exp1_ << ")+";
      }
      break;
    case Type::REPEAT_MIN:
      if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR or exp1_->type_ == Type::EMPTY) {
        ss << *exp1_ << "{" << std::to_string(min_) << ",}";
      } else {
        ss << '(' << *exp1_ << "){" << std::to_string(min_) << ",}";
      }
      break;
    case Type::REPEAT_MINMAX:
      if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR or exp1_->type_ == Type::EMPTY) {
        ss << *exp1_ << "{" << std::to_string(min_) << "," << std::to_string(max_) << "}";
      } else {
        ss << '(' << *exp1_ << "){" << std::to_string(min_) << "," << std::to_string(max_) << "}";
      }
      break;
    case Type::COMPLEMENT:
      ss << "~(" << *exp1_ << ')';
      break;
    case Type::CHAR: {
      std::string character(1, character_);
      ss << RegularExpression::escape_raw_string(character);
    }
      ;
      break;
    case Type::CHAR_RANGE: {
      std::string from = std::string(1, from_char_);
      std::string to = std::string(1, to_char_);
      if (from_char_ == '^' or from_char_ == '\\' or from_char_ == '[' or from_char_ == ']') {
        from = "\\" + from;
      }

      if (to_char_ == '^' or to_char_ == '\\' or to_char_ == '[' or to_char_ == ']') {
        to = "\\" + to;
      }

      ss << "[" << from << "-" << to << "]";
    }
      ;
      break;
    case Type::ANYCHAR:
      ss << '.';
      break;
    case Type::EMPTY:
      ss << '#';
      break;
    case Type::STRING: {
      ss << RegularExpression::escape_raw_string(string_);
    }
      ;
      break;
    case Type::ANYSTRING:
      ss << '@';
      break;
    case Type::AUTOMATON:
      ss << '<' << string_ << '>';
      break;
    case Type::INTERVAL: {
      std::string min_str = std::to_string(min_);
      std::string max_str = std::to_string(max_);
      ss << '<';
      if (digits_ > 0) {
        for (unsigned i = (unsigned) min_str.length(); i < digits_; i++) {
          ss << '0';
        }
      }

      ss << min_str << '-';
      if (digits_ > 0) {
        for (unsigned i = (unsigned) max_str.length(); i < digits_; i++) {
          ss << '0';
        }
      }
      ss << max_str << '>';
      break;
    }
    default:

      break;
  }
  return ss.str();
}

RegularExpression_ptr RegularExpression::clone() const {
  return new RegularExpression(*this);
}

/**
 *
 */
std::string RegularExpression::escape_raw_string(std::string input) {
  if(not escape_) {
    return input;
  }

  std::stringstream ss;
  std::string special = ".+*?(){}[]\"|\\";
  for (auto c : input) {
    if (special.find(c) != std::string::npos) {
      ss << R"(\)";
    } else if (((DEFAULT & INTERSECTION) != 0) and c == '&') {
      ss << R"(\)";
    } else if (((DEFAULT & COMPLEMENT) != 0) and c == '~') {
      ss << R"(\)";
    } else if (((DEFAULT & EMPTY) != 0) and c == '#') {
      ss << R"(\)";
    } else if (((DEFAULT & ANYSTRING) != 0) and c == '@') {
      ss << R"(\)";
    } else if ((((DEFAULT & INTERVAL) != 0) or ((DEFAULT & AUTOMATON) != 0)) and (c == '<' or c == '>')) {
      ss << R"(\)";
    }
    ss << c;
  }
  return ss.str();
}

RegularExpression_ptr RegularExpression::makeUnion(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  bool is_left_constant = false;
  bool is_right_constant = false;
  std::string left;
  std::string right;

  if (exp1->type_ == Type::STRING) {
    left = exp1->string_;
    is_left_constant = true;
  } else if (exp1->type_ == Type::CHAR) {
    left = std::string(1, exp1->character_);
    is_left_constant = true;
  }

  if (exp2->type_ == Type::STRING) {
    right = exp2->string_;
    is_right_constant = true;
  } else if (exp2->type_ == Type::CHAR) {
    right = std::string(1, exp2->character_);
    is_right_constant = true;
  }

  RegularExpression_ptr regex = new RegularExpression();
  if (is_left_constant and is_right_constant and left == right) {  // optimize
    regex->type_ = Type::STRING;
    regex->string_ = left;
    delete exp1;
    delete exp2;
  } else if (exp1->type_ == Type::ANYSTRING) {  // optimize
    regex = exp1->clone();
    delete exp1;
    delete exp2;
  } else if (exp2->type_ == Type::ANYSTRING) {  // optimize
    regex = exp2->clone();
    delete exp1;
    delete exp2;
  } else if (exp1->type_ == Type::EMPTY) {  // optimize
    regex = exp2->clone();
    delete exp1;
    delete exp2;
  } else if (exp2->type_ == Type::EMPTY) {  // optimize
    regex = exp1->clone();
    delete exp1;
    delete exp2;
  } else {
    regex->type_ = Type::UNION;
    regex->exp1_ = exp1;
    regex->exp2_ = exp2;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeConcatenation(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  RegularExpression_ptr regex = nullptr;
  if ((exp1->type_ == Type::EMPTY or exp2->type_ == Type::EMPTY)) {
    regex = RegularExpression::makeEmpty();
    delete exp1;
    delete exp2;
  } else if (exp1->type_ == Type::STRING and exp1->string_ == "") {
    regex = exp2->clone();
    delete exp1;
    delete exp2;
  } else if (exp2->type_ == Type::STRING and exp2->string_ == "") {
    regex = exp1->clone();
    delete exp1;
    delete exp2;
  } else if ((exp1->type_ == Type::CHAR or exp1->type_ == Type::STRING)
      and (exp2->type_ == Type::CHAR or exp2->type_ == Type::STRING)) {
    regex = RegularExpression::concat_constants(exp1, exp2);
    delete exp1;
    delete exp2;
  } else if (exp1->type_ == Type::CONCATENATION
      and (exp1->exp2_->type_ == Type::CHAR or exp1->exp2_->type_ == Type::STRING)
      and (exp2->type_ == Type::CHAR or exp2->type_ == Type::STRING)) {
    regex = new RegularExpression();
    regex->type_ = Type::CONCATENATION;
    regex->exp1_ = exp1->exp1_->clone();
    regex->exp2_ = RegularExpression::concat_constants(exp1->exp2_, exp2);
    delete exp1;
    delete exp2;
  } else if ((exp1->type_ == Type::CHAR or exp1->type_ == Type::STRING) and exp2->type_ == Type::CONCATENATION
      and (exp2->exp1_->type_ == Type::CHAR or exp2->exp1_->type_ == Type::STRING)) {
    regex = new RegularExpression();
    regex->type_ = Type::CONCATENATION;
    regex->exp1_ = RegularExpression::concat_constants(exp1, exp2->exp1_);
    regex->exp2_ = exp2->exp2_->clone();
    delete exp1;
    delete exp2;
  } else if(exp1->type() == Type::ANYSTRING and exp2->type() == Type::ANYSTRING) {
    regex = makeAnyString();
    delete exp1;
    delete exp2;
  } else {
    regex = new RegularExpression();
    regex->type_ = Type::CONCATENATION;
    regex->exp1_ = exp1;
    regex->exp2_ = exp2;
  }

  return regex;
}

RegularExpression_ptr RegularExpression::makeIntersection(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  bool is_left_constant = false;
  bool is_right_constant = false;
  std::string left;
  std::string right;

  if (exp1->type_ == Type::STRING) {
    left = exp1->string_;
    is_left_constant = true;
  } else if (exp1->type_ == Type::CHAR) {
    left = std::string(1, exp1->character_);
    is_left_constant = true;
  }

  if (exp2->type_ == Type::STRING) {
    right = exp2->string_;
    is_right_constant = true;
  } else if (exp2->type_ == Type::CHAR) {
    right = std::string(1, exp2->character_);
    is_right_constant = true;
  }

  RegularExpression_ptr regex = nullptr;
  if (is_left_constant and is_right_constant and left == right) {  // optimize
    regex = new RegularExpression();
    regex->type_ = Type::STRING;
    regex->string_ = left;
    delete exp1;
    delete exp2;
  } else if (exp1->type_ == Type::EMPTY or exp2->type_ == Type::EMPTY) {  // optimize
    regex = RegularExpression::makeEmpty();
    delete exp1;
    delete exp2;
  } else if (exp1->type_ == Type::ANYSTRING) {  // optimize
    regex = exp2->clone();
    delete exp1;
    delete exp2;
  } else if (exp2->type_ == Type::ANYSTRING) {  // optimize
    regex = exp1->clone();
    delete exp1;
    delete exp2;
  } else {
    regex = new RegularExpression();
    regex->type_ = Type::INTERSECTION;
    regex->exp1_ = exp1;
    regex->exp2_ = exp2;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeOptional(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  if (exp->type_ == Type::STRING and exp->string_ == "") {
    regex->type_ = Type::STRING;
    regex->string_ = "";
    delete exp;
  } else {
    regex->type_ = Type::OPTIONAL;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeatStar(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  if (exp->type_ == Type::EMPTY) {  // optimize
    regex->type_ = Type::STRING;
    regex->string_ = "";
    delete exp;
  } else if (exp->type_ == Type::ANYSTRING) { // kleene star is idempotent (x** = x*)
    regex->type_ = Type::ANYSTRING;
    delete exp;
  } else if (exp->type_ == Type::STRING and exp->string_ == "") {  // optimize
    regex->type_ = Type::STRING;
    regex->string_ = "";
    delete exp;
  } else {
    regex->type_ = Type::REPEAT_STAR;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeatPlus(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  if(exp->type_ == Type::EMPTY) {
    regex->type_ = Type::EMPTY;
    delete exp;
  } else if (exp->type_ == Type::STRING and exp->string_ == "") {
    regex->type_ = Type::STRING;
    regex->string_ = "";
    delete exp;
  } else {
    regex->type_ = Type::REPEAT_PLUS;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, unsigned long min) {
  RegularExpression_ptr regex = new RegularExpression();
  if (min < 0 || (exp->type_ == Type::STRING and exp->string_ == "")) {  // optimize
    regex->type_ = Type::STRING;
    regex->string_ = "";
    delete exp;
  } else {
    regex->type_ = Type::REPEAT_MIN;
    regex->exp1_ = exp;
    regex->min_ = min;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, unsigned long min, unsigned long max) {
  RegularExpression_ptr regex = new RegularExpression();
  if (min == 0 and max == 0) {  // optimize empty string
    regex->type_ = Type::STRING;
    regex->string_ = "";
    delete exp;
  } else if (min == max and exp->type_ == Type::STRING) {  // optimize one constant string
    regex->type_ = Type::STRING;
    std::stringstream ss;
    for (unsigned long i = 0; i < min; ++i) {
      ss << exp->string_;
    }
    regex->string_ = ss.str();
    delete exp;
  } else if (min == max and exp->type_ == Type::CHAR) {  // optimize one constant string
    regex->type_ = Type::STRING;
    std::stringstream ss;
    for (unsigned long i = 0; i < min; ++i) {
      ss << exp->character_;
    }
    regex->string_ = ss.str();
    delete exp;
  } else if (min > max) { // empty language when min is greater than max
    regex->type_ = Type::EMPTY;
  } else {
    regex->type_ = Type::REPEAT_MINMAX;
    regex->exp1_ = exp;
    regex->min_ = min;
    regex->max_ = max;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeComplement(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = nullptr;
  if (Type::COMPLEMENT == exp->type_) {  // optimize complement
    regex = exp->exp1_->clone();
    delete exp;
  } else if (Type::EMPTY == exp->type_) { // complement of empty language is any string
    regex = makeAnyString();
    delete exp;
  } else {
    regex = new RegularExpression();
    regex->type_ = Type::COMPLEMENT;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeChar(char c) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::CHAR;
  regex->character_ = c;
  return regex;
}

RegularExpression_ptr RegularExpression::makeCharRange(char from, char to) {
  RegularExpression_ptr regex = new RegularExpression();
  if (from == to) {  // optimize
    regex->type_ = Type::CHAR;
    regex->character_ = from;
  } else if (from > to) { // is empty set per smtlib standard
    regex->type_ = Type::EMPTY;
  } else {
    regex->type_ = Type::CHAR_RANGE;
    regex->from_char_ = from;
    regex->to_char_ = to;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeAnyChar() {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::ANYCHAR;
  return regex;
}

RegularExpression_ptr RegularExpression::makeEmpty() {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::EMPTY;
  return regex;
}

RegularExpression_ptr RegularExpression::makeString(std::string s) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::STRING;
  regex->string_ = s;
  return regex;
}

RegularExpression_ptr RegularExpression::makeAnyString() {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::ANYSTRING;
  return regex;
}

RegularExpression_ptr RegularExpression::makeAutomaton(std::string s) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::AUTOMATON;
  regex->string_ = s;
  return regex;
}

RegularExpression_ptr RegularExpression::makeInterval(unsigned long min, unsigned long max, unsigned digits) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::INTERVAL;
  regex->min_ = min;
  regex->max_ = max;
  regex->digits_ = digits;
  return regex;
}

RegularExpression_ptr RegularExpression::parseUnionExp() {
  RegularExpression_ptr regex = parseInterExp();
  if (match('|')) {
    regex = makeUnion(regex, parseUnionExp());
  }
  return regex;
}

RegularExpression_ptr RegularExpression::parseInterExp() {
  RegularExpression_ptr regex = parseConcatExp();
  if (check(INTERSECTION) and match('&')) {
    regex = makeIntersection(regex, parseInterExp());
  }
  return regex;
}

RegularExpression_ptr RegularExpression::parseConcatExp() {
  RegularExpression_ptr regex = parseRepeatExp();
  if (more() and !peek(")|") and (not check(INTERSECTION) or not peek(")&"))) {
    regex = makeConcatenation(regex, parseConcatExp());
  }
  return regex;
}

RegularExpression_ptr RegularExpression::parseRepeatExp() {
  RegularExpression_ptr regex = parseComplExp();
  while (peek("?*+{")) {
    if (match('?')) {
      regex = makeOptional(regex);
    } else if (match('*')) {
      regex = makeRepeatStar(regex);
    } else if (match('+')) {
      regex = makeRepeatPlus(regex);
    } else if (match('{')) {
      std::string::size_type start = pos_;
      while (peek("0123456789")) {
        next();
      }

      if (start == pos_) {
        LOG(FATAL)<< "integer expected at position: " << pos_;
      }

      unsigned long n = std::stoul(input_regex_string_.substr(start, pos_ - start));
      unsigned long m;
      bool is_m_set = false;
      if (match(',')) {
        start = pos_;
        while (peek("0123456789")) {
          next();
        }

        if (start != pos_) {
          m = std::stoul(input_regex_string_.substr(start, pos_ - start));
          is_m_set = true;
        }

      } else {
        m = n;
        is_m_set = true;
      }

      if (!match('}')) {
        LOG(FATAL)<< "expected '}' at position: " << pos_;
      }

      if (not is_m_set) {
        return makeRepeat(regex, n);
      } else {
        return makeRepeat(regex, n, m);
      }
    }
  }
  return regex;
}

RegularExpression_ptr RegularExpression::parseComplExp() {
  if (check(COMPLEMENT) and match('~')) {
    return makeComplement(parseComplExp());
  } else {
    return parseCharClassExp();
  }
}

RegularExpression_ptr RegularExpression::parseCharClassExp() {
  if (match('[')) {
    bool negate = false;
    if (match('^') and !peek("-")) {
      negate = true;
    }

    RegularExpression_ptr regex = parseCharClasses();
    if (negate) {
      regex = makeIntersection(makeAnyChar(), makeComplement(regex));
    }

    if (!match(']')) {
      LOG(FATAL)<< "expected ']' at position: " << pos_;
    }
    return regex;
  } else {
    return parseSimpleExp();
  }
}

RegularExpression_ptr RegularExpression::parseCharClasses() {
  RegularExpression_ptr regex = parseCharClass();
  while (more() and !peek("]")) {
    regex = makeUnion(regex, parseCharClass());
  }
  return regex;
}

RegularExpression_ptr RegularExpression::parseCharClass() {
  char c = parseCharExp();
  if (match('-')) {
    return makeCharRange(c, parseCharExp());
  } else {
    return makeChar(c);
  }
}

RegularExpression_ptr RegularExpression::parseSimpleExp() {
  if (match('.')) {
    return makeAnyChar();
  } else if (check(EMPTY) and match('#')) {
    return makeEmpty();
  } else if (check(ANYSTRING) and match('@')) {
    return makeAnyString();
  // } else if (match('"')) {
  //   int start = (int) pos_;
  //   while (more() and !peek("\"")) {
  //     next();
  //   }

  //   if (!match('"')) {
  //     LOG(FATAL)<< "expected '\"' at position: " << pos_;
  //   }

  //   return RegularExpression::makeString(input_regex_string_.substr(start, (pos_ - 1 - start)));
  } else if (match('(')) {
    if (match(')')) {
      return RegularExpression::makeString("");
    }

    RegularExpression_ptr regex = parseUnionExp();

    if (!match(')')) {
      LOG(FATAL)<< "expected ')' at position: " << pos_;
    }

    return regex;
  } else if ((check(AUTOMATON) or check(INTERVAL)) and match('<')) {
    int start = (int) pos_;
    while (more() and !peek(">")) {
      next();
    }

    if (!match('>')) {
      LOG(FATAL)<< "expected '>' at position: " << pos_;
    }

    std::string s = input_regex_string_.substr(start, (pos_ - 1 - start));
    std::string::size_type i = s.find('-');
    if (i == std::string::npos) {
      if (!check(AUTOMATON)) {
        LOG(FATAL)<< "interval syntax error at position: " << (pos_ - 1);
      }

      return makeAutomaton(s);
    } else {
      if(!check(INTERVAL)) {
        LOG(FATAL) << "illegal identifier at position: " << (pos_ - 1);
      }

      if(i == 0 or i == s.length() - 1 or i != s.find_last_of('-')) {
        LOG(FATAL) << "Number Format Error";
      }

      std::string smin = s.substr(0, i);
      std::string smax = s.substr(i + 1, (s.length()-(i + 1)));
      unsigned long imin = std::stoul(smin);
      unsigned long imax = std::stoul(smax);
      unsigned digits;
      if(smin.length() == smax.length()) {
        digits = (unsigned)smin.length();
      } else {
        digits = 0;
      }

      if(imin > imax) {
        unsigned long t = imin;
        imin = imax;
        imax = t;
      }
      return makeInterval(imin, imax, digits);
    }
  } else {
    return makeChar(parseCharExp());
  }
}

char RegularExpression::parseCharExp() {
  match('\\');
  return next();
}

RegularExpression::Type RegularExpression::type() {
  return type_;
}

RegularExpression_ptr RegularExpression::get_expr1() {
  return exp1_;
}

RegularExpression_ptr RegularExpression::get_expr2() {
  return exp2_;
}

unsigned long RegularExpression::get_min() {
  return min_;
}

unsigned long RegularExpression::get_max() {
  return max_;
}

char RegularExpression::get_character() {
  return character_;
}

char RegularExpression::get_from_character() {
  return from_char_;
}

char RegularExpression::get_to_character() {
  return to_char_;
}

std::string RegularExpression::get_string() {
  return string_;
}

std::vector<std::string> RegularExpression::enumerate() {

  std::vector<std::string> strings;  
  std::vector<std::string> prefixes;
  std::vector<std::string> suffixes;
  if(type_ == RegularExpression::Type::STRING) {
    strings.push_back(string_);
    return strings;
  }

  if(exp1_ != nullptr) {
    prefixes = exp1_->enumerate();
  }

  if(exp2_ != nullptr) {
    suffixes = exp2_->enumerate();
  }

  if(type_ == RegularExpression::Type::CONCATENATION) {
    for(auto prefix_iter : prefixes) {
      for(auto suffix_iter : suffixes) {
        strings.push_back(prefix_iter + suffix_iter);
      }
    }
  } else if(type_ == RegularExpression::Type::UNION) {
    for(auto prefix_iter : prefixes) {
      strings.push_back(prefix_iter);
    }
    for(auto suffix_iter : suffixes) {
      strings.push_back(suffix_iter);
    }
  }

  return strings;
}

void RegularExpression::simplify(int alpha, int omega, int depth) {
  // static int depth = 0;

  char anychar = '`';
  std::string anystring = "~";

  if(type_ == RegularExpression::Type::UNION) {
    exp1_->simplify(alpha, omega, depth+1);
    exp2_->simplify(alpha, omega, depth+1);

    if(exp1_->type() == RegularExpression::Type::STRING && exp2_->type() == RegularExpression::Type::STRING) {
      int len1 = exp1_->get_string().length();
      int len2 = exp2_->get_string().length();
      if(len1 <= alpha and len2 <= alpha and len1 == len2 
            and exp1_->get_string().find(anystring) == std::string::npos 
            and exp2_->get_string().find(anystring) == std::string::npos) {
        type_ = RegularExpression::Type::STRING;
        string_ = std::string(exp1_->get_string().length(),anychar);
        exp1_ = nullptr;
        exp2_ = nullptr;
        return;
      } 
    } 
    
    if(depth > omega || (exp1_->type() == RegularExpression::Type::STRING && exp1_->get_string() == anystring) 
                      || (exp2_->type() == RegularExpression::Type::STRING && exp2_->get_string() == anystring)) {
      type_ = RegularExpression::Type::STRING;
      string_ = anystring;
    }

  } else if(type_ == RegularExpression::Type::CONCATENATION) {
    exp1_->simplify(alpha, omega, depth);
    exp2_->simplify(alpha, omega, depth);

    if(exp1_->type() == RegularExpression::Type::STRING && exp2_->type() == RegularExpression::Type::STRING) {
      type_ = RegularExpression::Type::STRING;
      string_ = exp1_->get_string() + exp2_->get_string();
      exp1_ = nullptr;
      exp2_ = nullptr;
    }
  } else {
    if(exp1_ != nullptr) exp1_->simplify(alpha,omega, depth);
    if(exp2_ != nullptr) exp2_->simplify(alpha,omega, depth);
  }
}

// void RegularExpression::simplify() {
//   static int depth = 0;

//   // if(exp1_ != nullptr and exp2_ != nullptr) {
//   //   if(type_ == RegularExpression::Type::CONCATENATION) {
//   //     LOG(INFO) << "concat: ";
//   //   } else if (type_ == RegularExpression::Type::UNION) {
//   //     LOG(INFO) << "union: ";
//   //   }
//   //   LOG(INFO) << "    (" << exp1_->str() << " , " << exp2_->str() << ")";  
//   // }

//   char anychar = '`';
//   std::string anystring = "~";

//   if(exp1_ != nullptr) {
//     depth++;
//     exp1_->simplify();
//     depth--;
//   }
//   if(exp2_ != nullptr) {
//     depth++;
//     exp2_->simplify();
//     depth--;
//   }

//   if(type_ == RegularExpression::Type::UNION) {

//     if(depth >= 5) {
//       type_ = RegularExpression::Type::STRING;
//       string_ = anystring;
//       return;
//     }

//     if(exp1_->type() == RegularExpression::Type::STRING && exp1_->get_string() == anystring 
//           || exp2_->type() == RegularExpression::Type::STRING && exp2_->get_string() == anystring) {
//       type_ = RegularExpression::Type::STRING;
//       string_ = anystring;
//     } else if(exp1_->type() == RegularExpression::Type::STRING && exp2_->type() == RegularExpression::Type::STRING) {
//       int len1 = exp1_->get_string().length();
//       int len2 = exp2_->get_string().length();
//       if(len1 < 5 and len2 < 5 and len1 == len2 
//             and exp1_->get_string().find(anystring) == std::string::npos 
//             and exp2_->get_string().find(anystring) == std::string::npos) {
//         type_ = RegularExpression::Type::STRING;
//         string_ = std::string(exp1_->get_string().length(),anychar);
//       } else if(depth >= 5) {
//         type_ = RegularExpression::Type::STRING;
//         string_ = anystring;
//       }
//     }

//     if(exp1_->get_string().length() == exp2_->get_string().length() 
//             && exp1_->type() == RegularExpression::Type::STRING && exp2_->type() == RegularExpression::Type::STRING) {
      
//     }
//   } else if(type_ == RegularExpression::Type::CONCATENATION 
//           && exp1_->type() == RegularExpression::Type::STRING && exp2_->type() == RegularExpression::Type::STRING) {
//     type_ = RegularExpression::Type::STRING;
//     string_ = exp1_->get_string() + exp2_->get_string();
//   }
// }

void RegularExpression::set_escape(bool escape) {
  escape_ = escape;
}

int RegularExpression::ops() {
  switch(type_) {
    case RegularExpression::Type::NONE:
      return 0;
      break;
    case RegularExpression::Type::UNION:
      return 1 + exp1_->ops() + exp2_->ops();
      break;
    case RegularExpression::Type::CONCATENATION:
      return 1 + exp1_->ops() + exp2_->ops();
      break;
    case RegularExpression::Type::INTERSECTION:
      return 1 + exp1_->ops() + exp2_->ops();
      break;
    case RegularExpression::Type::OPTIONAL:
      return 1 + exp1_->ops();
      break;
    case RegularExpression::Type::REPEAT_STAR:
      return 1 + exp1_->ops();
      break;
    case RegularExpression::Type::REPEAT_PLUS:
      return 1 + exp1_->ops();
      break;
    case RegularExpression::Type::REPEAT_MIN:
      return 1 + exp1_->ops();
      break;
    case RegularExpression::Type::REPEAT_MINMAX:
      return 1 + exp1_->ops();
      break;
    case RegularExpression::Type::COMPLEMENT:
      return 1 + exp1_->ops();
      break;
    case RegularExpression::Type::CHAR:
      return 1;
      break;
    case RegularExpression::Type::CHAR_RANGE:
      return 1;
      break;
    case RegularExpression::Type::ANYCHAR:
      return 1;
      break;
    case RegularExpression::Type::EMPTY:
      return 1;
      break;
    case RegularExpression::Type::STRING:
      return 1;
      break;
    case RegularExpression::Type::ANYSTRING:
      return 1;
      break;
    case RegularExpression::Type::AUTOMATON:
      return 1;
      break;
    case RegularExpression::Type::INTERVAL:
      return 1;
      break;
    default:
      LOG(FATAL) << "can't determine number of obs for undefined type";
      return 0;
  }
}

std::ostream& operator<<(std::ostream& os, const RegularExpression& regex) {
  return os << regex.str();
}

RegularExpression_ptr RegularExpression::concat_constants(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  std::stringstream ss;
  if (exp1->type_ == Type::STRING) {
    ss << exp1->string_;
  } else {
    ss << exp1->character_;
  }

  if (exp2->type_ == Type::STRING) {
    ss << exp2->string_;
  } else {
    ss << exp2->character_;
  }
  return RegularExpression::makeString(ss.str());
}

void RegularExpression::parse() {
  if (input_regex_string_ == "") {
    type_ = Type::STRING;
    string_ = "";
    return;
  }

  RegularExpression_ptr e = parseUnionExp();
  if (pos_ < input_regex_string_.length()) {
    LOG(FATAL)<< "end-of-string expected at position: " << pos_;
  }

  type_ = e->type_;
  character_ = e->character_;
  from_char_ = e->from_char_;
  to_char_ = e->to_char_;
  digits_ = e->digits_;
  min_ = e->min_;
  max_ = e->max_;
  pos_ = e->pos_;
  exp1_ = e->exp1_;
  exp2_ = e->exp2_;
  string_ = e->string_;

  e->exp1_ = nullptr;
  e->exp2_ = nullptr;
  delete e;
  e = nullptr;
}

bool RegularExpression::peek(std::string s) {
  return (more() and (s.find(input_regex_string_[pos_]) != std::string::npos));
}

bool RegularExpression::match(char c) {
  if (pos_ >= input_regex_string_.length()) {
    return false;
  }

  if (input_regex_string_[pos_] == c) {
    pos_++;
    return true;
  }
  return false;
}

bool RegularExpression::more() {
  return pos_ < input_regex_string_.length();
}

char RegularExpression::next() {
  if (!more()) {
    LOG(FATAL)<< "unexpected end-of-string";
  }

  return input_regex_string_[pos_++];
}

bool RegularExpression::check(int flag) {
  return (flags_ & flag) != 0;
}

} /* namespace Util */
} /* namespace Vlab */
