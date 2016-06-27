/*
 * RegularExpression.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

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
const int RegularExpression::DEFAULT = 0x000f;

RegularExpression::RegularExpression()
        : exp1_(nullptr), exp2_(nullptr), min_(0), max_(0), digits_(0), flags_(0), character_('\0'), from_char_('\0'), to_char_('\0'), regex_string_(
                ""), string_(""), pos_(0), type_(Type::NONE) {

}

RegularExpression::RegularExpression(std::string regex)
        : exp1_(nullptr), exp2_(nullptr), min_(0), max_(0), digits_(0), flags_(0), character_('\0'), from_char_('\0'), to_char_('\0'), regex_string_(
                ""), string_(""), pos_(0), type_(Type::NONE) {
  init(regex, DEFAULT);
}

RegularExpression::RegularExpression(std::string regex, int syntax_flags)
        : exp1_(nullptr), exp2_(nullptr), min_(0), max_(0), digits_(0), flags_(syntax_flags), character_('\0'), from_char_('\0'), to_char_('\0'), regex_string_(
                ""), string_(""), pos_(0), type_(Type::NONE) {
  init(regex, syntax_flags);

}

RegularExpression::~RegularExpression() {
  delete exp1_; exp1_ = nullptr;
  delete exp2_; exp2_ = nullptr;
}

bool RegularExpression::is_constant_string() const {
  return (type_ == Type::STRING or type_ == Type::CHAR);
}

std::string RegularExpression::get_constant_string() const {
  if (type_ == Type::STRING) {
    return string_;
  } else if (type_ == Type::CHAR) {
    return "" + character_;
  } else {
    LOG(FATAL) << "Regular expression is not a constant string";
    return "";
  }
}

std::string RegularExpression::toString() const {
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
    if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR
          or exp1_->type_ == Type::EMPTY) {
      ss << *exp1_ << "?";
    } else {
      ss << '(' << *exp1_ << ")?";
    }
    break;
  case Type::REPEAT_STAR:
    if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR
            or exp1_->type_ == Type::EMPTY) {
      ss << *exp1_ << "*";
    } else {
      ss << '(' << *exp1_ << ")*";
    }
    break;
  case Type::REPEAT_PLUS:
    if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR
            or exp1_->type_ == Type::EMPTY) {
      ss << *exp1_ << "+";
    } else {
      ss << '(' << *exp1_ << ")+";
    }
    break;
  case Type::REPEAT_MIN:
    if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR
            or exp1_->type_ == Type::EMPTY) {
      ss << *exp1_ << "{" << std::to_string(min_) << ",}";
    } else {
      ss << '(' << *exp1_ << "){" << std::to_string(min_) << ",}";
    }
    break;
  case Type::REPEAT_MINMAX:
    if (exp1_->type_ == Type::CHAR or exp1_->type_ == Type::ANYCHAR
            or exp1_->type_ == Type::EMPTY) {
      ss << *exp1_ << "{" << std::to_string(min_) << "," << std::to_string(max_) << "}";
    } else {
      ss << '(' << *exp1_ << "){" << std::to_string(min_) << "," << std::to_string(max_) << "}";
    }
    break;
  case Type::COMPLEMENT:
    ss << "~(" << *exp1_ << ')';
    break;
  case Type::CHAR: {
    std::string character = "" + character_;
    if (character.find_first_of("&|?*+.@#(){}[]~\"\\")) {
      character = "\\" + character;
    }
    ss << character;
  };
    break;
  case Type::CHAR_RANGE: {
    std::string from = "" + from_char_;
    std::string to = "" + to_char_;
    if (from.find_first_of("^\\")) {
      from = "\\" + from;
    }

    if (to.find_first_of("^\\")) {
      to = "\\" + to;
    }

    ss << "[" << from << "-" << to << "]";
  };
    break;
  case Type::ANYCHAR:
    ss << '.';
    break;
  case Type::EMPTY:
    ss << '#';
    break;
  case Type::STRING: {// regex strings are quoted
    // if there is a quote escape it by getting out of string regex
    std::stringstream cleaner;
    for (auto c : string_) {
      if (c == '"') {
        if (cleaner.str() != "") {
          ss << '"' << cleaner.str() << '"';
          cleaner.str("");
        }
        ss << '\\' << '"';
      } else {
        cleaner << c;
      }
    }
    if (cleaner.str() != "") {
      ss << '"' << cleaner.str() << '"';
    }
  };
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

void RegularExpression::copy(RegularExpression_ptr e) {
  type_ = e->type_;
  exp1_ = e->exp1_;
  exp2_ = e->exp2_;
  this->string_ = e->string_;
  character_ = e->character_;
  min_ = e->min_;
  max_ = e->max_;
  digits_ = e->digits_;
  from_char_ = e->from_char_;
  to_char_ = e->to_char_;
  regex_string_ = "";
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
    left = "" + exp1->character_;
    is_left_constant = true;
  }

  if (exp2->type_ == Type::STRING) {
    right = exp2->string_;
    is_right_constant = true;
  } else if (exp2->type_ == Type::CHAR) {
    right = "" + exp2->character_;
    is_right_constant = true;
  }

  RegularExpression_ptr regex = new RegularExpression();
  if (is_left_constant and is_right_constant and left == right) { // optimize
    regex->type_ = Type::STRING;
    regex->string_ = left;
  } else if (exp1->type_ == Type::EMPTY) { // optimize
    regex->copy(exp2);
  } else if (exp2->type_ == Type::EMPTY) { // optimize
    regex->copy(exp1);
  } else {
    regex->type_ = Type::UNION;
    regex->exp1_ = exp1;
    regex->exp2_ = exp2;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeConcatenation(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  if ((exp1->type_ == Type::CHAR or exp1->type_ == Type::STRING)
          and (exp2->type_ == Type::CHAR or exp2->type_ == Type::STRING)) {
    return RegularExpression::makeString(exp1, exp2);
  }

  RegularExpression_ptr regex = new RegularExpression();
  if (exp1->type_ == Type::STRING and exp1->string_ == "") {
    regex->copy(exp2);
  } else if (exp2->type_ == Type::STRING and exp2->string_ == "") {
    regex->copy(exp1);
  } else {
    regex->type_ = Type::CONCATENATION;
    if (exp1->type_ == Type::CONCATENATION and (exp1->exp2_->type_ == Type::CHAR or exp1->exp2_->type_ == Type::STRING)
            and (exp2->type_ == Type::CHAR or exp2->type_ == Type::STRING)) {
      regex->exp1_ = exp1->exp1_;
      regex->exp2_ = RegularExpression::makeString(exp1->exp2_, exp2);
    } else if ((exp1->type_ == Type::CHAR or exp1->type_ == Type::STRING) and exp2->type_ == Type::CONCATENATION
            and (exp2->exp1_->type_ == Type::CHAR or exp2->exp1_->type_ == Type::STRING)) {
      regex->exp1_ = RegularExpression::makeString(exp1, exp2->exp1_);
      regex->exp2_ = exp2->exp2_;
    } else {
      regex->exp1_ = exp1;
      regex->exp2_ = exp2;
    }
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
    left = "" + exp1->character_;
    is_left_constant = true;
  }

  if (exp2->type_ == Type::STRING) {
    right = exp2->string_;
    is_right_constant = true;
  } else if (exp2->type_ == Type::CHAR) {
    right = "" + exp2->character_;
    is_right_constant = true;
  }

  RegularExpression_ptr regex = new RegularExpression();
  if (is_left_constant and is_right_constant and left == right) { // optimize
    regex->type_ = Type::STRING;
    regex->string_ = left;
  } else if (exp1->type_ == Type::EMPTY or exp2->type_ == Type::EMPTY) { // optimize
    regex->type_ = Type::EMPTY;
  } else {
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
  } else {
    regex->type_ = Type::OPTIONAL;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeatStar(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  if (exp->type_ == Type::EMPTY) { // optimize
    regex->type_ = Type::STRING;
    regex->string_ = "";
  } else if (exp->type_ == Type::STRING and exp->string_ == "") { // optimize
    regex->type_ = Type::STRING;
    regex->string_ = "";
  } else {
    regex->type_ = Type::REPEAT_STAR;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeatPlus(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  if (exp->type_ == Type::STRING and exp->string_ == "") {
    regex->type_ = Type::STRING;
    regex->string_ = "";
  } else {
    regex->type_ = Type::REPEAT_PLUS;
    regex->exp1_ = exp;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, unsigned long min) {
  RegularExpression_ptr regex = new RegularExpression();
  if (exp->type_ == Type::STRING and exp->string_ == "") { // optimize
    regex->type_ = Type::STRING;
    regex->string_ = "";
  } else {
    regex->type_ = Type::REPEAT_MIN;
    regex->exp1_ = exp;
    regex->min_ = min;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, unsigned long min, unsigned long max) {
  RegularExpression_ptr regex = new RegularExpression();
  if (min == 0 and max == 0) { // optimize empty string
    regex->type_ = Type::STRING;
    regex->string_ = "";
  } else if (min == max and exp->type_ == Type::STRING) { // optimize one constant string
    regex->type_ = Type::STRING;
    std::stringstream ss;
    for (unsigned long i = 0; i < min; ++i) {
      ss << exp->string_;
    }
    regex->string_ = ss.str();
  } else if (min == max and exp->type_ == Type::CHAR) { // optimize one constant string
    regex->type_ = Type::STRING;
    std::stringstream ss;
    for (unsigned long i = 0; i < min; ++i) {
      ss << exp->character_;
    }
    regex->string_ = ss.str();
  } else {
    regex->type_ = Type::REPEAT_MINMAX;
    regex->exp1_ = exp;
    regex->min_ = min;
    regex->max_ = max;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeComplement(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type_ = Type::COMPLEMENT;
  regex->exp1_ = exp;
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
  if (from == to) { // optimize
    regex->type_ = Type::CHAR;
    regex->character_ = from;
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
  if (more() and !peek(")&|")) {
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

      unsigned long n = std::stoul(regex_string_.substr(start, pos_ - start));
      unsigned long m;
      bool is_m_set = false;
      if (match(',')) {
        start = pos_;
        while (peek("0123456789")) {
          next();
        }

        if (start != pos_) {
          m = std::stoul(regex_string_.substr(start, pos_ - start));
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
    if (match('^')) {
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
  } else if (match('"')) {
    int start = (int) pos_;
    while (more() and !peek("\"")) {
      next();
    }

    if (!match('"')) {
      LOG(FATAL)<< "expected '\"' at position: " << pos_;
    }

    return RegularExpression::makeString(regex_string_.substr(start, (pos_ - 1 - start)));
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

    std::string s = regex_string_.substr(start, (pos_ - 1 - start));
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

RegularExpression::Type RegularExpression::getType() {
  return type_;
}

RegularExpression_ptr RegularExpression::getExpr1() {
  return exp1_;
}

RegularExpression_ptr RegularExpression::getExpr2() {
  return exp2_;
}

unsigned long RegularExpression::getMin() {
  return min_;
}

unsigned long RegularExpression::getMax() {
  return max_;
}

char RegularExpression::getChar() {
  return character_;
}

char RegularExpression::getFrom() {
  return from_char_;
}

char RegularExpression::getTo() {
  return to_char_;
}

std::string RegularExpression::getS() {
  return string_;
}

std::ostream& operator<<(std::ostream& os, const RegularExpression& regex) {
  return os << regex.toString();
}

RegularExpression_ptr RegularExpression::makeString(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
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

void RegularExpression::init(std::string regex, int syntax_flags) {

//  CHECK_EQ(0, regex.find("/"));
//  std::string::size_type last = regex.substr(1).find_last_of("/");
//  CHECK_NE(std::string::npos, last);
//
//  regex_string_ = regex.substr(1, last);

  regex_string_ = regex;
  flags_ = syntax_flags;
  RegularExpression_ptr e = parseUnionExp();

  if (pos_ < regex_string_.length()) {
    LOG(FATAL)<< "end-of-string expected at position: " << pos_;
  }

  type_ = e->type_;
  exp1_ = e->exp1_;
  exp2_ = e->exp2_;
  this->string_ = e->string_;
  character_ = e->character_;
  min_ = e->min_;
  max_ = e->max_;
  digits_ = e->digits_;
  from_char_ = e->from_char_;
  to_char_ = e->to_char_;
  regex_string_ = "";
}

bool RegularExpression::peek(std::string s) {
  return (more() and (s.find(regex_string_[pos_]) != std::string::npos));
}

bool RegularExpression::match(char c) {
  if (pos_ >= regex_string_.length()) {
    return false;
  }

  if (regex_string_[pos_] == c) {
    pos_++;
    return true;
  }
  return false;
}

bool RegularExpression::more() {
  return pos_ < regex_string_.length();
}

char RegularExpression::next() {
  if (!more()) {
    LOG(FATAL)<< "unexpected end-of-string";
  }

  return regex_string_[pos_++];
}

bool RegularExpression::check(int flag) {
  return (flags_ & flag) != 0;
}

} /* namespace Util */
} /* namespace Vlab */
