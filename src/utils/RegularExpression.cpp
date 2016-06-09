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
        : exp1(nullptr), exp2(nullptr), min(0), max(0), digits(0), flags(0), c('\0'), from('\0'), to('\0'), regex_string(
                ""), s(""), pos(0), type(Type::NONE) {

}

RegularExpression::RegularExpression(std::string regex)
        : exp1(nullptr), exp2(nullptr), min(0), max(0), digits(0), flags(0), c('\0'), from('\0'), to('\0'), regex_string(
                ""), s(""), pos(0), type(Type::NONE) {
  init(regex, DEFAULT);
}

RegularExpression::RegularExpression(std::string regex, int syntax_flags)
        : exp1(nullptr), exp2(nullptr), min(0), max(0), digits(0), flags(syntax_flags), c('\0'), from('\0'), to('\0'), regex_string(
                ""), s(""), pos(0), type(Type::NONE) {
  init(regex, syntax_flags);

}

RegularExpression::~RegularExpression() {
  delete exp1;
  delete exp2;
}

std::string RegularExpression::toString() const {
  std::stringstream ss;
  switch (type) {
  case Type::UNION:
    ss << '(' << *exp1 << '|' << *exp2 << ')';
    break;
  case Type::CONCATENATION:
    ss << *exp1 << *exp2;
    break;
  case Type::INTERSECTION:
    ss << '(' << *exp1 << '&' << *exp2 << ')';
    break;
  case Type::OPTIONAL:
    ss << '(' << *exp1 << ")?";
    break;
  case Type::REPEAT_STAR:
    ss << '(' << *exp1 << ")*";
    break;
  case Type::REPEAT_PLUS:
    ss << '(' << *exp1 << ")+";
    break;
  case Type::REPEAT_MIN:
    ss << '(' << *exp1 << "){" << std::to_string(min) << ",}";
    break;
  case Type::REPEAT_MINMAX:
    ss << '(' << *exp1 << "){" << std::to_string(min) << "," << std::to_string(max) << "}";
    break;
  case Type::COMPLEMENT:
    ss << "~(" << *exp1 << ')';
    break;
  case Type::CHAR:
    ss << c;
    break;
  case Type::CHAR_RANGE:
    ss << "[\\" << std::to_string(from) << "-\\" << std::to_string(to) << "]";
    break;
  case Type::ANYCHAR:
    ss << '.';
    break;
  case Type::EMPTY:
    ss << '#';
    break;
  case Type::STRING:
    ss << "\"" << s << "\"";
    break;
  case Type::ANYSTRING:
    ss << '@';
    break;
  case Type::AUTOMATON:
    ss << '<' << s << '>';
    break;
  case Type::INTERVAL: {
    std::string min_str = std::to_string(min);
    std::string max_str = std::to_string(max);
    ss << '<';
    if (digits > 0) {
      for (unsigned i = (unsigned) min_str.length(); i < digits; i++) {
        ss << '0';
      }
    }

    ss << min_str << '-';
    if (digits > 0) {
      for (unsigned i = (unsigned) max_str.length(); i < digits; i++) {
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

void RegularExpression::simplify() {
  if (exp1 != nullptr) {
    exp1->simplify();
  }

  if (exp2 != nullptr) {
    exp2->simplify();
  }

  Type re_type = type;
  switch (re_type) {
  case Type::UNION:
    if (exp1->type == Type::EMPTY) {
      copy(exp2);
    } else if (exp2->type == Type::EMPTY) {
      copy(exp1);
    }
    break;
  case Type::CONCATENATION:
    if (exp1->type == Type::STRING and exp1->s == "") {
      copy(exp2);
    } else if (exp2->type == Type::STRING and exp2->s == "") {
      copy(exp1);
    }
    break;
  case Type::REPEAT_STAR:
    if (exp1->type == Type::EMPTY) {
      type = Type::STRING;
      s = "";
    }
    break;
  case Type::CHAR_RANGE:
    if (from == to) {
      c = from;
      type = Type::CHAR;
    }
    break;
  default:
    break;
  }
}

void RegularExpression::copy(RegularExpression_ptr e) {
  type = e->type;
  exp1 = e->exp1;
  exp2 = e->exp2;
  this->s = e->s;
  c = e->c;
  min = e->min;
  max = e->max;
  digits = e->digits;
  from = e->from;
  to = e->to;
  regex_string = "";
}

RegularExpression_ptr RegularExpression::makeUnion(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::UNION;
  regex->exp1 = exp1;
  regex->exp2 = exp2;
  return regex;
}

RegularExpression_ptr RegularExpression::makeConcatenation(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  if ((exp1->type == Type::CHAR or exp1->type == Type::STRING)
          and (exp2->type == Type::CHAR or exp2->type == Type::STRING)) {
    return RegularExpression::makeString(exp1, exp2);
  }

  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::CONCATENATION;
  if (exp1->type == Type::CONCATENATION and (exp1->exp2->type == Type::CHAR or exp1->exp2->type == Type::STRING)
          and (exp2->type == Type::CHAR or exp2->type == Type::STRING)) {
    regex->exp1 = exp1->exp1;
    regex->exp2 = RegularExpression::makeString(exp1->exp2, exp2);
  } else if ((exp1->type == Type::CHAR or exp1->type == Type::STRING) and exp2->type == Type::CONCATENATION
          and (exp2->exp1->type == Type::CHAR or exp2->exp1->type == Type::STRING)) {
    regex->exp1 = RegularExpression::makeString(exp1, exp2->exp1);
    regex->exp2 = exp2->exp2;
  } else {
    regex->exp1 = exp1;
    regex->exp2 = exp2;
  }
  return regex;
}

RegularExpression_ptr RegularExpression::makeIntersection(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  RegularExpression_ptr r = new RegularExpression();
  r->type = Type::INTERSECTION;
  r->exp1 = exp1;
  r->exp2 = exp2;
  return r;
}

RegularExpression_ptr RegularExpression::makeOptional(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::OPTIONAL;
  regex->exp1 = exp;
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeatStar(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::REPEAT_STAR;
  regex->exp1 = exp;
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeatPlus(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::REPEAT_PLUS;
  regex->exp1 = exp;
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, unsigned long min) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::REPEAT_MIN;
  regex->exp1 = exp;
  regex->min = min;
  return regex;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, unsigned long min, unsigned long max) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::REPEAT_MINMAX;
  regex->exp1 = exp;
  regex->min = min;
  regex->max = max;
  return regex;
}

RegularExpression_ptr RegularExpression::makeComplement(RegularExpression_ptr exp) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::COMPLEMENT;
  regex->exp1 = exp;
  return regex;
}

RegularExpression_ptr RegularExpression::makeChar(char c) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::CHAR;
  regex->c = c;
  return regex;
}

RegularExpression_ptr RegularExpression::makeCharRange(char from, char to) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::CHAR_RANGE;
  regex->from = from;
  regex->to = to;
  return regex;
}

RegularExpression_ptr RegularExpression::makeAnyChar() {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::ANYCHAR;
  return regex;
}

RegularExpression_ptr RegularExpression::makeEmpty() {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::EMPTY;
  return regex;
}

RegularExpression_ptr RegularExpression::makeString(std::string s) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::STRING;
  regex->s = s;
  return regex;
}

RegularExpression_ptr RegularExpression::makeAnyString() {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::ANYSTRING;
  return regex;
}

RegularExpression_ptr RegularExpression::makeAutomaton(std::string s) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::AUTOMATON;
  regex->s = s;
  return regex;
}

RegularExpression_ptr RegularExpression::makeInterval(unsigned long min, unsigned long max, unsigned digits) {
  RegularExpression_ptr regex = new RegularExpression();
  regex->type = Type::INTERVAL;
  regex->min = min;
  regex->max = max;
  regex->digits = digits;
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
      std::string::size_type start = pos;
      while (peek("0123456789")) {
        next();
      }

      if (start == pos) {
        LOG(FATAL)<< "integer expected at position: " << pos;
      }

      unsigned long n = std::stoul(regex_string.substr(start, pos - start));
      unsigned long m;
      bool is_m_set = false;
      if (match(',')) {
        start = pos;
        while (peek("0123456789")) {
          next();
        }

        if (start != pos) {
          m = std::stoul(regex_string.substr(start, pos - start));
          is_m_set = true;
        }

      } else {
        m = n;
        is_m_set = true;
      }

      if (!match('}')) {
        LOG(FATAL)<< "expected '}' at position: " << pos;
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
      LOG(FATAL)<< "expected ']' at position: " << pos;
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
    int start = (int) pos;
    while (more() and !peek("\"")) {
      next();
    }

    if (!match('"')) {
      LOG(FATAL)<< "expected '\"' at position: " << pos;
    }

    return RegularExpression::makeString(regex_string.substr(start, (pos - 1 - start)));
  } else if (match('(')) {
    if (match(')')) {
      return RegularExpression::makeString("");
    }

    RegularExpression_ptr regex = parseUnionExp();

    if (!match(')')) {
      LOG(FATAL)<< "expected ')' at position: " << pos;
    }

    return regex;
  } else if ((check(AUTOMATON) or check(INTERVAL)) and match('<')) {
    int start = (int) pos;
    while (more() and !peek(">")) {
      next();
    }

    if (!match('>')) {
      LOG(FATAL)<< "expected '>' at position: " << pos;
    }

    std::string s = regex_string.substr(start, (pos - 1 - start));
    std::string::size_type i = s.find('-');
    if (i == std::string::npos) {
      if (!check(AUTOMATON)) {
        LOG(FATAL)<< "interval syntax error at position: " << (pos - 1);
      }

      return makeAutomaton(s);
    } else {
      if(!check(INTERVAL)) {
        LOG(FATAL) << "illegal identifier at position: " << (pos - 1);
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
  return type;
}

RegularExpression_ptr RegularExpression::getExpr1() {
  return exp1;
}

RegularExpression_ptr RegularExpression::getExpr2() {
  return exp2;
}

unsigned long RegularExpression::getMin() {
  return min;
}

unsigned long RegularExpression::getMax() {
  return max;
}

char RegularExpression::getChar() {
  return c;
}

char RegularExpression::getFrom() {
  return from;
}

char RegularExpression::getTo() {
  return to;
}

std::string RegularExpression::getS() {
  return s;
}

std::ostream& operator<<(std::ostream& os, const RegularExpression& regex) {
  return os << regex.toString();
}

RegularExpression_ptr RegularExpression::makeString(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
  std::stringstream ss;
  if (exp1->type == Type::STRING) {
    ss << exp1->s;
  } else {
    ss << exp1->c;
  }

  if (exp2->type == Type::STRING) {
    ss << exp2->s;
  } else {
    ss << exp2->c;
  }
  return RegularExpression::makeString(ss.str());
}

void RegularExpression::init(std::string regex, int syntax_flags) {

//  CHECK_EQ(0, regex.find("/"));
//  std::string::size_type last = regex.substr(1).find_last_of("/");
//  CHECK_NE(std::string::npos, last);
//
//  regex_string = regex.substr(1, last);

  regex_string = regex;
  flags = syntax_flags;
  RegularExpression_ptr e = parseUnionExp();

  if (pos < regex_string.length()) {
    LOG(FATAL)<< "end-of-string expected at position: " << pos;
  }

  type = e->type;
  exp1 = e->exp1;
  exp2 = e->exp2;
  this->s = e->s;
  c = e->c;
  min = e->min;
  max = e->max;
  digits = e->digits;
  from = e->from;
  to = e->to;
  regex_string = "";
}

bool RegularExpression::peek(std::string s) {
  return (more() and (s.find(regex_string[pos]) != std::string::npos));
}

bool RegularExpression::match(char c) {
  if (pos >= regex_string.length()) {
    return false;
  }

  if (regex_string[pos] == c) {
    pos++;
    return true;
  }
  return false;
}

bool RegularExpression::more() {
  return pos < regex_string.length();
}

char RegularExpression::next() {
  if (!more()) {
    LOG(FATAL)<< "unexpected end-of-string";
  }

  return regex_string[pos++];
}

bool RegularExpression::check(int flag) {
  return (flags & flag) != 0;
}

} /* namespace Util */
} /* namespace Vlab */
