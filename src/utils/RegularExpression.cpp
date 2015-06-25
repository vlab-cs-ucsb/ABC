/*
 * RegularExpression.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "RegularExpression.h"

namespace Vlab {
namespace Util {

int RegularExpression::id;

const int RegularExpression::VLOG_LEVEL = 9;

void RegularExpression::restID()
{
    id = 0;
}

void RegularExpression::simplify()
{
    if(exp1 != nullptr) {
        exp1->simplify();
    }
    if(exp2 != nullptr) {
        exp2->simplify();
    }
    {
        Type v = kind;
        if(v == Type::CHAR_RANGE) {
            if(from == to) {
                c = from;
                kind = Type::CHAR;
            }
            goto end_switch0;;
        }
        if(v == Type::UNION) {
            if(exp1->kind == Type::EMPTY) {
                copy(exp2);
            } else if(exp2->kind == Type::EMPTY) {
                copy(exp1);
            }
            goto end_switch0;;
        }
        if(v == Type::REPEAT_STAR) {
            if(exp1->kind == Type::EMPTY) {
                kind = Type::STRING;
                s = "";
            }
            goto end_switch0;;
        }
        if(v == Type::CONCATENATION) {
            if(exp1->kind == Type::STRING && exp1->s == "") {
                copy(exp2);
            } else if(exp2->kind == Type::STRING && exp2->s == "") {
                copy(exp1);
            }
            goto end_switch0;;
        }
end_switch0:;
    }

}

void RegularExpression::copy(RegularExpression_ptr e) {
    kind = e->kind;
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

RegularExpression::RegularExpression()
	: exp1 (nullptr), exp2 (nullptr), min (0), max(0), digits(0), flags(0),
	  c ('\0'), from ('\0'), to ('\0'), regex_string (""), s (""), pos(0),
	  kind (Type::NONE) {

}

RegularExpression::RegularExpression(std::string regex)
	: exp1 (nullptr), exp2 (nullptr), min (0), max(0), digits(0), flags(0),
	  c ('\0'), from ('\0'), to ('\0'), regex_string (""), s (""), pos(0),
	  kind (Type::NONE) {
	init(regex, ALL);
}

RegularExpression::RegularExpression(std::string regex, int syntax_flags)
	: exp1 (nullptr), exp2 (nullptr), min (0), max(0), digits(0), flags(0),
	  c ('\0'), from ('\0'), to ('\0'), regex_string (""), s (""), pos(0),
	  kind (Type::NONE) {
	init(regex, syntax_flags);

}

RegularExpression::~RegularExpression() { }

void RegularExpression::init(std::string regex, int syntax_flags) {

    regex_string = regex;
    flags = syntax_flags;
    RegularExpression_ptr e = parseUnionExp();

    if(pos < regex_string.length())
        throw std::invalid_argument((StringBuilder() << "end-of-string expected at position " << pos));


    kind = e->kind;
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

//StrangerAutomaton_ptr RegularExpression::toAutomaton() {
//    StrangerAutomaton_ptr a = nullptr;
//    StrangerAutomaton_ptr auto1;
//    StrangerAutomaton_ptr auto2;
//    {
//        Kind v = kind;
//        if(v == Kind::RegularExpression_UNION) {
//        	Log::i(TAG, "union");
//            auto1 = exp1->toAutomaton();
//            auto2 = exp2->toAutomaton();
//            a = auto1->union_(auto2, ++id);
//            delete auto1;
//            delete auto2;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_CONCATENATION) {
//        	Log::i(TAG, "concatenation");
//            auto1 = exp1->toAutomaton();
//            auto2 = exp2->toAutomaton();
//            a = auto1->concatenate(auto2, ++id);
//            delete auto1;
//            delete auto2;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_INTERSECTION) {
//        	Log::i(TAG, "intersection");
//            auto1 = exp1->toAutomaton();
//            auto2 = exp2->toAutomaton();
//            a = auto1->intersect(auto2, ++id);
//            delete auto1;
//            delete auto2;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_OPTIONAL) {
//        	Log::i(TAG, "optional");
//            auto1 = exp1->toAutomaton();
//            a = auto1->optional(++id);
//            delete auto1;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_REPEAT_STAR) {
//            auto1 = exp1->toAutomaton();
//            a = auto1->kleensStar(++id);
//            delete auto1;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_REPEAT_PLUS) {
//        	Log::i(TAG, "repeat plus");
//            auto1 = exp1->toAutomaton();
//            a = auto1->closure(++id);
//            delete auto1;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_REPEAT_MIN) {
//        	Log::i(TAG, "repeat min");
//            auto1 = exp1->toAutomaton();
//            a = auto1->repeat(min, ++id);
//            delete auto1;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_REPEAT_MINMAX) {
//        	Log::i(TAG, "repeat minmax");
//            auto1 = exp1->toAutomaton();
//            a = auto1->repeat(min, max, ++id);
//            delete auto1;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_COMPLEMENT) {
//        	Log::i(TAG, "complement");
//            auto1 = exp1->toAutomaton();
//            a = auto1->complement(++id);
//            delete auto1;
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_CHAR) {
//        	Log::i(TAG, "char");
//            a = StrangerAutomaton::makeChar(c, ++id);
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_CHAR_RANGE) {
//        	Log::i(TAG, "char range");
//            a = StrangerAutomaton::makeCharRange(from, to, ++id);
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_ANYCHAR) {
//        	Log::i(TAG, "any char");
//            a = StrangerAutomaton::makeDot(++id);
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_EMPTY) {
//        	Log::i(TAG, "empty");
//            a = StrangerAutomaton::makeEmptyString(++id);
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_STRING) {
//        	Log::i(TAG, "string");
//            a = StrangerAutomaton::makeString(s, ++id);
//            goto end_switch1;;
//        }
//        if(v == Kind::RegularExpression_ANYSTRING) {
//        	Log::i(TAG, "any string");
//            a = StrangerAutomaton::makeAnyString(++id);
//            goto end_switch1;;
//        }
//end_switch1:;
//    }
//
//    return a;
//}

std::string RegularExpression::toString()
{
	std::string s;
    return toStringBuilder(s);
}

std::string RegularExpression::toStringBuilder(std::string b)
{
    {
        std::string s1;
        std::string s2;
        {
            Type v = kind;
            if(v == Type::UNION) {
                b.append("(");
                exp1->toStringBuilder(b);
                b.append("|");
                exp2->toStringBuilder(b);
                b.append(")");
                goto end_switch2;;
            }
            if(v == Type::CONCATENATION) {
                exp1->toStringBuilder(b);
                exp2->toStringBuilder(b);
                goto end_switch2;;
            }
            if(v == Type::INTERSECTION) {
                b.append("(");
                exp1->toStringBuilder(b);
                b.append("&");
                exp2->toStringBuilder(b);
                b.append(")");
                goto end_switch2;;
            }
            if(v == Type::OPTIONAL) {
                b.append("(");
                exp1->toStringBuilder(b);
                b.append(")?");
                goto end_switch2;;
            }
            if(v == Type::REPEAT_STAR) {
                b.append("(");
                exp1->toStringBuilder(b);
                b.append(")*");
                goto end_switch2;;
            }
            if(v == Type::REPEAT_MIN) {
                b.append("(");
                exp1->toStringBuilder(b);
                b.append("){").append(std::to_string(min)).append(",}");
                goto end_switch2;;
            }
            if(v == Type::REPEAT_MINMAX) {
                b.append("(");
                exp1->toStringBuilder(b);
                b.append("){").append(std::to_string(min)).append(",").append(std::to_string(max)).append("}");
                goto end_switch2;;
            }
            if(v == Type::COMPLEMENT) {
                b.append("~(");
                exp1->toStringBuilder(b);
                b.append(")");
                goto end_switch2;;
            }
            if(v == Type::CHAR) {
                b.append(1, c);
                goto end_switch2;;
            }
            if(v == Type::CHAR_RANGE) {
                b.append("[\\").append(std::to_string(from)).append("-\\").append(std::to_string(to)).append("]");
                goto end_switch2;;
            }
            if(v == Type::ANYCHAR) {
                b.append(".");
                goto end_switch2;;
            }
            if(v == Type::EMPTY) {
                b.append("#");
                goto end_switch2;;
            }
            if(v == Type::STRING) {
                b.append("\"").append(s).append("\"");
                goto end_switch2;;
            }
            if(v == Type::ANYSTRING) {
                b.append("@");
                goto end_switch2;;
            }
            if(v == Type::AUTOMATON) {
                b.append("<").append(s).append(">");
                goto end_switch2;;
            }
            if(v == Type::INTERVAL) {
                std::string s1 = std::to_string(min);
                std::string s2 = std::to_string(max);
                b.append("<");
                if(digits > 0)
                    for (int i = (int)s1.length(); i < digits; i++)
						b.append("0");


                b.append(s1).append("-");
                if(digits > 0)
                    for (int i = (int)s2.length(); i < digits; i++)
						b.append("0");


                b.append(s2).append(">");
                goto end_switch2;;
            }
end_switch2:;
        }
    }

    return b;
}

RegularExpression_ptr RegularExpression::makeUnion(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::UNION;
    r->exp1 = exp1;
    r->exp2 = exp2;
    return r;
}

RegularExpression_ptr RegularExpression::makeConcatenation(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
    if((exp1->kind == Type::CHAR || exp1->kind == Type::STRING) && (exp2->kind == Type::CHAR || exp2->kind == Type::STRING))
        return makeString(exp1, exp2);

    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::CONCATENATION;
    if(exp1->kind == Type::CONCATENATION && (exp1->exp2->kind == Type::CHAR || exp1->exp2->kind == Type::STRING) && (exp2->kind == Type::CHAR || exp2->kind == Type::STRING)) {
        r->exp1 = exp1->exp1;
        r->exp2 = makeString(exp1->exp2, exp2);
    } else if((exp1->kind == Type::CHAR || exp1->kind == Type::STRING) && exp2->kind == Type::CONCATENATION && (exp2->exp1->kind == Type::CHAR || exp2->exp1->kind == Type::STRING)) {
        r->exp1 = makeString(exp1, exp2->exp1);
        r->exp2 = exp2->exp2;
    } else {
        r->exp1 = exp1;
        r->exp2 = exp2;
    }
    return r;
}

RegularExpression_ptr RegularExpression::makeString(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
    std::string b;
    if(exp1->kind == Type::STRING)
        b.append(exp1->s);
    else
        b.append(1, exp1->c);
    if(exp2->kind == Type::STRING)
        b.append(exp2->s);
    else
        b.append(1, exp2->c);
    return makeString(b);
}

RegularExpression_ptr RegularExpression::makeIntersection(RegularExpression_ptr exp1, RegularExpression_ptr exp2) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::INTERSECTION;
    r->exp1 = exp1;
    r->exp2 = exp2;
    return r;
}

RegularExpression_ptr RegularExpression::makeOptional(RegularExpression_ptr exp) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::OPTIONAL;
    r->exp1 = exp;
    return r;
}

RegularExpression_ptr RegularExpression::makeRepeatStar(RegularExpression_ptr exp) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::REPEAT_STAR;
    r->exp1 = exp;
    return r;
}

RegularExpression_ptr RegularExpression::makeRepeatPlus(RegularExpression_ptr exp) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::REPEAT_PLUS;
    r->exp1 = exp;
    return r;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, int min) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::REPEAT_MIN;
    r->exp1 = exp;
    r->min = min;
    return r;
}

RegularExpression_ptr RegularExpression::makeRepeat(RegularExpression_ptr exp, int min, int max) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::REPEAT_MINMAX;
    r->exp1 = exp;
    r->min = min;
    r->max = max;
    return r;
}

RegularExpression_ptr RegularExpression::makeComplement(RegularExpression_ptr exp) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::COMPLEMENT;
    r->exp1 = exp;
    return r;
}

RegularExpression_ptr RegularExpression::makeChar(char c) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::CHAR;
    r->c = c;
    return r;
}

RegularExpression_ptr RegularExpression::makeCharRange(char from, char to) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::CHAR_RANGE;
    r->from = from;
    r->to = to;
    return r;
}

RegularExpression_ptr RegularExpression::makeAnyChar() {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::ANYCHAR;
    return r;
}

RegularExpression_ptr RegularExpression::makeEmpty() {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::EMPTY;
    return r;
}

RegularExpression_ptr RegularExpression::makeString(std::string s) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::STRING;
    r->s = s;
    return r;
}

RegularExpression_ptr RegularExpression::makeAnyString() {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::ANYSTRING;
    return r;
}

RegularExpression_ptr RegularExpression::makeAutomaton(std::string s) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::AUTOMATON;
    r->s = s;
    return r;
}

RegularExpression_ptr RegularExpression::makeInterval(int min, int max, int digits) {
    RegularExpression_ptr r = (new RegularExpression());
    r->kind = Type::INTERVAL;
    r->min = min;
    r->max = max;
    r->digits = digits;
    return r;
}

bool RegularExpression::peek(std::string s) {
    return more() && (s.find(regex_string[pos]) != std::string::npos);
}

bool RegularExpression::match(char c) {
    if(pos >= regex_string.length())
        return false;

    if(regex_string[pos] == c) {
        pos++;
        return true;
    }
    return false;
}

bool RegularExpression::more() {
    return pos < regex_string.length();
}

char RegularExpression::next() {
    if(!more())
    	throw std::invalid_argument((StringBuilder() << "unexpected end-of-string"));

    return regex_string[pos++];
}

bool RegularExpression::check(int flag) {
    return (flags & flag) != 0;
}

RegularExpression_ptr RegularExpression::parseUnionExp() {
    RegularExpression_ptr e = parseInterExp();
    if(match('|'))
        e = makeUnion(e, parseUnionExp());

    return e;
}

RegularExpression_ptr RegularExpression::parseInterExp() {
    RegularExpression_ptr e = parseConcatExp();
    if(check(INTERSECTION) && match('&'))
        e = makeIntersection(e, parseInterExp());

    return e;
}

RegularExpression_ptr RegularExpression::parseConcatExp() {
    RegularExpression_ptr e = parseRepeatExp();
    if(more() && !peek(")&|"))
        e = makeConcatenation(e, parseConcatExp());

    return e;
}

RegularExpression_ptr RegularExpression::parseRepeatExp() {
    RegularExpression_ptr e = parseComplExp();
    while (peek("?*+{")) {
        if(match('?'))
            e = makeOptional(e);
        else if(match('*'))
            e = makeRepeatStar(e);
        else if(match('+'))
            e = makeRepeatPlus(e);
        else if(match('{')) {
            std::string::size_type start = pos;
            while (peek("0123456789"))
                                next();

            if(start == pos)
            	throw std::invalid_argument((StringBuilder() << "integer expected at position " << pos));

            int n = std::stoi(regex_string.substr(start, pos - start));
            int m = -1;
            if(match(',')) {
                start = pos;
                while (peek("0123456789"))
                                        next();

                if(start != pos)
                    m = std::stoi(regex_string.substr(start, pos - start));

            } else
                m = n;
            if(!match('}'))
            	throw std::invalid_argument((StringBuilder() << "expected '}' at position " << pos));

            if(m == -1)
                return makeRepeat(e, n);
            else
                return makeRepeat(e, n, m);
        }
    }
    return e;
}

RegularExpression_ptr RegularExpression::parseComplExp() {
    if(check(COMPLEMENT) && match('~'))
        return makeComplement(parseComplExp());
    else
        return parseCharClassExp();
}

RegularExpression_ptr RegularExpression::parseCharClassExp() {
    if(match('[')) {
        bool negate = false;
        if(match('^'))
            negate = true;

        RegularExpression_ptr e = parseCharClasses();
        if(negate)
            e = makeIntersection(makeAnyChar(), makeComplement(e));

        if(!match(']'))
        	throw std::invalid_argument((StringBuilder() << "expected ']' at position " << pos));

        return e;
    } else
        return parseSimpleExp();
}

RegularExpression_ptr RegularExpression::parseCharClasses() {
    RegularExpression_ptr e = parseCharClass();
    while (more() && !peek("]"))
                e = makeUnion(e, parseCharClass());

    return e;
}

RegularExpression_ptr RegularExpression::parseCharClass() {
    char c = parseCharExp();
    if(match('-'))
        return makeCharRange(c, parseCharExp());
    else
        return makeChar(c);
}

RegularExpression_ptr RegularExpression::parseSimpleExp() {
    if(match('.'))
        return makeAnyChar();
    else if(check(EMPTY) && match('#'))
        return makeEmpty();
    else if(check(ANYSTRING) && match('@'))
        return makeAnyString();
    else if(match('"')) {
        int start = (int)pos;
        while (more() && !peek("\""))
                        next();

        if(!match('"'))
        	throw std::invalid_argument((StringBuilder() << "expected '\"' at position " << pos));

        return makeString(regex_string.substr(start, (pos - 1 - start)));
    } else if(match('(')) {
        if(match(')'))
            return makeString("");

        RegularExpression_ptr e = parseUnionExp();
        if(!match(')'))
        	throw std::invalid_argument((StringBuilder() << "expected ')' at position " << pos));

        return e;
    } else if((check(AUTOMATON) || check(INTERVAL)) && match('<')) {
        int start = (int)pos;
        while (more() && !peek(">"))
                        next();

        if(!match('>'))
        	throw std::invalid_argument((StringBuilder() << "expected '>' at position " << pos));

        std::string s = regex_string.substr(start, (pos - 1 - start));
        std::string::size_type i = s.find('-');
        if(i == std::string::npos) {
            if(!check(AUTOMATON))
            	throw std::invalid_argument((StringBuilder() << "interval syntax error at position " << (pos - 1)));

            return makeAutomaton(s);
        } else {
            if(!check(INTERVAL))
            	throw std::invalid_argument((StringBuilder() << "illegal identifier at position " << (pos - 1)));

            try {
                if(i == 0 || i == s.length() - 1 || i != s.find_last_of('-'))
                	throw std::invalid_argument((StringBuilder() << "Number Format Error"));

                std::string smin = s.substr(0, i);
                std::string smax = s.substr(i + 1, (s.length()-(i + 1)));
                int imin = std::stoi(smin);
                int imax = std::stoi(smax);
                int digits;
                if(smin.length() == smax.length())
                    digits = (int)smin.length();
                else
                    digits = 0;
                if(imin > imax) {
                    int t = imin;
                    imin = imax;
                    imax = t;
                }
                return makeInterval(imin, imax, digits);
            } catch (std::exception& e) {
                throw (std::invalid_argument((StringBuilder() << "interval syntax error at position " << (pos - 1))));
            }
        }
    } else
        return makeChar(parseCharExp());
}

char RegularExpression::parseCharExp() {
    match('\\');
    return next();
}

} /* namespace Util */
} /* namespace Vlab */
