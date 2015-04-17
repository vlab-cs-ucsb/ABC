/*
 * enums.h
 *
 *  Created on: Dec 3, 2014
 *      Author: baki
 */

#ifndef SMT_ENUMS_H_
#define SMT_ENUMS_H_

#include <map>

namespace Vlab { namespace SMT {

enum class type_VAR : u_int8_t {
	NONE = 0, BOOL, INT, STRING
};

static std::map<type_VAR, std::string> _varStringMap = {
		{type_VAR::NONE, "None"},
		{type_VAR::BOOL, "Bool"},
		{type_VAR::INT, "Int"},
		{type_VAR::STRING, "String"}
};

enum class type_CMD : u_int8_t {
	NONE = 0, SET_LOGIC, SET_OPTION, SET_INFO, DECLARE_SORT, DEFINE_SORT, DECLARE_FUN, DEFINE_FUN,
	PUSH, POP, ASSERT, CHECK_SAT, GET_ASSERTIONS, GET_PROOF, GET_UNSAT_CORE, GET_VALUE,
	GET_ASSIGNMENT, GET_OPTION, GET_INFO, EXIT
};

enum class type_Primitive {
	NONE = 0, BINARY, DECIMAL, HEXADECIMAL, KEYWORD,
	NUMERAL, STRING, REGEX, SYMBOL
};


template <typename T>
static inline std::string enumToStr(T type) {
	throw new std::runtime_error("unknown enum type");
}

template<>
std::string enumToStr<type_VAR>(type_VAR type) {
	return _varStringMap[type];
}


} /* namespace SMT */
} /* namespace Vlab */



#endif /* SMT_ENUMS_H_ */
