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

enum class type_VAR {
	NONE = 0, BOOL, INT, STRING
};

static std::map<type_VAR, std::string> _varStringMap = {
		{type_VAR::NONE, "None"},
		{type_VAR::BOOL, "Bool"},
		{type_VAR::INT, "Int"},
		{type_VAR::STRING, "String"}
};

enum class type_CMD {
	NONE = 0, SET_LOGIC, SET_OPTION, SET_INFO, DECLARE_SORT, DEFINE_SORT, DECLARE_FUN, DEFINE_FUN,
	PUSH, POP, ASSERT, CHECK_SAT, CHECK_SAT_AND_COUNT, GET_ASSERTIONS, GET_PROOF, GET_UNSAT_CORE, GET_VALUE,
	GET_ASSIGNMENT, GET_OPTION, GET_INFO, EXIT
};

static std::map<type_CMD, std::string> _commandStringMap = {
		{type_CMD::NONE, "None"},
		{type_CMD::SET_LOGIC, "set-logic"},
		{type_CMD::SET_OPTION, "set-option"},
		{type_CMD::SET_INFO, "set-info"},
		{type_CMD::DECLARE_SORT, "declare-sort"},
		{type_CMD::DEFINE_SORT, "define-sort"},
		{type_CMD::DECLARE_FUN, "declare-fun"},
		{type_CMD::DEFINE_FUN, "define-fun"},
		{type_CMD::PUSH, "push"},
		{type_CMD::POP, "pop"},
		{type_CMD::ASSERT, "assert"},
		{type_CMD::CHECK_SAT, "check-sat"},
		{type_CMD::CHECK_SAT_AND_COUNT, "check-sat-and-count"},
		{type_CMD::GET_ASSERTIONS, "get-assertions"},
		{type_CMD::GET_PROOF, "get-proof"},
		{type_CMD::GET_UNSAT_CORE, "get-unsat-core"},
		{type_CMD::GET_VALUE, "get-value"},
		{type_CMD::GET_ASSIGNMENT, "get-assignment"},
		{type_CMD::GET_OPTION, "get-option"},
		{type_CMD::GET_INFO, "get-info"},
		{type_CMD::EXIT, "exit"}
};

enum class type_Primitive {
	NONE = 0, BINARY, DECIMAL, HEXADECIMAL, KEYWORD,
	NUMERAL, STRING, REGEX, SYMBOL
};

static std::map<type_Primitive, std::string> _primitiveStringMap = {
		{type_Primitive::NONE, "None"},
		{type_Primitive::BINARY, "BINARY"},
		{type_Primitive::DECIMAL, "DECIMAL"},
		{type_Primitive::HEXADECIMAL, "HEXADECIMAL"},
		{type_Primitive::KEYWORD, "KEYWORD"},
		{type_Primitive::NUMERAL, "NUMERAL"},
		{type_Primitive::STRING, "STRING"},
		{type_Primitive::REGEX, "REGEX"},
		{type_Primitive::SYMBOL, "SYMBOL"}
};


template <typename T>
static inline std::string enumToStr(T type) {
	throw new std::runtime_error("unknown enum type");
}

template<>
std::string enumToStr<type_VAR>(type_VAR type) {
	return _varStringMap[type];
}

template<>
std::string enumToStr<type_CMD>(type_CMD type) {
	return _commandStringMap[type];
}

template<>
std::string enumToStr<type_Primitive>(type_Primitive type) {
	return _primitiveStringMap[type];
}


} /* namespace SMT */
} /* namespace Vlab */



#endif /* SMT_ENUMS_H_ */
