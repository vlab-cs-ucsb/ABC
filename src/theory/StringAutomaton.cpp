/*
 * StringAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "StringAutomaton.h"

namespace Vlab {
namespace Theory {

const int StringAutomaton::VLOG_LEVEL = 8;

int StringAutomaton::DEFAULT_NUM_OF_VARIABLES = 8;

int* StringAutomaton::DEFAULT_VARIABLE_INDICES = StringAutomaton::allocateAscIIIndexWithExtraBit(
        StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

unsigned* StringAutomaton::DEFAULT_UNSIGNED_VARIABLE_INDICES = StringAutomaton::get_unsigned_indices_main(
        StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

StringAutomaton::StringAutomaton(DFA_ptr dfa)
        : Automaton(Automaton::Type::STRING), dfa (dfa), num_of_variables(StringAutomaton::DEFAULT_NUM_OF_VARIABLES) {
}

StringAutomaton::StringAutomaton(DFA_ptr dfa, int num_of_variables)
        : Automaton(Automaton::Type::STRING), dfa(dfa), num_of_variables(num_of_variables) {
}

StringAutomaton::StringAutomaton(const StringAutomaton& other)
        : Automaton(Automaton::Type::STRING), dfa(dfaCopy(other.dfa)), num_of_variables(other.num_of_variables) {
}

StringAutomaton::~StringAutomaton() {
//  DVLOG(VLOG_LEVEL) << "delete " << " [" << this->id << "]";
  dfaFree(dfa);
  dfa = nullptr;
}

StringAutomaton_ptr StringAutomaton::clone() const {
  StringAutomaton_ptr cloned_auto = new StringAutomaton(*this);
  DVLOG(VLOG_LEVEL) << cloned_auto->id << " = [" << this->id << "]->clone()";
  return cloned_auto;
}

/**
 * Creates an automaton that accepts nothing
 */
StringAutomaton_ptr StringAutomaton::makePhi(int num_of_variables, int* variable_indices) {
  DFA_ptr non_value_string_dfa = nullptr;
  StringAutomaton_ptr non_value_string = nullptr;
  std::array<char, 1> statuses { '-' };
  dfaSetup(1, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(0);
  non_value_string_dfa = dfaBuild(&*statuses.begin());
  non_value_string = new StringAutomaton(non_value_string_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << non_value_string->id << " = makePhi()";

  return non_value_string;
}

StringAutomaton_ptr StringAutomaton::makeEmptyString(int num_of_variables, int* variable_indices) {
  DFA_ptr empty_string_dfa = nullptr;
  StringAutomaton_ptr empty_string = nullptr;
  std::array<char, 2> statuses { '+', '-' };

  dfaSetup(2, num_of_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  empty_string_dfa = dfaBuild(&*statuses.begin());
  empty_string = new StringAutomaton(empty_string_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << empty_string->id << " = makeEmptyString()";

  return empty_string;
}

StringAutomaton_ptr StringAutomaton::makeString(std::string str, int num_of_variables, int* variable_indices) {
  if (str.empty()) {
    return StringAutomaton::makeEmptyString();
  }

  char* binary_char = nullptr;
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;
  int str_length = str.length();
  int number_of_states = str_length + 2;
  char* statuses = new char[number_of_states];

  dfaSetup(number_of_states, num_of_variables, variable_indices);

  int i;
  for (i = 0; i < str_length; i++) {
    dfaAllocExceptions(1);
    binary_char = StringAutomaton::binaryFormat((unsigned long) str[i], num_of_variables);
    dfaStoreException(i + 1, binary_char);
    delete binary_char;
    dfaStoreState(str_length + 1);
    statuses[i] = '-';
  }

  dfaAllocExceptions(0);
  dfaStoreState(str_length + 1);
  statuses[str_length] = '+';
  CHECK_EQ(str_length, i);

  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(str_length + 1);
  statuses[str_length + 1] = '-';

  result_dfa = dfaBuild(statuses);
  result_auto = new StringAutomaton(result_dfa, num_of_variables);
  delete statuses;

  DVLOG(VLOG_LEVEL) << result_auto->id << " = makeString(\"" << str << "\")";

  return result_auto;
}

/**
 * Returns Sigma* except two reserved words (11111111, 11111110)
 *
 */
StringAutomaton_ptr StringAutomaton::makeAnyString(int num_of_variables, int* variable_indices) {
  DFA_ptr any_string_dfa = nullptr;
  StringAutomaton_ptr any_string = nullptr;
  std::array<char, 2> statuses { '+', '-' };
  std::vector<char> reserved_1 = StringAutomaton::getReservedWord('1', num_of_variables);
  std::vector<char> reserved_2 = StringAutomaton::getReservedWord('0', num_of_variables);
  char* sharp1 = &*reserved_1.begin();
  char* sharp0 = &*reserved_2.begin();

  dfaSetup(2, num_of_variables, variable_indices);
  dfaAllocExceptions(2);
  dfaStoreException(1, sharp1); // word 11111111
  dfaStoreException(1, sharp0); // word 11111110
  dfaStoreState(0);

  dfaAllocExceptions(0);
  dfaStoreState(1);

  any_string_dfa = dfaBuild(&*statuses.begin());
  any_string = new StringAutomaton(any_string_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << any_string->id << " = makeAnyString()";

  return any_string;
}

StringAutomaton_ptr StringAutomaton::makeChar(char c, int num_of_variables, int* variable_indices) {
  std::stringstream ss;
  ss << c;
  return StringAutomaton::makeString(ss.str(), num_of_variables, variable_indices);
}

/**
 * Generates dfa for range [from-to]
 */
StringAutomaton_ptr StringAutomaton::makeCharRange(char from, char to, int num_of_variables, int* variable_indices) {
  int from_char = (int) from;
  int to_char = (int) to;
  int index;
  int initial_state;
  std::array<char, 3> statuses { '-', '+', '-' };
  DFA_ptr range_dfa = nullptr;
  StringAutomaton_ptr range_auto = nullptr;

  if (from_char > to_char) {
    int tmp = from_char;
    from_char = to_char;
    to_char = tmp;
  }

  initial_state = to_char - from_char;

  dfaSetup(3, num_of_variables, variable_indices);

  //state 0
  dfaAllocExceptions(initial_state + 1);
  for (index = from_char; index <= to_char; index++) {
    dfaStoreException(1, bintostr(index, num_of_variables));
  }
  dfaStoreState(2);

  //state 1
  dfaAllocExceptions(0);
  dfaStoreState(2);

  //state 2
  dfaAllocExceptions(0);
  dfaStoreState(2);

  range_dfa = dfaBuild(&*statuses.begin());
  range_auto = new StringAutomaton(range_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << range_auto->id << " = makeCharRange('" << from << "', '" << to << "')";

  return range_auto;
}

/**
 * Regular expressions '.' operator
 */
StringAutomaton_ptr StringAutomaton::makeAnyChar(int num_of_variables, int* variable_indices) {
  std::array<char, 3> statuses { '-', '+', '-' };
  std::vector<char> reserved_1 = StringAutomaton::getReservedWord('1', num_of_variables);
  std::vector<char> reserved_2 = StringAutomaton::getReservedWord('0', num_of_variables);
  char* sharp1 = &*reserved_1.begin();
  char* sharp0 = &*reserved_2.begin();
  DFA_ptr dot_dfa = nullptr;
  StringAutomaton_ptr dot_auto = nullptr;

  dfaSetup(3, num_of_variables, variable_indices);

  dfaAllocExceptions(2);
  dfaStoreException(2, sharp1); // word 11111111
  dfaStoreException(2, sharp0); // word 11111110
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(2);
  dfaAllocExceptions(0);
  dfaStoreState(2);

  dot_dfa = dfaBuild(&*statuses.begin());
  dot_auto = new StringAutomaton(dot_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << dot_auto->id << " = makeAnyChar()";

  return dot_auto;
}

StringAutomaton_ptr StringAutomaton::makeRegexAuto(std::string regex, int num_of_variables, int* variable_indices) {
  StringAutomaton_ptr regex_auto = nullptr;

  Util::RegularExpression_ptr regular_expression = new Util::RegularExpression(regex);
  regex_auto = StringAutomaton::makeRegexAuto(regular_expression);

  DVLOG(VLOG_LEVEL) << regex_auto->id << " = makeRegexAuto(" << regex << ")";

  return regex_auto;
}

StringAutomaton_ptr StringAutomaton::makeRegexAuto(Util::RegularExpression_ptr regular_expression) {
  StringAutomaton_ptr regex_auto = nullptr;
  StringAutomaton_ptr regex_expr1_auto = nullptr;
  StringAutomaton_ptr regex_expr2_auto = nullptr;

  switch (regular_expression->getType()) {
  case Util::RegularExpression::Type::UNION:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_expr2_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr2());
    regex_auto = regex_expr1_auto->union_(regex_expr2_auto);
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    delete regex_expr2_auto;
    regex_expr2_auto = nullptr;
    break;
  case Util::RegularExpression::Type::CONCATENATION:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_expr2_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr2());
    regex_auto = regex_expr1_auto->concatenate(regex_expr2_auto);
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    delete regex_expr2_auto;
    regex_expr2_auto = nullptr;
    break;
  case Util::RegularExpression::Type::INTERSECTION:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_expr2_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr2());
    regex_auto = regex_expr1_auto->intersect(regex_expr2_auto);
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    delete regex_expr2_auto;
    regex_expr2_auto = nullptr;
    break;
  case Util::RegularExpression::Type::OPTIONAL:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_auto = regex_expr1_auto->optional();
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    break;
  case Util::RegularExpression::Type::REPEAT_STAR:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_auto = regex_expr1_auto->kleeneClosure();
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    break;
  case Util::RegularExpression::Type::REPEAT_PLUS:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_auto = regex_expr1_auto->closure();
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    break;
  case Util::RegularExpression::Type::REPEAT_MIN:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_auto = regex_expr1_auto->repeat(regular_expression->getMin());
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    break;
  case Util::RegularExpression::Type::REPEAT_MINMAX:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_auto = regex_expr1_auto->repeat(regular_expression->getMin(), regular_expression->getMax());
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    break;
  case Util::RegularExpression::Type::COMPLEMENT:
    regex_expr1_auto = StringAutomaton::makeRegexAuto(regular_expression->getExpr1());
    regex_auto = regex_expr1_auto->complement();
    delete regex_expr1_auto;
    regex_expr1_auto = nullptr;
    break;
  case Util::RegularExpression::Type::CHAR:
    regex_auto = StringAutomaton::makeChar(regular_expression->getChar());
    break;
  case Util::RegularExpression::Type::CHAR_RANGE:
    regex_auto = StringAutomaton::makeCharRange(regular_expression->getFrom(), regular_expression->getTo());
    break;
  case Util::RegularExpression::Type::ANYCHAR:
    regex_auto = StringAutomaton::makeAnyChar();
    break;
  case Util::RegularExpression::Type::EMPTY:
    regex_auto = StringAutomaton::makePhi();
    break;
  case Util::RegularExpression::Type::STRING:
    regex_auto = StringAutomaton::makeString(regular_expression->getS());
    break;
  case Util::RegularExpression::Type::ANYSTRING:
    regex_auto = StringAutomaton::makeAnyString();
    break;
  case Util::RegularExpression::Type::AUTOMATON:
    LOG(FATAL)<< "Unsported regular expression" << *regular_expression;
    break;
    case Util::RegularExpression::Type::INTERVAL:
    {
      LOG(FATAL) << "Unsported regular expression" << *regular_expression;
      break;
    }
    default:
    LOG(FATAL) << "Unsported regular expression" << *regular_expression;
    break;
  }

  return regex_auto;
}

/**
 * TODO Try to avoid intersection during complement, figure out a better way
 *
 */
StringAutomaton_ptr StringAutomaton::complement() {
  DFA_ptr complement_dfa = nullptr, minimized_dfa = nullptr, current_dfa = dfaCopy(dfa);
  StringAutomaton_ptr complement_auto = nullptr;
  StringAutomaton_ptr any_string = StringAutomaton::makeAnyString();

  dfaNegation(current_dfa);
  complement_dfa = dfaProduct(any_string->dfa, current_dfa, dfaAND);
  delete any_string;
  any_string = nullptr;
  dfaFree(current_dfa);
  current_dfa = nullptr;

  minimized_dfa = dfaMinimize(complement_dfa);
  dfaFree(complement_dfa);
  complement_dfa = nullptr;

  complement_auto = new StringAutomaton(minimized_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << complement_auto->id << " = [" << this->id << "]->makeComplement()";

  return complement_auto;
}

/**
 * TODO Figure out why empty check is necessary
 */
StringAutomaton_ptr StringAutomaton::union_(StringAutomaton_ptr other_auto) {
  DFA_ptr union_dfa = nullptr, minimized_dfa = nullptr;
  StringAutomaton_ptr union_auto = nullptr;

  union_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaOR);
  minimized_dfa = dfaMinimize(union_dfa);
  dfaFree(union_dfa);
  union_dfa = nullptr;

  //  if ( this->hasEmptyString() || other_auto->hasEmptyString() ) {
  //    tmpM = dfa_union_empty_M(result, var, indices);
  //    dfaFree(result); result = NULL;
  //    result = tmpM;
  //  }

  union_auto = new StringAutomaton(minimized_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << union_auto->id << " = [" << this->id << "]->union(" << other_auto->id << ")";

  return union_auto;
}

StringAutomaton_ptr StringAutomaton::intersect(StringAutomaton_ptr other_auto) {
  DFA_ptr intersect_dfa = nullptr, minimized_dfa = nullptr;
  StringAutomaton_ptr intersect_auto = nullptr;

  intersect_dfa = dfaProduct(this->dfa, other_auto->dfa, dfaAND);
  minimized_dfa = dfaMinimize(intersect_dfa);
  dfaFree(intersect_dfa);
  intersect_dfa = nullptr;

  intersect_auto = new StringAutomaton(minimized_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << intersect_auto->id << " = [" << this->id << "]->intersect(" << other_auto->id << ")";

  return intersect_auto;
}

/**
 * TODO 1 - If we implement this method in low level we can avoid unnecessary
 * dfa product
 * 2 - Before refactoring this try to refactor complement so that item 1- will
 * not be a concern anymore.
 */
StringAutomaton_ptr StringAutomaton::difference(StringAutomaton_ptr other_auto) {
  StringAutomaton_ptr difference_auto = nullptr, complement_auto = nullptr;

  complement_auto = other_auto->complement();
  difference_auto = this->intersect(complement_auto);

  DVLOG(VLOG_LEVEL) << difference_auto->id << " = [" << this->id << "]->difference(" << other_auto->id << ")";

  return difference_auto;
}

StringAutomaton_ptr StringAutomaton::concatenate(StringAutomaton_ptr other_auto) {
  DFA_ptr concat_dfa = nullptr;
  StringAutomaton_ptr concat_auto = nullptr;

  concat_dfa = dfa_concat(this->dfa, other_auto->dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          StringAutomaton::DEFAULT_VARIABLE_INDICES);

  concat_auto = new StringAutomaton(concat_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << concat_auto->id << " = [" << this->id << "]->concatenate(" << other_auto->id << ")";

  return concat_auto;
}

StringAutomaton_ptr StringAutomaton::optional() {
  StringAutomaton_ptr optional_auto = nullptr, empty_string = nullptr;

  empty_string = StringAutomaton::makeEmptyString();
  optional_auto = this->union_(empty_string);
  delete empty_string;

  DVLOG(VLOG_LEVEL) << optional_auto->id << " = [" << this->id << "]->optional()";

  return optional_auto;
}

/**
 * TODO improve implementation by refactoring libstranger call
 *
 */
StringAutomaton_ptr StringAutomaton::closure() {
  DFA_ptr closure_dfa = nullptr;
  StringAutomaton_ptr closure_auto = nullptr;

  closure_dfa = dfa_closure_extrabit(dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          StringAutomaton::DEFAULT_VARIABLE_INDICES);
  closure_auto = new StringAutomaton(closure_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << closure_auto->id << " = [" << this->id << "]->closure()";

  return closure_auto;
}

StringAutomaton_ptr StringAutomaton::kleeneClosure() {
  StringAutomaton_ptr kleene_closure_auto = nullptr, closure_auto = nullptr, empty_string = nullptr;

  closure_auto = this->closure();
  empty_string = StringAutomaton::makeEmptyString();
  kleene_closure_auto = closure_auto->union_(empty_string);
  delete closure_auto;
  delete empty_string;

  DVLOG(VLOG_LEVEL) << kleene_closure_auto->id << " = [" << this->id << "]->kleeneClosure()";

  return kleene_closure_auto;
}

StringAutomaton_ptr StringAutomaton::repeat(unsigned min) {
  StringAutomaton_ptr repeated_auto = nullptr, union_auto = nullptr, concat_auto = nullptr, complement_auto = nullptr,
          closure_auto = nullptr;

  if (min == 0) {
    repeated_auto = this->kleeneClosure();
  } else if (min == 1) {
    repeated_auto = this->closure();
  } else {
    closure_auto = this->closure();
    union_auto = this->clone();
    concat_auto = this->clone();

    for (unsigned int i = 2; i < min; i++) {
      StringAutomaton_ptr temp_concat = concat_auto;
      concat_auto = temp_concat->concatenate(this);
      delete temp_concat;

      StringAutomaton_ptr temp_union = union_auto;
      union_auto = temp_union->union_(concat_auto);
      delete temp_union;
    }

    complement_auto = union_auto->complement();
    repeated_auto = closure_auto->intersect(complement_auto);

    delete complement_auto;
    delete concat_auto;
    delete union_auto;
    delete closure_auto;
  }

  DVLOG(VLOG_LEVEL) << repeated_auto->id << " = [" << this->id << "]->repeat(" << min << ")";

  return repeated_auto;
}

StringAutomaton_ptr StringAutomaton::repeat(unsigned min, unsigned max) {
  StringAutomaton_ptr repeated_auto = nullptr, concat_auto = nullptr;

  // handle min
  if (min == 0) { // {min, max} where min is 0
    repeated_auto = StringAutomaton::makeEmptyString();
    concat_auto = StringAutomaton::makeEmptyString();
  } else {                    // {min, max} where min > 0
    concat_auto = this->clone();     // {min, max} where min = 1
    for (unsigned i = 2; i <= min; i++) { // {min, max} where min > 1
      StringAutomaton_ptr temp_concat = concat_auto;
      concat_auto = temp_concat->concatenate(this);
      delete temp_concat;
    }
    repeated_auto = concat_auto->clone();
  }

  // handle min + 1, max
  for (unsigned i = min + 1; i <= max; i++) {
    StringAutomaton_ptr temp_concat = concat_auto;
    concat_auto = temp_concat->concatenate(this);
    delete temp_concat;

    StringAutomaton_ptr temp_union = repeated_auto;
    repeated_auto = temp_union->union_(concat_auto);
    delete temp_union;
  }

  delete concat_auto;

  DVLOG(VLOG_LEVEL) << repeated_auto->id << " = [" << this->id << "]->repeat(" << min << ", " << max << ")";

  return repeated_auto;
}

StringAutomaton_ptr StringAutomaton::contains(StringAutomaton_ptr other_auto) {
  StringAutomaton_ptr contains_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr, tmp_auto_2 = nullptr;

  any_string_auto = StringAutomaton::makeAnyString();
  tmp_auto_1 = any_string_auto->concatenate(other_auto);
  tmp_auto_2 = tmp_auto_1->concatenate(any_string_auto);

  contains_auto = this->intersect(tmp_auto_2);
  delete any_string_auto;
  delete tmp_auto_1; delete tmp_auto_2;

  DVLOG(VLOG_LEVEL) << contains_auto->id << " = [" << this->id << "]->contains(" << other_auto->id << ")";

  return contains_auto;
}

StringAutomaton_ptr StringAutomaton::begins(StringAutomaton_ptr other_auto) {
  StringAutomaton_ptr begins_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr;

  any_string_auto = StringAutomaton::makeAnyString();
  tmp_auto_1 = other_auto->concatenate(any_string_auto);

  begins_auto = this->intersect(tmp_auto_1);

  DVLOG(VLOG_LEVEL) << begins_auto->id << " = [" << this->id << "]->begins(" << other_auto->id << ")";

  return begins_auto;
}

StringAutomaton_ptr StringAutomaton::ends(StringAutomaton_ptr other_auto) {
  StringAutomaton_ptr ends_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr;

  any_string_auto = StringAutomaton::makeAnyString();
  tmp_auto_1 = any_string_auto->concatenate(other_auto);

  ends_auto = this->intersect(tmp_auto_1);

  DVLOG(VLOG_LEVEL) << ends_auto->id << " = [" << this->id << "]->ends(" << other_auto->id << ")";

  return ends_auto;
}

StringAutomaton_ptr StringAutomaton::toUpperCase() {
  DFA_ptr upper_case_dfa = nullptr;
  StringAutomaton_ptr upper_case_auto = nullptr;

  upper_case_dfa = dfaToUpperCase(dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  upper_case_auto = new StringAutomaton(upper_case_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << upper_case_auto->id << " = [" << this->id << "]->toUpperCase()";

  return upper_case_auto;
}

StringAutomaton_ptr StringAutomaton::toLowerCase() {
  DFA_ptr lower_case_dfa = nullptr;
  StringAutomaton_ptr lower_case_auto = nullptr;

  lower_case_dfa = dfaToLowerCase(dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  lower_case_auto = new StringAutomaton(lower_case_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << lower_case_auto->id << " = [" << this->id << "]->toLowerCase()";

  return lower_case_auto;
}

StringAutomaton_ptr StringAutomaton::trim() {
  DFA_ptr trimmed_dfa = nullptr;
  StringAutomaton_ptr trimmed_auto = nullptr;

  trimmed_dfa = dfaTrim(dfa, ' ', StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  trimmed_auto = new StringAutomaton(trimmed_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << trimmed_auto->id << " = [" << this->id << "]->trim()";

  return trimmed_auto;
}

StringAutomaton_ptr StringAutomaton::replace(StringAutomaton_ptr search_auto, StringAutomaton_ptr replace_auto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  result_dfa = dfa_general_replace_extrabit(dfa, search_auto->dfa, replace_auto->dfa,
          StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);

  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->repeat(" << search_auto->id << ", " << replace_auto->id << ")";

  return result_auto;
}

/**
 * TODO Needs complete refactoring, has a lot of room for improvements
 * especially in libstranger function calls
 */
bool StringAutomaton::checkEquivalence(StringAutomaton_ptr other_auto) {
  DFA *M[4];
  int result, i;

  M[0] = dfaProduct(this->dfa, other_auto->dfa, dfaIMPL);
  M[1] = dfaProduct(other_auto->dfa, this->dfa, dfaIMPL);
  M[2] = dfa_intersect(M[0], M[1]);
  M[3] = dfa_negate(M[2], StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  result = check_emptiness(M[3], StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);

  for (i = 0; i < 4; i++) {
    dfaFree(M[i]);
    M[i] = nullptr;
  }

  return result;
}

/**
 * TODO implement this again independent of libstranger
 */
bool StringAutomaton::isEmptyLanguage() {
  bool result;
  int i = check_emptiness(this->dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  result = (i == 1);
  DVLOG(VLOG_LEVEL) << "[" << this->id << "]->isEmptyLanguage? " << std::boolalpha << result;
  return result;
}

bool StringAutomaton::hasEmptyString() {
  return ((dfa->f[dfa->s]) == 1) ? true : false;
}

/**
 * TODO Figure out bdd details and find a better way to check that
 * without calling check_equivalence
 */
bool StringAutomaton::isEmptyString() {
  LOG(FATAL)<< "implement me";
  return false;
}

void StringAutomaton::toDotAscii(bool print_sink, std::ostream& out) {
  int sink_status = (print_sink) ? 1 : 0;
  sink_status = (dfa->ns == 1 and dfa->f[0] == -1) ? 2 : sink_status;
  dfaPrintGraphvizAsciiRange(dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES,
          sink_status);
}

int* StringAutomaton::allocateAscIIIndexWithExtraBit(int length) {
  int* indices = new int[length + 1];
  int i;
  for (i = 0; i <= length; i++) {
    indices[i] = i;
  }
  return indices;
}

std::vector<char> StringAutomaton::getReservedWord(char last_char, int length) {
  std::vector<char> reserved_word;

  int i;
  for (i = 0; i < length - 1; i++) {
    reserved_word.push_back('1');
  }
  reserved_word.push_back(last_char);
  reserved_word.push_back('\0');

  return reserved_word;
}

char* StringAutomaton::binaryFormat(unsigned long number, int bit_length) {
  char* binary_str = nullptr;
  int index = bit_length;
  unsigned long subject = number;

  // no extra bit
  binary_str = new char[bit_length + 1];
  binary_str[bit_length] = '\0';

  for (index--; index >= 0; index--) {
    if (subject & 1) {
      binary_str[index] = '1';
    } else {
      binary_str[index] = '0';
    }
    if (subject > 0) {
      subject >>= 1;
    }
  }

  return binary_str;
}

} /* namespace Theory */
} /* namespace Vlab */


