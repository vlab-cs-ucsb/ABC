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

int StringAutomaton::name_counter = 0;

int StringAutomaton::DEFAULT_NUM_OF_VARIABLES = 8;

int* StringAutomaton::DEFAULT_VARIABLE_INDICES = Automaton::getIndices(
        StringAutomaton::DEFAULT_NUM_OF_VARIABLES, 1);

unsigned* StringAutomaton::DEFAULT_UNSIGNED_VARIABLE_INDICES = Automaton::getIndices(
        (unsigned)StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

StringAutomaton::StringAutomaton(DFA_ptr dfa)
        : Automaton(Automaton::Type::STRING, dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES) {
}

StringAutomaton::StringAutomaton(DFA_ptr dfa, int num_of_variables)
        : Automaton(Automaton::Type::STRING, dfa, num_of_variables) {
}

StringAutomaton::StringAutomaton(const StringAutomaton& other)
        : Automaton(other) {
}

StringAutomaton::~StringAutomaton() {
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
  DFA_ptr non_accepting_string_dfa = nullptr;
  StringAutomaton_ptr non_accepting_string_auto = nullptr;
  non_accepting_string_dfa = Automaton::makePhi(num_of_variables, variable_indices);
  non_accepting_string_auto = new StringAutomaton(non_accepting_string_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << non_accepting_string_auto->id << " = makePhi()";

  return non_accepting_string_auto;
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
  std::vector<char> reserved_1 = Automaton::getReservedWord('1', num_of_variables);
  std::vector<char> reserved_2 = Automaton::getReservedWord('0', num_of_variables);
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
  std::vector<char> reserved_1 = Automaton::getReservedWord('1', num_of_variables);
  std::vector<char> reserved_2 = Automaton::getReservedWord('0', num_of_variables);
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
    regex_auto = regex_expr1_auto->concat(regex_expr2_auto);
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
    LOG(FATAL)<< "Unsupported regular expression" << *regular_expression;
    break;
    case Util::RegularExpression::Type::INTERVAL:
    {
      LOG(FATAL) << "Unsupported regular expression" << *regular_expression;
      break;
    }
    default:
    LOG(FATAL) << "Unsupported regular expression" << *regular_expression;
    break;
  }

  return regex_auto;
}

StringAutomaton_ptr StringAutomaton::makeLengthEqual(int length, int num_of_variables, int* variable_indices){
  StringAutomaton_ptr length_auto = nullptr;

  if(length < 0){
    length_auto = StringAutomaton::makeAnyString();
  }
  else if (length == 0){
    length_auto = StringAutomaton::makeEmptyString();
  }
  else{
    DFA_ptr length_dfa = dfaStringAutomatonL1toL2(length, length,
             StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
         length_auto = new StringAutomaton(length_dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  }

  DVLOG(VLOG_LEVEL) << length_auto->id << " = makeLength(" << length <<  ")";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::makeLengthLessThan(int length, int num_of_variables, int* variable_indices){
   StringAutomaton_ptr length_auto = nullptr;

   if(length < 0){
     length_auto = StringAutomaton::makeAnyString();
   }
   else if (length == 0){
     length_auto = StringAutomaton::makePhi();
   }
   else{
     DFA_ptr length_dfa = dfaStringAutomatonL1toL2(0, length-1,
         StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
     length_auto = new StringAutomaton(length_dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
   }

   DVLOG(VLOG_LEVEL) << length_auto->id << " = makeLengthLessThan(" << length <<  ")";

   return length_auto;
}

StringAutomaton_ptr StringAutomaton::makeLengthLessThanEqual(int length, int num_of_variables, int* variable_indices){
  StringAutomaton_ptr length_auto = nullptr;
  StringAutomaton_ptr anyChar_auto = nullptr;

  anyChar_auto = StringAutomaton::makeAnyChar();

  if(length < 0){
    length_auto = StringAutomaton::makeAnyString();
  }
  else if (length == 0){
    length_auto = StringAutomaton::makeEmptyString();
  }
  else{
//    length_auto = anyChar_auto->repeat(0,length);

    DFA_ptr length_dfa = dfaStringAutomatonL1toL2(0, length,
             StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
         length_auto = new StringAutomaton(length_dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  }

  delete anyChar_auto;
  anyChar_auto = nullptr;

  DVLOG(VLOG_LEVEL) << length_auto->id << " = makeLengthLessThanEqual(" << length <<  ")";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::makeLengthGreaterThan(int length, int num_of_variables, int* variable_indices){
  StringAutomaton_ptr length_auto = nullptr;

  if(length < 0){
    length_auto = StringAutomaton::makeAnyString();
  }
  else{
    length_auto = StringAutomaton::makeLengthLessThanEqual(length)->complement();
  }

  DVLOG(VLOG_LEVEL) << length_auto->id << " = makeLengthGreaterThan(" << length <<  ")";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::makeLengthGreaterThanEqual(int length, int num_of_variables, int* variable_indices){
  StringAutomaton_ptr length_auto = nullptr;

  if(length < 0){
    length_auto = StringAutomaton::makeAnyString();
  }
  else{
    length_auto = StringAutomaton::makeLengthLessThan(length)->complement();
  }

  DVLOG(VLOG_LEVEL) << length_auto->id << " = makeLengthGreaterThanEqual(" << length <<  ")";

  return length_auto;
}


StringAutomaton_ptr StringAutomaton::makeLengthRange(int start, int end, int num_of_variables, int* variable_indices){
  StringAutomaton_ptr range_auto = nullptr, lessThan_auto = nullptr, greaterThanEqual_auto = nullptr;

  greaterThanEqual_auto = StringAutomaton::makeLengthGreaterThanEqual(start);
  lessThan_auto = StringAutomaton::makeLengthLessThan(end);
  range_auto = lessThan_auto->intersect(greaterThanEqual_auto);

  delete greaterThanEqual_auto;
  delete lessThan_auto;

  DVLOG(VLOG_LEVEL) << range_auto->id << " = makeLengthRange(" << start << "," << end <<  ")";

  return range_auto;
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

/**
 * @Deprecated
 */
StringAutomaton_ptr StringAutomaton::concatenate(StringAutomaton_ptr other_auto) {
  DFA_ptr concat_dfa = nullptr;
  StringAutomaton_ptr concat_auto = nullptr;

  LOG(FATAL) << "please use 'concat' function";

  DFA_ptr M1 = this->dfa;
  DFA_ptr M2 = other_auto->dfa;
  int var = StringAutomaton::DEFAULT_NUM_OF_VARIABLES;
  int* indices = StringAutomaton::DEFAULT_VARIABLE_INDICES;

  StringAutomaton_ptr tmp0 = nullptr;
      DFA *tmp1 = nullptr;


      if(checkEmptyString(M2)) {
        if(state_reachable(M2, M2->s, var, indices)){
          tmp1 = dfa_shift_empty_M(M2, var, indices);
          StringAutomaton_ptr tmp = new StringAutomaton(tmp1, var);
          tmp0 = this->concat(tmp);
          dfaFree(tmp1);
        }
        else{
          tmp0 =  concat(other_auto);
        }
        tmp1 = dfa_union(tmp0->dfa, M1);
        delete tmp0;
      }else{
        tmp1 = concat(other_auto)->dfa;
      }
  concat_auto = new StringAutomaton(tmp1, num_of_variables);

  DVLOG(VLOG_LEVEL) << concat_auto->id << " = [" << this->id << "]->concatenate(" << other_auto->id << ")";

  return concat_auto;
}

/**
 * Re-implementation of  'dfa_concat_extrabit' in LibStranger
 * Added single string check
 *
 */
StringAutomaton_ptr StringAutomaton::concat(StringAutomaton_ptr other_auto) {
  DFA_ptr concat_dfa = nullptr, tmp_dfa = nullptr;
  StringAutomaton_ptr concat_auto = nullptr, to_union_auto = nullptr;

  if (this->isEmptyLanguage() or other_auto->isEmptyLanguage()) {
    return StringAutomaton::makePhi();
  } else if (this->isEmptyString()) {
    return other_auto->clone();
  } else if (other_auto->isEmptyString()) {
    return this->clone();
  }

  bool has_empty_string = other_auto->hasEmptyString();
  bool delete_other_auto = false;


  if (has_empty_string and other_auto->hasIncomingTransition(other_auto->dfa->s)) {
    DFA_ptr shifted_dfa = dfa_shift_empty_M(other_auto->dfa, other_auto->num_of_variables, other_auto->variable_indices);
    StringAutomaton_ptr shifted_auto = new StringAutomaton(shifted_dfa, other_auto->num_of_variables);
    other_auto = shifted_auto;
    delete_other_auto = true;
  }



  int var = num_of_variables;
  int* indices = variable_indices;
  int tmp_num_of_variables,
      state_id_shift_amount,
      expected_num_of_states,
      num_of_exceptions_to_add = 0,
      sink_state_left_auto,
      sink_state_right_auto,
      state_key_left_auto = 0,
      state_key_right_auto = 0,
      state_key_fix = 0,
      loc,
      i = 0,
      j = 0;

  bool is_start_state_reachable;
  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;

  std::map<int, std::vector<char>*> exceptions_left_auto;
  std::map<int, std::vector<char>*> exceptions_right_auto;
  std::map<int, std::vector<char>*> exceptions_fix;
  std::map<int, int> state_map_right_auto;
  std::map<int, int> state_map_left_auto;
  std::map<int, int> state_map_fix;
  char* statuses = nullptr;

  // variable initializations
  sink_state_left_auto = this->getSinkState();
  sink_state_right_auto = other_auto->getSinkState();

  CHECK_GT(sink_state_left_auto, -1);
  CHECK_GT(sink_state_right_auto, -1);

  tmp_num_of_variables = this->num_of_variables + 1; // add one extra bit
  state_id_shift_amount = this->dfa->ns;

  expected_num_of_states = this->dfa->ns + other_auto->dfa->ns - 1; // -1 is for to remove one of the sink states
  is_start_state_reachable = other_auto->isStartStateReachableFromAnAcceptingState();
  if (not is_start_state_reachable) {
    expected_num_of_states = expected_num_of_states  - 1; // if start state is reachable from an accepting state, it will be merge with accepting states of left hand side
  }

  statuses = new char[expected_num_of_states];

//  std::cout << "sink 1: " << sink_state_left_auto << std::endl;
//  std::cout << "sink 2: " << sink_state_right_auto << std::endl;
//  std::cout << "left ns: " << this->dfa->ns << std::endl;
//  std::cout << "right ns: " << other_auto->dfa->ns << std::endl;
//  std::cout << "right initflag: " << is_start_state_reachable << std::endl;
//  std::cout << "new ns: " << expected_num_of_states << std::endl;
//
//  std::cout << "shift: " << state_id_shift_amount << std::endl;
//  std::cout << "right start state: " << other_auto->dfa->s << std::endl;

  dfaSetup(expected_num_of_states, tmp_num_of_variables, getIndices(tmp_num_of_variables)); //sink states are merged
  state_paths = pp = make_paths(other_auto->dfa->bddm, other_auto->dfa->q[other_auto->dfa->s]);
  while (pp) {
    if ( pp->to != (unsigned)sink_state_right_auto ) {
      state_map_right_auto[state_key_right_auto] = pp->to + state_id_shift_amount;
      // if there is a self loop keep it
      if ( pp->to == (unsigned)other_auto->dfa->s ) {
        state_map_right_auto[state_key_right_auto] -= 2;
      } else {
        if ( sink_state_right_auto >= 0 && pp->to > (unsigned)sink_state_right_auto ) {
          state_map_right_auto[state_key_right_auto]--; //to new state, sink state will be eliminated and hence need -1
        }
        if ((not is_start_state_reachable) && pp->to > (unsigned)other_auto->dfa->s) {
          state_map_right_auto[state_key_right_auto]--; // to new state, init state will be eliminated if init is not reachable
        }
      }

      exceptions_right_auto[state_key_right_auto] = new std::vector<char>();
      for (j = 0; j < other_auto->num_of_variables; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            exceptions_right_auto[state_key_right_auto]->push_back('1');
          }
          else {
            exceptions_right_auto[state_key_right_auto]->push_back('0');
          }
        }
        else {
          exceptions_right_auto[state_key_right_auto]->push_back('X');
        }
      }

      exceptions_right_auto[state_key_right_auto]->push_back('1'); // new path
      exceptions_right_auto[state_key_right_auto]->push_back('\0');
      state_key_right_auto++;
    }

    tp = nullptr;
    pp = pp->next;
  }

  kill_paths(state_paths);
  state_paths = pp = nullptr;

  num_of_exceptions_to_add = state_key_right_auto; //num_of_exceptions_to_add is the number of new paths
  for (i = 0; i < this->dfa->ns; i++) {
    state_paths = pp = make_paths(this->dfa->bddm, this->dfa->q[i]);
    state_key_left_auto = 0;
    while (pp) {
      if (pp->to == (unsigned)sink_state_left_auto) {
        pp = pp->next;
        continue;
      }

      state_map_left_auto[state_key_left_auto] = pp->to;
      exceptions_left_auto[state_key_left_auto] = new std::vector<char>();
      for (j = 0; j < this->num_of_variables; j++) {
        for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) {
            exceptions_left_auto[state_key_left_auto]->push_back('1');
          } else {
            exceptions_left_auto[state_key_left_auto]->push_back('0');
          }
        } else {
          exceptions_left_auto[state_key_left_auto]->push_back('X');
        }
      }

      exceptions_left_auto[state_key_left_auto]->push_back('0'); // add extra bit, '0' is used for the exceptions coming from left auto
      exceptions_left_auto[state_key_left_auto]->push_back('\0');

      state_key_left_auto++;
      tp = nullptr;
      pp = pp->next;
    }

    // generate concat automaton
    int num_of_exceptions_left_auto = state_key_left_auto;
    if (this->isAcceptingState(i)) {
      dfaAllocExceptions(num_of_exceptions_left_auto + num_of_exceptions_to_add);
      for (int state_key = 0; state_key < num_of_exceptions_left_auto; state_key++) {
        dfaStoreException(state_map_left_auto[state_key], &*(exceptions_left_auto[state_key]->begin()));
      }
      for (int state_key = 0; state_key < num_of_exceptions_to_add; state_key++) {
        dfaStoreException(state_map_right_auto[state_key], &*(exceptions_right_auto[state_key]->begin()));
      }

      dfaStoreState(sink_state_left_auto);
      if (other_auto->isAcceptingState(0)) {
        statuses[i]='+';
      }
      else {
        statuses[i]='-';
      }
    } else {
      dfaAllocExceptions(num_of_exceptions_left_auto);
      for (int state_key = 0; state_key < num_of_exceptions_left_auto; state_key++) {
        dfaStoreException(state_map_left_auto[state_key], &*exceptions_left_auto[state_key]->begin());
      }
      dfaStoreState(sink_state_left_auto);
      statuses[i] = '-';
    }
    kill_paths(state_paths);
    state_paths = pp = nullptr;
  }

  // clear maps
  for (auto& entry : exceptions_left_auto) {
    entry.second->clear();
    delete entry.second;
  }
  for (auto& entry : exceptions_right_auto) {
    entry.second->clear();
    delete entry.second;
  }
  state_map_left_auto.clear();
  state_map_right_auto.clear();

  //  initflag is 1 iff init is reached by some state. In this case,
  for (i = 0; i < other_auto->dfa->ns; i++) {
    if ( i != sink_state_right_auto ) {
      if ( i != other_auto->dfa->s || is_start_state_reachable) {
        state_paths = pp = make_paths(other_auto->dfa->bddm, other_auto->dfa->q[i]);
        state_key_fix = 0;
        while (pp) {
          if ( pp->to != (unsigned)sink_state_right_auto) {
            state_map_fix[state_key_fix] = pp->to + state_id_shift_amount;

            if ( sink_state_right_auto >= 0 && pp->to > (unsigned)sink_state_right_auto) {
              state_map_fix[state_key_fix]--; //to new state, sink state will be eliminated and hence need -1
            }

            if ( (not is_start_state_reachable) && pp->to > (unsigned)other_auto->dfa->s) {
              state_map_fix[state_key_fix]--; // to new state, init state will be eliminated if init is not reachable
            }

            exceptions_fix[state_key_fix] = new std::vector<char>();
            for (j = 0; j < var; j++) {
              for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp =tp->next);
              if (tp) {
                if (tp->value){
                  exceptions_fix[state_key_fix]->push_back('1');
                }
                else {
                  exceptions_fix[state_key_fix]->push_back('0');
                }
              }
              else {
                exceptions_fix[state_key_fix]->push_back('X');
              }
            }
            exceptions_fix[state_key_fix]->push_back('0'); // old value
            exceptions_fix[state_key_fix]->push_back('\0');
            state_key_fix++;
            tp = nullptr;
          }
          pp = pp->next;
        }

        dfaAllocExceptions(state_key_fix);
        for (int state_key = 0; state_key < state_key_fix; state_key++) {
          dfaStoreException(state_map_fix[state_key], &*(exceptions_fix[state_key]->begin()));
        }

        dfaStoreState(sink_state_left_auto);

        loc = state_id_shift_amount + i;
        if ( (not is_start_state_reachable) && i > other_auto->dfa->s) {
          loc--;
        }
        if ( sink_state_right_auto >= 0 && i > sink_state_right_auto) {
          loc--;
        }

        if ( other_auto->isAcceptingState(i)) {
          statuses[loc]='+';
        } else {
          statuses[loc]='-';
        }

        kill_paths(state_paths);
        state_paths = pp = nullptr;
      }
    }
  }

//  statuses[expected_num_of_states]='\0';
  for (auto& entry : exceptions_fix) {
    entry.second->clear();
    delete entry.second;
  }
  state_map_fix.clear();

  concat_dfa = dfaBuild(statuses);
  tmp_dfa = dfaProject(concat_dfa, (unsigned) var);
  delete concat_dfa;
  concat_dfa = dfaMinimize(tmp_dfa);
  delete tmp_dfa;

  concat_auto = new StringAutomaton(concat_dfa, num_of_variables);

  if (has_empty_string) {
    StringAutomaton_ptr tmp_auto = concat_auto;
    concat_auto = tmp_auto->union_(this);
    delete tmp_auto;
    if (delete_other_auto) {
      delete other_auto;
    }
  }

  DVLOG(VLOG_LEVEL) << concat_auto->id << " = [" << this->id << "]->concat(" << other_auto->id << ")";

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
      concat_auto = temp_concat->concat(this);
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
      concat_auto = temp_concat->concat(this);
      delete temp_concat;
    }
    repeated_auto = concat_auto->clone();
  }

  // handle min + 1, max
  for (unsigned i = min + 1; i <= max; i++) {
    StringAutomaton_ptr temp_concat = concat_auto;
    concat_auto = temp_concat->concat(this);
    delete temp_concat;

    StringAutomaton_ptr temp_union = repeated_auto;
    repeated_auto = temp_union->union_(concat_auto);
    delete temp_union;
  }

  delete concat_auto;

  DVLOG(VLOG_LEVEL) << repeated_auto->id << " = [" << this->id << "]->repeat(" << min << ", " << max << ")";

  return repeated_auto;
}


StringAutomaton_ptr StringAutomaton::suffixes(){
  DFA_ptr suffix_dfa = nullptr;
  StringAutomaton_ptr suffix_auto = nullptr;

  suffix_dfa = dfaCopy(dfa);

  suffix_auto = new StringAutomaton(dfaMinimize(dfa_Suffix(suffix_dfa,0,0,StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
          StringAutomaton::DEFAULT_VARIABLE_INDICES)), num_of_variables);
  return suffix_auto;
}

StringAutomaton_ptr StringAutomaton::prefixes(){
  DFA_ptr prefix_dfa = nullptr;
  StringAutomaton_ptr prefix_auto = nullptr;
  int sink;

  prefix_dfa = dfaCopy(dfa);
  sink = find_sink(prefix_dfa);

  for (int i = 0; i < prefix_dfa->ns; i++) {
    if(i != sink){
      prefix_dfa->f[i] = 1;
    }
  }

  prefix_auto = new StringAutomaton(dfaMinimize(prefix_dfa), num_of_variables);

  DVLOG(VLOG_LEVEL) << prefix_auto->id << " = [" << this->id << "]->prefixes()";
  return prefix_auto;
}

StringAutomaton_ptr StringAutomaton::suffixesFromIndex(int start){
  DFA_ptr suffix_dfa = nullptr;
  DFA_ptr current_dfa = nullptr;
  StringAutomaton_ptr suffix_auto = nullptr;

  if(start <= 0){
    suffix_dfa = dfaCopy(dfa);
  }
  else{
    suffix_dfa = dfaMinimize(dfa_Suffix(dfaCopy(dfa),start,start,StringAutomaton::DEFAULT_NUM_OF_VARIABLES,
            StringAutomaton::DEFAULT_VARIABLE_INDICES));
  }

  suffix_auto = new StringAutomaton(suffix_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << suffix_auto->id << " = [" << this->id << "]->suffixesFromIndex()";

  return suffix_auto;
}

StringAutomaton_ptr StringAutomaton::prefixesUntilIndex(int index){
  StringAutomaton_ptr prefixes_auto = nullptr;
  StringAutomaton_ptr length_auto = nullptr;
  StringAutomaton_ptr prefixesUntil_auto = nullptr;

  prefixes_auto = this->prefixes();
  length_auto = makeLengthLessThan(index);

  prefixesUntil_auto = prefixes_auto->intersect(length_auto);
  DVLOG(VLOG_LEVEL) << prefixesUntil_auto->id << " = [" << this->id << "]->prefixesUntilIndex("<<index<<")";
  return prefixesUntil_auto;
}

StringAutomaton_ptr StringAutomaton::prefixesAtIndex(int index){
  StringAutomaton_ptr prefixes_auto = nullptr;
  StringAutomaton_ptr length_auto = nullptr;
  StringAutomaton_ptr prefixesAt_auto = nullptr;

  prefixes_auto = this->prefixes();
  prefixesAt_auto = prefixes_auto->intersect(makeLengthEqual(index+1));
  DVLOG(VLOG_LEVEL) << prefixesAt_auto->id << " = [" << this->id << "]->prefixesAtIndex("<<index<<")";
  return prefixesAt_auto;
}

StringAutomaton_ptr StringAutomaton::charAt(int index){
  return this->substring(index,index);
}

StringAutomaton_ptr StringAutomaton::substring(int start){
  StringAutomaton_ptr substring_auto = nullptr;
  substring_auto = this->suffixesFromIndex(start);
  DVLOG(VLOG_LEVEL) << substring_auto->id << " = [" << this->id << "]->substring(" << start << ")";
  return substring_auto;
}

StringAutomaton_ptr StringAutomaton::substring(int start, int end){
  StringAutomaton_ptr substring_auto = nullptr, suffixes_auto = nullptr;
  suffixes_auto = this->suffixesFromIndex(start);
  substring_auto = suffixes_auto->prefixesAtIndex(end - start);
  delete suffixes_auto;
  DVLOG(VLOG_LEVEL) << substring_auto->id << " = [" << this->id << "]->substring(" << start << "," << end << ")";
  return substring_auto;
}

/**
 * TODO
 * 1) first check the existance with contains,
 * then continue with the result of contains.
 * 2) if there are strings those contain search auto and
 * there are strings those do not contain search result should include
 * -1 as well.
 */
IntAutomaton_ptr StringAutomaton::indexOf(StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr contains_auto = nullptr, difference_auto = nullptr, ends_auto = nullptr,
      indexOf_auto = nullptr, search_result_auto = nullptr;
  IntAutomaton_ptr length_auto = nullptr;

  DFA_ptr indexOf_dfa = nullptr, minimized_dfa = nullptr;
  bool has_negative_1 = false;

  contains_auto = this->contains(search_auto);
  if (contains_auto->isEmptyLanguage()) {
    delete contains_auto;
    length_auto = IntAutomaton::makeInt(-1);
    DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id << "]->indexOf(" << search_auto->id  << ")";
    return length_auto;
  }

  difference_auto = this->difference(contains_auto);
  if (not difference_auto->isEmptyLanguage()) {
    has_negative_1 = true;
  }
  delete difference_auto;

  std::map<int, NodeOld*> nodes;
  std::map<int, int> state_id_map;
  std::map<int, int> reverse_state_id_map;
  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;
  std::set<int> final_states;
  std::stack<int> state_work_list;
  std::set<int> processed;

  int* tmp_indices_with_extra_bit = getIndices(num_of_variables, 1);
  StringAutomaton_ptr contains_duplicate_auto = new StringAutomaton(dfa_replace_step1_duplicate(contains_auto->dfa, num_of_variables, tmp_indices_with_extra_bit), num_of_variables);
  StringAutomaton_ptr search_complement_auto = new StringAutomaton(dfa_replace_step2_match_compliment(search_auto->dfa, num_of_variables, tmp_indices_with_extra_bit), num_of_variables);
  StringAutomaton_ptr tmp_auto = contains_duplicate_auto->intersect(search_complement_auto);
  delete[] tmp_indices_with_extra_bit;
  delete contains_auto; contains_auto = nullptr;
  delete contains_duplicate_auto; contains_duplicate_auto = nullptr;
  delete search_complement_auto; search_complement_auto = nullptr;
  StringAutomaton_ptr sharp_auto = StringAutomaton::dfaSharpStringWithExtraBit();
  search_result_auto = sharp_auto->intersect(tmp_auto);
  delete tmp_auto; tmp_auto = nullptr;
  delete sharp_auto; sharp_auto = nullptr;

  search_result_auto->project((unsigned) num_of_variables);
  search_result_auto->minimize();

  // extract automaton
  std::vector<char> marked_transition = Automaton::getReservedWord('1', num_of_variables);
  int sink_state = search_result_auto->getSinkState();
  int current_state;
  int state_id = 0;
  int* indices = variable_indices;
  std::vector<char>* current_exception = nullptr;
  NodeOld* current_node = nullptr;

  state_work_list.push(search_result_auto->dfa->s);
  while (not state_work_list.empty()) {
    current_state = state_work_list.top(); state_work_list.pop();
    if (processed.find(current_state) != processed.end()) {
      continue;
    }
    processed.insert(current_state);
    current_node = new NodeOld(current_state);
    state_paths = pp = make_paths(search_result_auto->dfa->bddm, search_result_auto->dfa->q[current_state]);

    while (pp) {
      if ( pp->to != (unsigned)sink_state) {
        current_exception = new std::vector<char>();
        for (int j = 0; j < search_result_auto->num_of_variables; j++) {
          for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
          if (tp) {
            if (tp->value) {
              current_exception->push_back('1');
            }
            else {
              current_exception->push_back('0');
            }
          }
          else {
            current_exception->push_back('X');
          }
        }
        current_exception->push_back('\0');
        if (marked_transition == *current_exception) {
          final_states.insert(current_state);
          delete current_exception;
        } else {
          current_node->addExceptionToState(current_exception, pp->to);
          if (processed.find(pp->to) == processed.end()) {
            state_work_list.push(pp->to);
          }
        }
      }

      tp = nullptr;
      pp = pp->next;
    }

    nodes[current_state] = current_node;
    if (state_id == sink_state) {
      state_id_map[state_id] = sink_state;
      reverse_state_id_map[sink_state] = state_id;
      nodes[sink_state] = new NodeOld(sink_state);
      state_id++;
    }

    state_id_map[state_id] = current_state;
    reverse_state_id_map[current_state] = state_id;
    state_id++;

    current_node = nullptr;
    kill_paths(state_paths);
    state_paths = pp = nullptr;
  }

  // make sure sink state is there
  if (reverse_state_id_map.find(sink_state) == reverse_state_id_map.end()) {
    state_id_map[state_id] = sink_state;
    reverse_state_id_map[sink_state] = state_id;
    nodes[sink_state] = new NodeOld(sink_state);
  }

  // create automaton
  int expected_num_of_states = nodes.size();
  std::vector<char> statuses (expected_num_of_states);
  int old_state_id;
  statuses[sink_state] = '-';
  dfaSetup(expected_num_of_states, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  for (int i = 0; i < expected_num_of_states; i++) {
    old_state_id = state_id_map[i];
    current_node = nodes[old_state_id];
    dfaAllocExceptions(current_node->getNumberOfExceptions());
    for (auto& entry: current_node->getExceptions()) {
      dfaStoreException(reverse_state_id_map[entry.second], &*(entry.first->begin()));
    }
    dfaStoreState(sink_state);
    if (final_states.find(old_state_id) != final_states.end()) {
      statuses[i] = '+';
    } else {
      statuses[i] = '-';
    }
  }
  statuses.push_back('\0');
  indexOf_auto = new StringAutomaton(dfaBuild(&*(statuses.begin())), StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  // minimize?
  length_auto = indexOf_auto->length();
  length_auto->setMinus1(has_negative_1);
  delete indexOf_auto;

  DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id << "]->indexOf(" << search_auto->id  << ")";

  return length_auto;
}

/**
 * TODO include -1 in the result if it does not contain search
 * TODO fix the bug when search auto is not a singleton, see test case 09
 */
IntAutomaton_ptr StringAutomaton::lastIndexOf(StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr contains_auto = nullptr, difference_auto = nullptr, ends_auto = nullptr,
      lastIndexOf_auto = nullptr, search_result_auto = nullptr;
  IntAutomaton_ptr length_auto = nullptr;
  DFA_ptr lastIndexOf_dfa = nullptr, minimized_dfa = nullptr;
  bool has_negative_1 = false;

  contains_auto = this->contains(search_auto);
  if (contains_auto->isEmptyLanguage()) {
    delete contains_auto;
    length_auto = IntAutomaton::makeInt(-1);
    DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id << "]->lastIndexOf(" << search_auto->id  << ")";
    return length_auto;
  }

  difference_auto = this->difference(contains_auto);
  if (not difference_auto->isEmptyLanguage()) {
    has_negative_1 = true;
  }
  delete difference_auto;

  int* tmp_indices_with_extra_bit = getIndices(num_of_variables, 1);
  StringAutomaton_ptr contains_duplicate_auto = new StringAutomaton(dfa_replace_step1_duplicate(contains_auto->dfa, num_of_variables, tmp_indices_with_extra_bit), num_of_variables);
  StringAutomaton_ptr search_complement_auto = new StringAutomaton(dfa_replace_step2_match_compliment(search_auto->dfa, num_of_variables, tmp_indices_with_extra_bit), num_of_variables);
  StringAutomaton_ptr tmp_auto = contains_duplicate_auto->intersect(search_complement_auto);
  delete[] tmp_indices_with_extra_bit;

  delete contains_auto; contains_auto = nullptr;
  delete contains_duplicate_auto; contains_duplicate_auto = nullptr;
  delete search_complement_auto; search_complement_auto = nullptr;
  StringAutomaton_ptr sharp_auto = StringAutomaton::dfaSharpStringWithExtraBit();
  search_result_auto = sharp_auto->intersect(tmp_auto);
  delete tmp_auto; tmp_auto = nullptr;
  delete sharp_auto; sharp_auto = nullptr;

  search_result_auto->project((unsigned) StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  search_result_auto->minimize();

  Graph_ptr graph = search_result_auto->toGraph();
  // Mark start states and end states of matches
  std::vector<char> flag_1_exception = {'1', '1', '1', '1', '1', '1', '1', '1'}; // 255
  std::vector<char> flag_2_exception = {'1', '1', '1', '1', '1', '1', '1', '0'}; // 254
  GraphNode_ptr node = nullptr;
  int sink_state = search_result_auto->getSinkState();
  int next_state = -1;
  for (int s = 0; s < search_result_auto->dfa->ns; s++) {
    node = graph->getNode(s);
    if (sink_state != (next_state = search_result_auto->getNextStateFrom(s, flag_1_exception))) {
      node->addEdgeFlag(1, graph->getNode(next_state)); // flag 1 is to mark for beginning of a match
    } else if ( sink_state != (next_state = search_result_auto->getNextStateFrom(s, flag_2_exception)) ) {
      node->addEdgeFlag(2, graph->getNode(next_state)); // flag 2 is to mark for end of a match
    }
  }

  // BEGIN find new final states using reverse DFS traversal
  for (auto final_node : graph->getFinalNodes()) {
    std::stack<GraphNode_ptr> node_stack;
    std::map<GraphNode_ptr, bool> is_visited; // by default bool is initialized as false
    GraphNode_ptr curr_node = nullptr;
    node_stack.push(final_node);
    while (not node_stack.empty()) {
      curr_node = node_stack.top(); node_stack.pop();
      is_visited[curr_node] = true;
      for (auto& prev_node : curr_node->getPrevNodes()) {
        if (prev_node->hasEdgeFlag(1, curr_node)) { // a match state found
          prev_node->removeEdgeFlag(1, curr_node);
          prev_node->addEdgeFlag(3, curr_node); // 3 is for new final state
        } else {
          if (is_visited.find(prev_node) == is_visited.end()) {
            node_stack.push(prev_node);
          }
        }
      }
    }
  }
  // END find new final states using reverse DFS traversal

  graph->resetFinalNodesToFlag(3);
  std::stack<GraphNode_ptr> node_stack;
  std::map<GraphNode_ptr, bool> is_visited; // by default bool is initialized as false
  GraphNode_ptr sink_node = graph->getSinkNode();

  // BEGIN figure out new number of states and new state mapping
  // node ids in the graph corresponds the states ids in the search result automaton
  int next_state_id = 0;
  std::map<int, std::set<int>> state_id_map;
  std::map<int, int> reverse_state_id_map;
  GraphNode_ptr start_node = graph->getStartNode();
  CHECK_EQ(sink_state, sink_node->getID()); // we should preserve that up until here

  state_id_map[sink_state].insert(sink_node->getID()); // do not change sink state
  reverse_state_id_map[sink_node->getID()] = sink_state;

  node_stack.push(start_node);
  while (not node_stack.empty()) {
    GraphNode_ptr curr_node = node_stack.top(); node_stack.pop();
    if (is_visited.find(curr_node) != is_visited.end()) {
      continue;
    }

    if (next_state_id == sink_state) {
      ++next_state_id;
    }

    if (curr_node->hasEdgeFlags()) { // node has a marked edge
      std::stack<GraphNode_ptr> merge_stack;
      auto check_callback = [&merge_stack](GraphNode_ptr node) mutable -> bool {
        merge_stack.push(node);
        if (node->hasEdgeFlags()) {
          return false;
        }
        return true;
      };
      auto cont_callback = [](GraphNode_ptr node, std::stack<GraphNode_ptr>& st, std::map<GraphNode_ptr, bool>& v) mutable {
          std::map<int, GraphNodeSet> flags = node->getEdgeFlagMap();
          CHECK_EQ(1, flags.size()); // that check is specific to lastIndexOf algorithm
          for (auto it: flags) {
            for (auto& next_node : it.second) {
              if (v.find(next_node) == v.end()) {
                st.push(next_node);
              }
            }
          }
      };
      graph->dfs(curr_node, check_callback, cont_callback);
      GraphNode_ptr merge_node = nullptr;
      int map_id = -1;
      while (not merge_stack.empty()) {
        merge_node = merge_stack.top();
        if (map_id == -1 and reverse_state_id_map.find(merge_node->getID()) == reverse_state_id_map.end()) {
          state_id_map[next_state_id].insert(merge_node->getID());
          reverse_state_id_map[merge_node->getID()] = next_state_id;
          map_id = next_state_id;
          ++next_state_id;
        } else if (map_id == -1) {
          map_id = reverse_state_id_map[merge_node->getID()];
        } else {
          state_id_map[map_id].insert(merge_node->getID());
          reverse_state_id_map[merge_node->getID()] = map_id;
        }
        merge_stack.pop();
      }
    } else {
      if (reverse_state_id_map.find(curr_node->getID()) == reverse_state_id_map.end()) {
        state_id_map[next_state_id].insert(curr_node->getID());
        reverse_state_id_map[curr_node->getID()] = next_state_id;
        ++next_state_id;
      }
    }

    for (auto next_node : curr_node->getNextNodes()) {
      if (sink_node != next_node) { // do not visit sink we already assigned it
        node_stack.push(next_node);
      }
    }
    is_visited[curr_node] = true;
  }
  // END figure out new number of states and new state mapping

  // BEGIN generate automaton
  int expected_num_of_states = state_id_map.size();
  std::vector<char> statuses (expected_num_of_states);
  int* indices = StringAutomaton::DEFAULT_VARIABLE_INDICES;
  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;
  for (auto& ch : statuses) {
    ch = '-';
  }
  LOG(FATAL) << "fix bug here that appears on last index of test case 03";
  dfaSetup(expected_num_of_states, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, indices);
  for (int s = 0; s < expected_num_of_states; s++) {
    std::map<std::vector<char>*, int> exceptions;
    for (auto old_state : state_id_map[s]) {
      state_paths = pp = make_paths(search_result_auto->dfa->bddm, search_result_auto->dfa->q[old_state]);
      GraphNode_ptr node = graph->getNode(old_state);
      if (graph->isFinalNode(node)) {
        statuses[s] = '+';
      }
      while (pp) {
        if ( pp->to != (unsigned)sink_state and (node->getEdgeFlag(graph->getNode(pp->to)) == 0)) {
          int to_state = reverse_state_id_map[pp->to];
          std::vector<char> *current_exception = new std::vector<char>();
          for (int j = 0; j < search_result_auto->num_of_variables; j++) {
            for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
            if (tp) {
              if (tp->value) {
                current_exception->push_back('1');
              }
              else {
                current_exception->push_back('0');
              }
            }
            else {
              current_exception->push_back('X');
            }
          }
          current_exception->push_back('\0');
          exceptions.insert(std::make_pair(current_exception, to_state));
        }
        tp = nullptr;
        pp = pp->next;
      }
    }

    dfaAllocExceptions(exceptions.size());
    for (auto it = exceptions.begin(); it != exceptions.end();) {
      dfaStoreException(it->second, &*(it->first->begin()));
      delete it->first;
      it = exceptions.erase(it);
    }

    dfaStoreState(sink_state);
  }
  statuses.push_back('\0');

  lastIndexOf_auto = new StringAutomaton(dfaBuild(&*(statuses.begin())), StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
  std::cout << "last index of" << std::endl;
  lastIndexOf_auto->inspectAuto();
  // END generate automaton
  lastIndexOf_auto->minimize(); // trims the automaton

  length_auto = lastIndexOf_auto->length();
  length_auto->setMinus1(has_negative_1);
  delete lastIndexOf_auto;

  DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id << "]->lastIndexOf(" << search_auto->id << ")";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::contains(StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr contains_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr, tmp_auto_2 = nullptr;

  any_string_auto = StringAutomaton::makeAnyString();
  tmp_auto_1 = any_string_auto->concat(search_auto);
  tmp_auto_2 = tmp_auto_1->concat(any_string_auto);

  contains_auto = this->intersect(tmp_auto_2);
  delete any_string_auto;
  delete tmp_auto_1; delete tmp_auto_2;

  DVLOG(VLOG_LEVEL) << contains_auto->id << " = [" << this->id << "]->contains(" << search_auto->id << ")";

  return contains_auto;
}

StringAutomaton_ptr StringAutomaton::begins(StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr begins_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr;

  any_string_auto = StringAutomaton::makeAnyString();
  tmp_auto_1 = search_auto->concat(any_string_auto);

  begins_auto = this->intersect(tmp_auto_1);

  DVLOG(VLOG_LEVEL) << begins_auto->id << " = [" << this->id << "]->begins(" << search_auto->id << ")";

  return begins_auto;
}

StringAutomaton_ptr StringAutomaton::ends(StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr ends_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr;

  any_string_auto = StringAutomaton::makeAnyString();
  tmp_auto_1 = any_string_auto->concat(search_auto);

  ends_auto = this->intersect(tmp_auto_1);

  DVLOG(VLOG_LEVEL) << ends_auto->id << " = [" << this->id << "]->ends(" << search_auto->id << ")";

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
 * TODO get rid of libstranger calls
 */
IntAutomaton_ptr StringAutomaton::length() {
  DFA_ptr unary_dfa = nullptr, length_dfa = nullptr;
  IntAutomaton_ptr length_auto = nullptr;
  StringAutomaton_ptr any_string_auto = nullptr;

  if (this->isAcceptingSingleString()) {
    std::string example = this->getAnAcceptingString();
    length_auto = IntAutomaton::makeInt(example.length(), num_of_variables);
  } else {
    unary_dfa = dfa_string_to_unaryDFA(this->dfa, num_of_variables, variable_indices);
    any_string_auto = StringAutomaton::makeAnyString();
    length_dfa = dfa_restrict_by_unaryDFA(any_string_auto->dfa, unary_dfa, num_of_variables, variable_indices);
    delete any_string_auto;
    dfaFree(unary_dfa);

    length_auto = new IntAutomaton(length_dfa, num_of_variables);
  }

  DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id << "]->length()";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::restrictLengthTo(int length) {
  StringAutomaton_ptr restricted_auto = nullptr;
  StringAutomaton_ptr length_string_auto = StringAutomaton::makeLengthEqual(length);

  restricted_auto = this->intersect(length_string_auto);
  delete length_string_auto; length_string_auto = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id << " = [" << this->id << "]->restrictLengthTo(" << length << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictLengthTo(IntAutomaton_ptr length_auto) {
  StringAutomaton_ptr restricted_auto = nullptr;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(length_auto->getDFA());

  restricted_auto = this->intersect(length_string_auto);
  length_string_auto->dfa = nullptr;
  delete length_string_auto; length_string_auto = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id << " = [" << this->id << "]->restrictLengthTo(" << length_auto->getId() << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictIndexOfTo(int index, StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->restrictIndexOfTo(index_auto, search_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr restricted_auto = nullptr, contains_auto = nullptr,
          not_contains_auto = nullptr, tmp_auto_1 = nullptr, tmp_auto_2;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA());
  StringAutomaton_ptr any_string = StringAutomaton::makeAnyString();

  not_contains_auto = length_string_auto->difference(contains_auto);
  delete contains_auto; contains_auto = nullptr;
  length_string_auto->dfa = nullptr;
  delete length_string_auto; length_string_auto = nullptr;

  tmp_auto_1 = not_contains_auto->concat(search_auto);
  tmp_auto_2 = tmp_auto_1->concat(any_string);
  delete tmp_auto_1; tmp_auto_1 = nullptr;
  delete any_string; any_string = nullptr;

  restricted_auto = this->intersect(tmp_auto_2);
  delete tmp_auto_2; tmp_auto_2 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id << " = [" << this->id << "]->restrictIndexOfTo(" << index_auto->getId() << ", " << search_auto->id << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictLastIndexOfTo(int index, StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->restrictLastIndexOfTo(index_auto, search_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictLastIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto) {
  StringAutomaton_ptr restricted_auto = nullptr, complement_auto = nullptr,
          closure_auto = nullptr, tmp_auto_1 = nullptr, tmp_auto_2;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA());

  complement_auto = search_auto->complement();
  closure_auto = complement_auto->closure();
  delete complement_auto; complement_auto = nullptr;

  tmp_auto_1 = length_string_auto->concat(search_auto);
  tmp_auto_2 = tmp_auto_1->concat(closure_auto);
  length_string_auto->dfa = nullptr;
  delete length_string_auto; length_string_auto = nullptr;
  delete tmp_auto_1; tmp_auto_1 = nullptr;

  restricted_auto = this->intersect(tmp_auto_2);
  delete tmp_auto_2; tmp_auto_2 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id << " = [" << this->id << "]->restrictLastIndexOfTo(" << index_auto->getId() << ", " << search_auto->id << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictFromIndexToEndTo(int index, StringAutomaton_ptr sub_string_auto) {
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->restrictFromIndexToEndTo(index_auto, sub_string_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictFromIndexToEndTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto) {
  StringAutomaton_ptr restricted_auto = nullptr, tmp_auto_1 = nullptr, tmp_auto_2;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA());

  tmp_auto_1 = length_string_auto->concat(sub_string_auto);
  length_string_auto->dfa = nullptr;
  delete length_string_auto; length_string_auto = nullptr;

  restricted_auto = this->intersect(tmp_auto_1);
  delete tmp_auto_1; tmp_auto_1 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id << " = [" << this->id << "]->restrictFromIndexToEndTo(" << index_auto->getId() << ", " << sub_string_auto->id << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictAtIndexTo(int index, StringAutomaton_ptr sub_string_auto) {
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->restrictAtIndexTo(index_auto, sub_string_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::restrictAtIndexTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto) {
  StringAutomaton_ptr restricted_auto = nullptr, tmp_auto_1 = nullptr, tmp_auto_2;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA());
  StringAutomaton_ptr any_string = StringAutomaton::makeAnyString();

  tmp_auto_1 = length_string_auto->concat(sub_string_auto);
  tmp_auto_2 = tmp_auto_1->concat(any_string);
  length_string_auto->dfa = nullptr;
  delete length_string_auto; length_string_auto = nullptr;
  delete tmp_auto_1; tmp_auto_1 = nullptr;
  delete any_string; any_string = nullptr;

  restricted_auto = this->intersect(tmp_auto_2);
  delete tmp_auto_2; tmp_auto_2 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id << " = [" << this->id << "]->restrictIndexTo(" << index_auto->getId() << ", " << sub_string_auto->id << ")";

  return restricted_auto;
}

/**
 * TODO Efficiency of the pre image computations can be improved
 * if they are guided by the post image values
 */

StringAutomaton_ptr StringAutomaton::preToUpperCase(StringAutomaton_ptr rangeAuto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  result_dfa = dfaPreToUpperCase(dfa,
      StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->preToUpperCase()";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::preToLowerCase(StringAutomaton_ptr rangeAuto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  result_dfa = dfaPreToLowerCase(dfa,
      StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->preToLowerCase()";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::preTrim(StringAutomaton_ptr rangeAuto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  result_dfa = dfaPreTrim(dfa, ' ',
      StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->preTrim()";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::preConcatLeft(StringAutomaton_ptr right_auto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  if (right_auto->isAcceptingSingleString()) {
    std::string string_value = right_auto->getAnAcceptingString();

    char* string_value_ptr = new char[string_value.length() + 1];
    strncpy(string_value_ptr, string_value.c_str(), string_value.length() + 1);
    result_dfa = dfa_pre_concat_const(this->dfa, string_value_ptr, 1, num_of_variables, variable_indices);
    delete[] string_value_ptr;
  } else {
    result_dfa = dfa_pre_concat(this->dfa, right_auto->dfa, 1, num_of_variables, variable_indices);
  }

  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->preLeftConcat(" << right_auto->id << ")";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::preConcatRight(StringAutomaton_ptr left_auto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  if (left_auto->isAcceptingSingleString()) {
    std::string string_value = left_auto->getAnAcceptingString();
    char* string_value_ptr = new char[string_value.length() + 1];
    strncpy(string_value_ptr, string_value.c_str(), string_value.length() + 1);
    result_dfa = dfa_pre_concat_const(this->dfa, string_value_ptr, 2, num_of_variables, variable_indices);
    delete[] string_value_ptr;
  } else {
    result_dfa = dfa_pre_concat(this->dfa, left_auto->dfa, 2, num_of_variables, variable_indices);
  }

  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->preLeftConcat(" << left_auto->id << ")";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::preReplace(StringAutomaton_ptr searchAuto, std::string replaceString, StringAutomaton_ptr rangeAuto) {
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;
  std::vector<char> replaceStringVector(replaceString.begin(), replaceString.end());
  replaceStringVector.push_back('\0');

  result_dfa = dfa_pre_replace_str(dfa, searchAuto->dfa, &replaceStringVector[0],
      StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  result_auto = new StringAutomaton(result_dfa, num_of_variables);

  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id << " = [" << this->id << "]->preReplace(" << searchAuto->id << ", " << replaceString << ")";

  return result_auto;
}

bool StringAutomaton::hasEmptyString() {
  return isInitialStateAccepting();
}

bool StringAutomaton::isEmptyString() {
  return isOnlyInitialStateAccepting();
}

bool StringAutomaton::isAcceptingSingleString() {
  return isAcceptingSingleWord();
}

std::string StringAutomaton::getAnAcceptingString() {
  return Automaton::getAnAcceptingWord();
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

StringAutomaton_ptr StringAutomaton::dfaSharpStringWithExtraBit(int num_of_variables, int* variable_indices) {
  DFA_ptr sharp_string_dfa = nullptr;
  StringAutomaton_ptr sharp_string_extra_bit = nullptr;
  std::array<char, 2> statuses { '-', '+' };
  std::vector<char> reserved_1 = Automaton::getReservedWord('1', num_of_variables, true);
  char* sharp1 = &*reserved_1.begin();
  int *tmp_variable_indices = getIndices(num_of_variables, 1);
  dfaSetup(2, num_of_variables + 1, tmp_variable_indices);
  delete [] tmp_variable_indices;
  dfaAllocExceptions(1);
  dfaStoreException(1, sharp1); // word 111111111
  dfaStoreState(0);

  dfaAllocExceptions(0);
  dfaStoreState(1);

  sharp_string_dfa = dfaBuild(&*statuses.begin());
  sharp_string_extra_bit = new StringAutomaton(sharp_string_dfa, num_of_variables);

  DVLOG(VLOG_LEVEL) << sharp_string_extra_bit->id << " = dfaSharpStringWithExtraBit()";

  return sharp_string_extra_bit;
}

/**
 * @returns true if state has the given exception to a state that is not sink
 */
bool StringAutomaton::hasExceptionToValidStateFrom(int state, std::vector<char>& exception) {
  int sink_state = this->getSinkState();
  return (sink_state != this->getNextStateFrom(state, exception));
}

/**
 * @returns the next state if there is a transition with given exception
 */
int StringAutomaton::getNextStateFrom(int state, std::vector<char>& exception) {

  int next_state = -1; // only for initialization
  unsigned p, l, r, index = 0; // BDD traversal variables

  CHECK_EQ(num_of_variables, exception.size());

  p = this->dfa->q[state];

  for (int i = 0; i < num_of_variables; i++) {
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      next_state = l;
      break;
    } else {
      if (exception[i] == '0') {
        p = l;
      } else if (exception[i] == '1') {
        p = r;
      }
    }
  }

  if (index != BDD_LEAF_INDEX) {
    LOAD_lri(&this->dfa->bddm->node_table[p], l, r, index);
    if (index == BDD_LEAF_INDEX) {
      next_state = l;
    } else {
      LOG(FATAL) << "Please check this algorithm, something wrong with bdd traversal";
    }
  }

  return next_state;
}

/**
 * Returns final states
 */
std::vector<int> StringAutomaton::getAcceptingStates() {
  std::vector<int> final_states;
  for (int s = 0; s < this->dfa->ns; s++) {
    if (this->isAcceptingState(s)) {
      final_states.push_back(s);
    }
  }
  return final_states;
}

GraphOld* StringAutomaton::getGraph() {
  int sink_state = this->getSinkState();
  GraphOld* graph = new GraphOld();
  NodeOld* node = nullptr;
  std::set<int>* states = nullptr;

  for (int s = 0; s < this->dfa->ns; s++) {
    if (s == sink_state) {
      continue;
    }
    node = new NodeOld(s);
    node->setPrevStates(new std::set<int>());
    graph->addNode(node);
  }

  for (auto& entry : *(graph->getNodeMap())) {
    states = getNextStates(entry.first);
    states->erase(states->find(sink_state));
    entry.second->setNextStates(states);
    for (int n : *states) {
      graph->getNode(n)->addPrevState(entry.first);
    }
  }

   return graph;
}

} /* namespace Theory */
} /* namespace Vlab */


