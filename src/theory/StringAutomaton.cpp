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

int* StringAutomaton::DEFAULT_VARIABLE_INDICES = StringAutomaton::allocateAscIIIndexWithExtraBit(StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

unsigned* StringAutomaton::DEFAULT_UNSIGNED_VARIABLE_INDICES = StringAutomaton::get_unsigned_indices_main(StringAutomaton::DEFAULT_NUM_OF_VARIABLES);

StringAutomaton::StringAutomaton(DFA_ptr dfa)
    : Automaton (Automaton::Type::STRING), dfa (dfa) { }

StringAutomaton::StringAutomaton(const StringAutomaton& other)
    : Automaton (Automaton::Type::STRING), dfa (other.dfa) { }

StringAutomaton::~StringAutomaton() {
  dfaFree(dfa);
  dfa = nullptr;
}

StringAutomaton_ptr StringAutomaton::clone() const { return new StringAutomaton(*this); }

/**
 * Creates an automaton that accepts nothing
 */
StringAutomaton_ptr StringAutomaton::makePhi() {
  DFA_ptr non_value_string_dfa = nullptr;
  StringAutomaton_ptr non_value_string = nullptr;
  std::array<char, 1> statuses {'-'};
  dfaSetup(1, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  dfaAllocExceptions(0);
  dfaStoreState(0);
  non_value_string_dfa = dfaBuild(&*statuses.begin());
  non_value_string = new StringAutomaton(non_value_string_dfa);

  DVLOG(VLOG_LEVEL) << non_value_string->id << " = makePhi()";

  return non_value_string;
}

StringAutomaton_ptr StringAutomaton::makeEmptyString() {
  DFA_ptr empty_string_dfa = nullptr;
  StringAutomaton_ptr empty_string = nullptr;
  std::array<char, 2> statuses {'+', '-'};

  dfaSetup(2, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  empty_string_dfa = dfaBuild(&*statuses.begin());
  empty_string = new StringAutomaton(empty_string_dfa);

  DVLOG(VLOG_LEVEL) << empty_string->id << " = makeEmptyString()";

  return empty_string;
}

StringAutomaton_ptr StringAutomaton::makeString(char c) {
  return StringAutomaton::makeString("" + c);
}

StringAutomaton_ptr StringAutomaton::makeString(std::string str) {
  DFA_ptr str_dfa = nullptr;
  StringAutomaton_ptr str_auto = nullptr;

  if ( str.empty() ) {
    return StringAutomaton::makeEmptyString();
  }

  str_auto = StringAutomaton::makeString(str, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);

 return str_auto;
}



StringAutomaton_ptr StringAutomaton::makeAnyString() {
  DFA_ptr any_string_dfa = dfaAllStringASCIIExceptReserveWords(StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES);
  StringAutomaton_ptr any_string = new StringAutomaton(any_string_dfa);

  DVLOG(VLOG_LEVEL) << any_string->id << " = makeAnyString()";

  return any_string;
}

void StringAutomaton::toDotAscii(bool print_sink, std::ostream& out) {
  int sink_status = (print_sink) ? 1 : 0;
  sink_status = (dfa->ns == 1 and dfa->f[0] == -1) ? 2 : sink_status;
  dfaPrintGraphvizAsciiRange(dfa, StringAutomaton::DEFAULT_NUM_OF_VARIABLES, StringAutomaton::DEFAULT_VARIABLE_INDICES, sink_status);
}

StringAutomaton_ptr StringAutomaton::makeString(std::string str, int num_of_variables, int variable_indices[]) {
  char* binChar = nullptr;
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;
  int str_length = str.length();
  int number_of_states = str_length + 2;
  char* statuses = new char[number_of_states + 1];

  dfaSetup(number_of_states, num_of_variables + 1, variable_indices);

  int i;
  for ( i = 0; i < str_length; i++ ) {
    dfaAllocExceptions(1);
    binChar = bintostrWithExtraBit((unsigned long) str[i], StringAutomaton::DEFAULT_NUM_OF_VARIABLES);
    dfaStoreException(i + 1, binChar);
    dfaStoreState(str_length + 1);
    statuses[i] = '0';
    delete binChar;
  }

  dfaAllocExceptions(0);
  dfaStoreState(str_length + 1);
  statuses[str_length] = '+';
  CHECK_EQ(str_length, i);

  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(str_length + 1);
  statuses[str_length + 1] = '-';
  statuses[str_length + 2] = '\0';
  result_dfa = dfaBuild(statuses);
  result_auto = new StringAutomaton(result_dfa);
  delete statuses;

  return result_auto;
}

int* StringAutomaton::allocateAscIIIndexWithExtraBit(int length) {
  int* indices = new int[length + 1];
  int i;
  for ( i = 0; i <= length; i++ ) {
    indices[i] = i;
  }
  return indices;
}

} /* namespace Theory */
} /* namespace Vlab */
