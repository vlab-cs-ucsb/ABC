/*
 * BoolAutomaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "BoolAutomaton.h"

namespace Vlab {
namespace Theory {

const int BoolAutomaton::VLOG_LEVEL = 9;

int BoolAutomaton::DEFAULT_NUM_OF_VARIABLES = 2;

int* BoolAutomaton::DEFAULT_VARIABLE_INDICES = nullptr; // TODO remove or fix that

unsigned* BoolAutomaton::DEFAULT_UNSIGNED_VARIABLE_INDICES = nullptr; // TODO remove or fix that

BoolAutomaton::BoolAutomaton(DFA_ptr dfa)
        : Automaton(Automaton::Type::STRING), dfa (dfa), num_of_variables (BoolAutomaton::DEFAULT_NUM_OF_VARIABLES) {
}

BoolAutomaton::BoolAutomaton(DFA_ptr dfa, int num_of_variables)
        : Automaton(Automaton::Type::STRING), dfa (dfa), num_of_variables (num_of_variables) {
}

BoolAutomaton::BoolAutomaton(const BoolAutomaton& other)
        : Automaton(Automaton::Type::STRING), dfa(dfaCopy(other.dfa)), num_of_variables(other.num_of_variables) {
}

BoolAutomaton_ptr BoolAutomaton::clone() const {
	LOG(FATAL) << "IMPLEMENT ME";
	//return new BoolAutomaton(*this);
}

BoolAutomaton::~BoolAutomaton() {
}

BoolAutomaton_ptr BoolAutomaton::makeTrue(int num_of_variables, int* variable_indices) {
	LOG(FATAL) << "IMPLEMENT ME";
//  BoolAutomaton_ptr result = nullptr;
//  DFA_ptr true_dfa = nullptr;
//  std::array<char, 1> statuses { '+' };
//
//  dfaSetup(1, 0, nullptr);
//
//  dfaAllocExceptions(0);
//  dfaStoreState(0);
//
//  true_dfa = dfaBuild(&*statuses.begin());
//  result = new BoolAutomaton(true_dfa);
//  return result;
}

BoolAutomaton_ptr BoolAutomaton::makeFalse(int num_of_variables,int* variable_indices) {
	LOG(FATAL) << "IMPLEMENT ME";
//  BoolAutomaton_ptr result = nullptr;
//  DFA_ptr false_dfa = nullptr;
//  std::array<char, 1> statuses { '-' };
//
//  dfaSetup(1, 0, nullptr);
//
//  dfaAllocExceptions(0);
//  dfaStoreState(0);
//
//  false_dfa = dfaBuild(&*statuses.begin());
//  result = new BoolAutomaton(false_dfa);
//  return result;
}

void BoolAutomaton::toDot() {
  dfaPrintGraphviz(dfa, 0, nullptr);
}

} /* namespace Theory */
} /* namespace Vlab */
