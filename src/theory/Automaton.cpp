/*
 * Automaton.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "Automaton.h"

namespace Vlab {
namespace Theory {

const int Automaton::VLOG_LEVEL = 9;

unsigned long Automaton::trace_id = 0;

const std::string Automaton::Name::NONE = "none";
const std::string Automaton::Name::BOOL = "BoolAutomaton";
const std::string Automaton::Name::INT = "IntAutomaton";
const std::string Automaton::Name::INTBOOl = "IntBoolAutomaton";
const std::string Automaton::Name::STRING = "StringAutomaton";

Automaton::Automaton(Automaton::Type type)
        : type(type), dfa(nullptr), num_of_variables(0), variable_indices(nullptr), id (Automaton::trace_id++) {
}

Automaton::Automaton(Automaton::Type type, DFA_ptr dfa, int num_of_variables)
        : type(type), dfa(dfa), num_of_variables(num_of_variables), id (Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables);
}

Automaton::Automaton(const Automaton& other)
        : type(other.type), dfa(dfaCopy(other.dfa)), num_of_variables(other.num_of_variables), id (Automaton::trace_id++) {
  variable_indices = getIndices(num_of_variables);
}

Automaton_ptr Automaton::clone() const {
  return new Automaton(*this);
}

Automaton::~Automaton() {
  dfaFree(dfa);
  dfa = nullptr;
  delete variable_indices;
}

std::string Automaton::str() const {
  switch (type) {
  case Automaton::Type::NONE:
    return Automaton::Name::NONE;
  case Automaton::Type::BOOL:
    return Automaton::Name::BOOL;
  case Automaton::Type::INT:
    return Automaton::Name::INT;
  case Automaton::Type::INTBOOl:
    return Automaton::Name::INTBOOl;
  case Automaton::Type::STRING:
    return Automaton::Name::STRING;
  default:
    LOG(FATAL)<< "Unknown automaton type!";
    return "";
  }
}

Automaton::Type Automaton::getType() const {
  return type;
}

std::ostream& operator<<(std::ostream& os, const Automaton& automaton) {
  return os << automaton.str();
}

int* Automaton::getIndices(int num_of_variables, int extra_num_of_variables) {
  int* indices = nullptr;
  int size = num_of_variables + extra_num_of_variables;

  indices = new int[size];
  for (int i = 0; i < size; i++) {
    indices[i] = i;
  }

  return indices;
}

unsigned* Automaton::getIndices(unsigned num_of_variables, unsigned extra_num_of_variables) {
  unsigned* indices = nullptr;
  unsigned size = num_of_variables + extra_num_of_variables;

  indices = new unsigned[size];
  for (unsigned i = 0; i < size; i++) {
    indices[i] = i;
  }

  return indices;
}

} /* namespace Theory */
} /* namespace Vlab */
