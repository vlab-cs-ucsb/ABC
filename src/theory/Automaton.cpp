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
        : type(type), id (Automaton::trace_id++) {
}

Automaton::Automaton(const Automaton& other)
        : type(other.type), id (Automaton::trace_id++) {
}

Automaton_ptr Automaton::clone() const {
  return new Automaton(*this);
}

Automaton::~Automaton() {
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

unsigned *Automaton::get_unsigned_indices_main(int length) {
  unsigned i;
  unsigned* indices;
  indices = new unsigned[length + 1];
  for (i = 0; i <= (unsigned) length; i++)
    indices[i] = i;
  return indices;
}

} /* namespace Theory */
} /* namespace Vlab */
