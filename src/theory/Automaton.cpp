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

Automaton::Automaton(Automaton::Type type)
	: type (type) { }

Automaton::Automaton(const Automaton& other)
	: type (other.type) { }

Automaton_ptr Automaton::clone() const { return new Automaton(*this); }

Automaton::~Automaton() { }

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
			LOG(FATAL) << "Unknown automaton type!";
			return "";
	}
}

Automaton::Type Automaton::getType() const { return type; }

std::ostream& operator<<(std::ostream& os, const Automaton& automaton) {
   return os <<  automaton.str();
}

} /* namespace Theory */
} /* namespace Vlab */
