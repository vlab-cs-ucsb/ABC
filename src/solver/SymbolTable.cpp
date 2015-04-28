/*
 * SymbolTable.cpp
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#include "SymbolTable.h"

namespace Vlab {
namespace SMT {
SymbolTable::SymbolTable()
	: global_var ("__vlab_global_var") {}
SymbolTable::~SymbolTable() {

	for (auto& entry : variables) {
		delete entry.second;
	}
}

void SymbolTable::addVariable(Variable_ptr variable) {
	auto result = variables.insert(std::make_pair(variable->getName(), variable));
	if (not result.second) {
		LOG(FATAL) << "Duplicate variable definition: " << *variable;
	} else {
		DVLOG(10) << "Variable defined: " << *variable;
	}
}

Variable_ptr SymbolTable::getVariable(std::string name) {
	auto it = variables.find(name);
	CHECK(it != variables.end()) << "Could not find variable: " << name;
	return it->second;
}

} /* namespace SMT */
} /* namespace Vlab */


