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

void SymbolTable::addVariable(std::string name, Variable::Type type, bool is_symbolic) {

}

} /* namespace SMT */
} /* namespace Vlab */


