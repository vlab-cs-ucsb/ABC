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
	: global_var ("__vlab_global_var"), bound(50) {}
SymbolTable::~SymbolTable() {

	for (auto& entry : variables) {
		delete entry.second;
	}
}

void SymbolTable::addVariable(Variable_ptr variable) {
	auto result = variables.insert(std::make_pair(variable->getName(), variable));
	if (not result.second) {
		LOG(FATAL) << "Duplicate variable definition: " << *variable;
	}
}

Variable_ptr SymbolTable::getVariable(std::string name) {
	auto it = variables.find(name);
	CHECK(it != variables.end()) << "Variable is not found: " << name;
	return it->second;
}

VariableMap& SymbolTable::getVariables() { return variables; }

void SymbolTable::setBound(int bound) { this->bound = bound; }

int SymbolTable::getBound() { return bound; }

void SymbolTable::push_scope(Visitable_ptr key) {
	scope_stack.push_back(key);
}

Visitable_ptr SymbolTable::pop_scope() {
	Visitable_ptr scope = scope_stack.back();
	scope_stack.pop_back();
	return scope;
}


void SymbolTable::increment_count(std::string var_name) {
	variable_counts_table[scope_stack.back()][var_name]++;
}

void SymbolTable::decrement_count(std::string var_name) {
	variable_counts_table[scope_stack.back()][var_name]--;
}

int SymbolTable::get_local_count(std::string var_name) {
	return variable_counts_table[scope_stack.back()][var_name];
}

int SymbolTable::get_total_count(std::string var_name) {
	int total = 0;
	for (auto& counters : variable_counts_table) {
		total += counters.second[var_name];
	}
	return total;
}
void SymbolTable::reset_count() {
	variable_counts_table.clear();
}


} /* namespace SMT */
} /* namespace Vlab */


