/*
 * SymbolTable.h
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYMBOLTABLE_H_
#define SOLVER_SYMBOLTABLE_H_

#include <map>

#include <glog/logging.h>
#include "../smt/ast.h"

namespace Vlab {
namespace SMT {

typedef std::map<std::string, Variable_ptr> VariableMap;

class SymbolTable {
public:
	SymbolTable();
	virtual ~SymbolTable();

	void addVariable(Variable_ptr);
	Variable_ptr getVariable(std::string name);
	VariableMap& getVariables();

	void setBound(int bound);
	int getBound();

private:
	std::string global_var;
	int bound;
	VariableMap variables;
};

typedef SymbolTable* SymbolTable_ptr;

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
