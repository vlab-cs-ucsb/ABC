/*
 * SymbolTable.h
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYMBOLTABLE_H_
#define SOLVER_SYMBOLTABLE_H_

#include <map>

#include "../smt/ast.h"

namespace Vlab {
namespace SMT {

class SymbolTable {
public:
	SymbolTable();
	virtual ~SymbolTable();

	void addVariable(Variable_ptr);
	void addVariable(std::string name, Variable::Type type, bool is_symbolic);

private:
	std::string global_var;
	std::map<std::string, Variable_ptr> variables;
};

typedef SymbolTable* SymbolTable_ptr;

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
