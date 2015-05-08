/*
 * SymbolTable.h
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYMBOLTABLE_H_
#define SOLVER_SYMBOLTABLE_H_

#include <vector>
#include <map>

#include <glog/logging.h>
#include "../smt/ast.h"

namespace Vlab {
namespace SMT {

typedef std::map<std::string, Variable_ptr> VariableMap;
typedef std::map<std::string, int> VariableCounterMap;
typedef std::map<Visitable_ptr, VariableCounterMap> VariableCounterTable;
typedef std::map<Variable_ptr, Term_ptr> VariableSubstitutionMap;
typedef std::map<Visitable_ptr, VariableSubstitutionMap> VariableSubstitutionTable;

class SymbolTable {
public:
	SymbolTable();
	virtual ~SymbolTable();

	void addVariable(Variable_ptr);
	Variable_ptr getVariable(std::string name);
	Variable_ptr getVariable(Term_ptr);
	VariableMap& getVariables();

	void setBound(int bound);
	int getBound();

	void push_scope(Visitable_ptr);
	Visitable_ptr pop_scope();

	bool add_var_substitution_rule(Variable_ptr, Term_ptr);
	bool remove_var_substitution_rule(Variable_ptr);
	Term_ptr get_variable_substitution_term(Variable_ptr);
	VariableSubstitutionMap& get_variable_substitution_map();
	VariableSubstitutionTable& get_variable_substitution_table();
	void reset_substitution_rules();

	/*
	 * Variable count functions, used for reduction and optimization
	 */
	void increment_count(std::string var_name);
	void decrement_count(std::string var_name);
	int get_local_count(std::string var_name);
	int get_total_count(std::string var_name);
	void reset_count();

private:
	std::string global_var;
	int bound;
	VariableMap variables;

	/**
	 * There is a global scope
	 * A new scope is generated when there is a disjuction of conjuctions
	 */
	std::vector<Visitable_ptr> scope_stack;

	/**
	 * Number of usages of variables
	 */
	VariableCounterTable variable_counts_table;

	/**
	 * Rules for eliminating variables
	 */
	VariableSubstitutionTable variable_substitution_table;


};

typedef SymbolTable* SymbolTable_ptr;

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
