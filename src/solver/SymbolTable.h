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
namespace Solver {

typedef std::map<std::string, SMT::Variable_ptr> VariableMap;
typedef std::map<SMT::Variable_ptr, int> VariableCounterMap;
typedef std::map<SMT::Visitable_ptr, VariableCounterMap> VariableCounterTable;
typedef std::map<SMT::Variable_ptr, SMT::Term_ptr> VariableSubstitutionMap;
typedef std::map<SMT::Visitable_ptr, VariableSubstitutionMap> VariableSubstitutionTable;

class SymbolTable {
public:
	SymbolTable();
	virtual ~SymbolTable();

	void addVariable(SMT::Variable_ptr);
	SMT::Variable_ptr getVariable(std::string name);
	SMT::Variable_ptr getVariable(SMT::Term_ptr);
	VariableMap& getVariables();

	void setBound(int bound);
	int getBound();

	void push_scope(SMT::Visitable_ptr);
	SMT::Visitable_ptr pop_scope();

	bool add_var_substitution_rule(SMT::Variable_ptr, SMT::Term_ptr);
	bool remove_var_substitution_rule(SMT::Variable_ptr);
	SMT::Term_ptr get_variable_substitution_term(SMT::Variable_ptr);
	VariableSubstitutionMap& get_variable_substitution_map();
	VariableSubstitutionTable& get_variable_substitution_table();
	void reset_substitution_rules();

	/*
	 * Variable count functions, used for reduction and optimization
	 */
	void increment_count(SMT::Variable_ptr);
	void decrement_count(SMT::Variable_ptr);
	int get_local_count(SMT::Variable_ptr);
	int get_total_count(SMT::Variable_ptr);
	void reset_count();

private:
	std::string global_var;
	int bound;
	VariableMap variables;

	/**
	 * There is a global scope
	 * A new scope is generated when there is a disjuction of conjuctions
	 */
	std::vector<SMT::Visitable_ptr> scope_stack;

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

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
