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
#include <set>
#include <algorithm>

#include <glog/logging.h>
#include "smt/ast.h"
#include "Value.h"

namespace Vlab {
namespace Solver {

typedef std::map<std::string, SMT::Variable_ptr> VariableMap;
typedef std::map<SMT::Variable_ptr, int> VariableCounterMap;
typedef std::map<SMT::Visitable_ptr, VariableCounterMap> VariableCounterTable;
typedef std::map<SMT::Variable_ptr, SMT::Term_ptr> VariableSubstitutionMap;
typedef std::map<SMT::Visitable_ptr, VariableSubstitutionMap> VariableSubstitutionTable;
typedef std::map<SMT::Variable_ptr, Value_ptr> VariableValueMap;
typedef std::map<SMT::Visitable_ptr, VariableValueMap> VariableValueTable;

class SymbolTable {
public:
  SymbolTable();
  virtual ~SymbolTable();

  bool isSatisfiable();
  void updateSatisfiability(bool value);
  void setScopeSatisfiability(bool value);
  void unionValuesOfVariables(SMT::Script_ptr script);

  void addVariable(SMT::Variable_ptr);
  SMT::Variable_ptr getVariable(std::string name);
  SMT::Variable_ptr getVariable(SMT::Term_ptr);
  VariableMap& getVariables();
  SMT::Variable_ptr getSymbolicVariable();

  void setBound(int bound);
  int getBound();

  void push_scope(SMT::Visitable_ptr);
  SMT::Visitable_ptr pop_scope();


  /*
   * Variable count functions, used for reduction and optimization
   */
  void increment_count(SMT::Variable_ptr);
  void decrement_count(SMT::Variable_ptr);
  int get_local_count(SMT::Variable_ptr);
  int get_total_count(SMT::Variable_ptr);
  void reset_count();

  bool add_var_substitution_rule(SMT::Variable_ptr, SMT::Term_ptr);
  bool remove_var_substitution_rule(SMT::Variable_ptr);
  SMT::Term_ptr get_variable_substitution_term(SMT::Variable_ptr);
  VariableSubstitutionMap& get_variable_substitution_map();
  VariableSubstitutionTable& get_variable_substitution_table();
  void reset_substitution_rules();

  Value_ptr getValue(std::string var_name);
  Value_ptr getValue(SMT::Variable_ptr variable);
  VariableValueMap& getValuesAtScope(SMT::Visitable_ptr scope);
  bool setValue(std::string var_name, Value_ptr value);
  bool setValue(SMT::Variable_ptr variable, Value_ptr value);


private:
  bool global_assertion_result;
  int bound;

  /**
   * Name to variable map
   */
  VariableMap variables;

  /**
   * There is a global scope
   * A new scope is generated when there is a disjuction
   */
  std::vector<SMT::Visitable_ptr> scope_stack;
  std::set<SMT::Visitable_ptr> scopes;

  /**
   * For each scope keep satisfiability result
   */
  std::map<SMT::Visitable_ptr, bool> is_scope_satisfiable;

  /**
   * Number of usages of variables
   */
  VariableCounterTable variable_counts_table;

  /**
   * Rules for eliminating variables
   */
  VariableSubstitutionTable variable_substitution_table;

  /**
   * Values of each variable for each scope
   */
  VariableValueTable variable_value_table;

  static const int VLOG_LEVEL;

};

typedef SymbolTable* SymbolTable_ptr;

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
