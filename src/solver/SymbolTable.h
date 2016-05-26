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
#include "Component.h"
#include "theory/StringRelation.h"

namespace Vlab {
namespace Solver {

using VariableMap = std::map<std::string, SMT::Variable_ptr>;
using VariableCounterMap = std::map<SMT::Variable_ptr, int>;
using VariableCounterTable = std::map<SMT::Visitable_ptr, VariableCounterMap>;
using VariableSubstitutionMap = std::map<SMT::Variable_ptr, SMT::Variable_ptr>;
using VariableSubstitutionTable = std::map<SMT::Visitable_ptr, VariableSubstitutionMap>;
using VariableValueMap = std::map<SMT::Variable_ptr, Value_ptr>;
using VariableValueTable = std::map<SMT::Visitable_ptr, VariableValueMap>;
using ComponentMap = std::map<SMT::Visitable_ptr, std::vector<Component_ptr>>;
using ComponentRelationMap = std::map<Component_ptr, Theory::StringRelation_ptr>;

class SymbolTable {
public:
  SymbolTable();
  virtual ~SymbolTable();

  bool isSatisfiable();
  void updateSatisfiability(bool value);
  void setScopeSatisfiability(bool value);
  void unionValuesOfVariables(SMT::Script_ptr script);
  void clearLetScopes();

  void addVariable(SMT::Variable_ptr);
  SMT::Variable_ptr getVariable(std::string name);
  SMT::Variable_ptr getVariable(SMT::Term_ptr);
  VariableMap& getVariables();
  SMT::Variable_ptr getSymbolicVariable();
  int get_num_of_variables(SMT::Variable::Type type);

  void setBound(int bound);
  int getBound();

  void push_scope(SMT::Visitable_ptr);
  SMT::Visitable_ptr top_scope();
  void pop_scope();


  /*
   * Variable count functions, used for reduction and optimization
   */
  void increment_count(SMT::Variable_ptr);
  void decrement_count(SMT::Variable_ptr);
  int get_local_count(SMT::Variable_ptr);
  int get_total_count(SMT::Variable_ptr);
  void reset_count();

  /*
  Functions to store and update a list of independent components. 
  */

  void add_component(Component_ptr);
  void add_components(std::vector<Component_ptr>&);
  std::vector<Component_ptr> get_components_at(SMT::Visitable_ptr);
  ComponentMap get_component_map();

  int get_number_of_components(SMT::Visitable_ptr);

  /*Added function to keep track of the amount of reuse 
  int getReuse();
  void incrementReuse();
  */
  
  bool add_variable_substitution_rule(SMT::Variable_ptr, SMT::Variable_ptr);
  bool remove_variable_substitution_rule(SMT::Variable_ptr);
  bool is_variable_substituted(SMT::Visitable_ptr, SMT::Variable_ptr);
  bool is_variable_substituted(SMT::Variable_ptr);
  SMT::Variable_ptr get_substituted_variable(SMT::Visitable_ptr, SMT::Variable_ptr);
  SMT::Variable_ptr get_substituted_variable(SMT::Variable_ptr);
  int get_num_of_substituted_variables(SMT::Visitable_ptr scope, SMT::Variable::Type type);
  void merge_variable_substitution_rule_into_current_scope(SMT::Visitable_ptr scope, SMT::Variable_ptr variable);

  Value_ptr getValue(std::string var_name);
  Value_ptr getValue(SMT::Variable_ptr variable);
  VariableValueMap& getValuesAtScope(SMT::Visitable_ptr scope);
  bool setValue(std::string var_name, Value_ptr value);
  bool setValue(SMT::Variable_ptr variable, Value_ptr value);
  bool updateValue(std::string var_name, Value_ptr value);
  bool updateValue(SMT::Variable_ptr variable, Value_ptr value);

  Theory::StringRelation_ptr get_component_relation(Component_ptr component);
  bool set_component_relation(Component_ptr component, Theory::StringRelation_ptr str_rel);

  static const char ARITHMETIC[];
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
   * Applied existential elimination rules
   * For each scope:
   * Keeps a map for each variable that is substituted by another variable
   * based on equality constraints
   */
  VariableSubstitutionTable variable_substitution_table;

  /**
   * Values of each variable for each scope
   */
  VariableValueTable variable_value_table;

  /**
   * For each scope:
   * Constraints that are dependent each other stored in the same component
   */
  ComponentMap components_;

  /**
   * Each component has an associated string relation, for multitrack
   */
  ComponentRelationMap component_relations_;

  static const int VLOG_LEVEL;
  //int reuse; 

};

typedef SymbolTable* SymbolTable_ptr;

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
