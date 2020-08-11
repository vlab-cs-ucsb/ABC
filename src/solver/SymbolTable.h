/*
 * SymbolTable.h
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYMBOLTABLE_H_
#define SOLVER_SYMBOLTABLE_H_

#include <algorithm>
// #include <bits/functional_hash.h>
#include <iterator>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
#include <glog/logging.h>
#include <atomic>
#include <thread>

#include "../smt/ast.h"
#include "../smt/typedefs.h"
#include "../theory/IntAutomaton.h"
#include "../theory/StringAutomaton.h"
#include "../theory/Formula.h"
#include "Ast2Dot.h"
#include "EquivalenceClass.h"
#include "options/Solver.h"
#include "Value.h"

namespace Vlab {
namespace Solver {

using VariableMap = std::map<std::string, SMT::Variable_ptr>;
using VariableCounterMap = std::map<SMT::Variable_ptr, int>;
using VariableCounterTable = std::map<SMT::Visitable_ptr, VariableCounterMap>;
using EquivClassMap = std::map<SMT::Variable_ptr, EquivalenceClass_ptr>;
using EquivClassTable = std::map<SMT::Visitable_ptr, EquivClassMap>;
using GroupMap = std::map<SMT::Variable_ptr, SMT::Variable_ptr>;
using VariableValueMap = std::map<SMT::Variable_ptr, Value_ptr>;
using VariableValueTable = std::map<SMT::Visitable_ptr, VariableValueMap>;
using TermChildrenTable = std::map<SMT::Visitable_ptr, std::set<std::string>>;

class SymbolTable;
using SymbolTable_ptr = SymbolTable*;

class SymbolTable {
public:

  SymbolTable(bool is_root = true);
  SymbolTable(const SymbolTable&);
  std::map<std::string,SMT::Variable_ptr> ss_term_vars;

  virtual ~SymbolTable();

  virtual SymbolTable_ptr clone() const;


  bool isSatisfiable();
  void update_satisfiability_result(bool value);
  void clearLetScopes();

  void add_variable(SMT::Variable_ptr);
  SMT::Variable_ptr get_variable(std::string name);
  SMT::Variable_ptr get_variable(SMT::Term_ptr);
  SMT::Variable_ptr get_variable_unsafe(std::string name);
  VariableMap& get_variables();
  int get_num_of_variables(SMT::Variable::Type type);

  void push_scope(SMT::Visitable_ptr, bool save_scope = true);
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

  /*Added function to keep track of the amount of reuse 
  int getReuse();
  void incrementReuse();
  */

  int get_num_of_substituted_variables(SMT::Visitable_ptr scope, SMT::Variable::Type type);
  EquivClassTable& get_equivalance_class_table();
  EquivalenceClass_ptr get_equivalence_class_of(SMT::Variable_ptr);
  EquivalenceClass_ptr get_equivalence_class_of_at_scope(SMT::Visitable_ptr scope, SMT::Variable_ptr);
  void add_variable_equiv_class_mapping(SMT::Variable_ptr, EquivalenceClass_ptr);
  SMT::Variable_ptr get_representative_variable_of_at_scope(SMT::Visitable_ptr scope, SMT::Variable_ptr);

  void set_variable_group_mapping(std::string variable_name, std::string group_name);
  void add_variable_group_mapping(std::string variable_name, std::string group_name);
  void add_variable_group_mapping(SMT::Variable_ptr, SMT::Variable_ptr);
  SMT::Variable_ptr get_group_variable_of(SMT::Variable_ptr);
  bool has_group_variable(std::string variable_name);

  Value_ptr get_value(std::string var_name);
  Value_ptr get_value(SMT::Variable_ptr variable);
  Value_ptr get_value_at_scope(SMT::Visitable_ptr scope, SMT::Variable_ptr variable);
  Value_ptr get_projected_value_at_scope(SMT::Visitable_ptr scope, SMT::Variable_ptr variable);
  VariableValueMap& get_values_at_scope(SMT::Visitable_ptr scope);
  void clear_variable_values();


  bool set_value(std::string var_name, Value_ptr value, bool clone = true);
  bool set_value(SMT::Variable_ptr variable, Value_ptr value, bool clone = true);
  bool IntersectValue(std::string var_name, Value_ptr value);
  bool IntersectValue(SMT::Variable_ptr variable, Value_ptr value);
  bool UnionValue(std::string var_name, Value_ptr value);
  bool UnionValue(SMT::Variable_ptr variable, Value_ptr value);

  bool clear_value(std::string var_name, SMT::Visitable_ptr scope);
  bool clear_value(SMT::Variable_ptr variable, SMT::Visitable_ptr scope);

  std::string get_var_name_for_expression(SMT::Visitable_ptr, SMT::Variable::Type);
  std::string get_var_name_for_node(SMT::Visitable_ptr, SMT::Variable::Type);

  void record_child_term(SMT::Visitable_ptr, std::string);
  bool has_child_term(SMT::Visitable_ptr, std::string);
  void clear_child_terms(SMT::Visitable_ptr);

  bool is_or_ite(SMT::Visitable_ptr);
  void add_or_ite(SMT::Visitable_ptr, SMT::Visitable_ptr, SMT::Visitable_ptr);
  void remove_or_ite(SMT::Visitable_ptr);
  SMT::Visitable_ptr get_ite_then_cond(SMT::Visitable_ptr);
  SMT::Visitable_ptr get_ite_else_cond(SMT::Visitable_ptr);
  void set_ite_then_cond(SMT::Visitable_ptr, SMT::Visitable_ptr);
  void set_ite_else_cond(SMT::Visitable_ptr, SMT::Visitable_ptr);

  void refactor_scope(SMT::Visitable_ptr old_scope_id, SMT::Visitable_ptr new_scope_id);
  void merge_scopes(SMT::Visitable_ptr parent_scope, SMT::Visitable_ptr child_scope);

  void set_count_variable(SMT::Primitive_ptr);
  SMT::Variable_ptr get_count_variable();
  bool has_count_variable();

  void add_unsorted_constraint(SMT::Visitable_ptr term);
  bool is_unsorted_constraint(SMT::Visitable_ptr term);
  void remove_unsorted_constraint(SMT::Visitable_ptr term);

  void increment_variable_usage(std::string);
  int get_variable_usage(std::string);
  void reset_variable_usage();

  // for normalization (variable/alphabet renaming)
  // for root scope only?
  void SetVariableMapping(std::map<std::string,std::string>);
  std::map<std::string,std::string> GetVariableMapping();
  std::map<std::string,std::string> GetReverseVariableMapping() {return reverse_variable_mapping_;}
  std::string GetMappedVariableName(std::string);

  std::map<char,char> GetCharacterMapping();
  std::map<char,char> GetReverseCharacterMapping();
  void SetCharacterMapping(std::map<char,char>);


  void LockValues() {values_lock_ = true;}
  void UnlockValues() {values_lock_ = false;}
  bool AreValuesLocked() {return values_lock_;}

private:
  std::string generate_internal_name(std::string, SMT::Variable::Type);

  bool global_assertion_result_;
  /**
   * Name to variable map
   */
  VariableMap variables_;

  VariableMap original_variables_;

  /**
   * There is a global scope
   * A new scope is generated when there is a disjuction
   */
  std::vector<SMT::Visitable_ptr> scope_stack_;
  std::set<SMT::Visitable_ptr> scopes_;

  /**
   * Number of usages of variables
   */
  VariableCounterTable variable_counts_table_;

  /**
   * Has a mapping from a variable to its corresponding equivalence class if any exists
   */
  EquivClassTable variable_equivalence_table_;

  /**
   * Has a mapping from a variable to its group variable if any; case occurs with multitrack auto
   */
  GroupMap variable_group_map_;

  /**
   * Projected values of variables that appear in multitrack automata
   * Stored only when necessary
   */
  VariableValueTable variable_projected_value_table_;

  /**
   * Values of each variable for each scope
   */
  VariableValueTable variable_value_table_;



  /**
    * string names of a terms children, mainly for ANDS
    */
  TermChildrenTable term_children_table_;
  

  std::map<SMT::Visitable_ptr,std::pair<SMT::Visitable_ptr, SMT::Visitable_ptr>> ite_conditions_;

  /**
   * Variable mapping (for normalization procedure)
   */
  std::map<std::string,std::string> variable_mapping_;
  std::map<std::string,std::string> reverse_variable_mapping_;

  std::map<char,char> character_mapping_;
  std::map<char,char> reverse_character_mapping_;

  std::set<std::string> last_constraints;

  /**
   * Count variable for kaluza tests
   */ 
  SMT::Primitive_ptr count_symbol_;

  bool is_root_table_;

  std::map<std::string,int> variable_usage_;

  std::atomic<bool> values_lock_;

  static const int VLOG_LEVEL;
  //int reuse; 

};



} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYMBOLTABLE_H_ */
