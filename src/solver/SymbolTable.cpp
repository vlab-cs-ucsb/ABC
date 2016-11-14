/*
 * SymbolTable.cpp
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#include "SymbolTable.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int SymbolTable::VLOG_LEVEL = 10;

SymbolTable::SymbolTable()
  : global_assertion_result_(true) {
}

SymbolTable::~SymbolTable() {
  for (auto& map_pair : variable_value_table_) {
    for (auto& value_pair : map_pair.second) {
      delete value_pair.second;
    }
  }
  variable_value_table_.clear();

  for (auto& map_pair : variable_projected_value_table_) {
    for (auto& value_pair : map_pair.second) {
      delete value_pair.second;
    }
  }
  variable_projected_value_table_.clear();

  std::set<EquivalenceClass_ptr> equivalence_classes;
  for (auto& map_pair : variable_equivalence_table_) {
    for (auto& value_pair : map_pair.second) {
      equivalence_classes.insert(value_pair.second);
    }
  }
  variable_projected_value_table_.clear();
  for (auto& eq : equivalence_classes) {
    delete eq;
  }
  equivalence_classes.clear();

  for (auto& entry : variables_) {
    delete entry.second;
  }
}

bool SymbolTable::isSatisfiable() {
  return global_assertion_result_;
}

void SymbolTable::update_satisfiability_result(bool value) {
  global_assertion_result_ = global_assertion_result_ and value;
}

/**
 * Removes let scope and all its data
 */
void SymbolTable::clearLetScopes() {
  for (auto sit = scopes_.begin(); sit != scopes_.end(); ) {
    if (dynamic_cast<Let_ptr>(*sit) not_eq nullptr) {

      for (auto it = variable_value_table_[*sit].begin(); it != variable_value_table_[*sit].end(); ) {
        delete it->second; it->second = nullptr;
        it = variable_value_table_[*sit].erase(it);
      }
      variable_value_table_.erase(*sit);
      sit = scopes_.erase(sit);
    } else {
      sit++;
    }
  }
}

void SymbolTable::add_variable(Variable_ptr variable) {
  auto result = variables_.insert(std::make_pair(variable->getName(), variable));
  if (not result.second) {
    LOG(FATAL) << "Duplicate variable definition: " << *variable;
  }
}

Variable_ptr SymbolTable::get_variable(std::string name) {
  auto it = variables_.find(name);
  CHECK(it != variables_.end()) << "Variable is not found: " << name;
  return it->second;
}

Variable_ptr SymbolTable::get_variable(Term_ptr term_ptr) {
  if (QualIdentifier_ptr variable_identifier = dynamic_cast<QualIdentifier_ptr>(term_ptr)) {
    return get_variable(variable_identifier->getVarName());
  }
  return nullptr;
}

Variable_ptr SymbolTable::get_variable_unsafe(std::string name) {
  if (variables_.find(name) != variables_.end()) {
    return variables_[name];
  }
  return nullptr;
}

VariableMap& SymbolTable::get_variables() {
  return variables_;
}

/*int SymbolTable::getReuse(){
  return reuse;
}

void SymbolTable::incrementReuse(){
  reuse++;
}*/

int SymbolTable::get_num_of_variables(Variable::Type type) {
  int count = 0;
  for (auto entry : variables_) {
    if (type == entry.second->getType()) {
      ++count;
    }
  }

  return count;
}

void SymbolTable::push_scope(Visitable_ptr key, bool save_scope) {
  scope_stack_.push_back(key);
  if (save_scope) {
    scopes_.insert(key);
  }
}

Visitable_ptr SymbolTable::top_scope() {
  return scope_stack_.back();
}

void SymbolTable::pop_scope() {
  scope_stack_.pop_back();
}



void SymbolTable::increment_count(Variable_ptr variable) {
  variable_counts_table_[scope_stack_.back()][variable]++;
}

void SymbolTable::decrement_count(Variable_ptr variable) {
  variable_counts_table_[scope_stack_.back()][variable]--;
}

int SymbolTable::get_local_count(Variable_ptr variable) {
  return variable_counts_table_[scope_stack_.back()][variable];
}

int SymbolTable::get_total_count(Variable_ptr variable) {
  int total = 0;
  for (auto& counters : variable_counts_table_) {
    total += counters.second[variable];
  }
  return total;
}
void SymbolTable::reset_count() {
  variable_counts_table_.clear();
}

int SymbolTable::get_num_of_substituted_variables(Visitable_ptr scope, Variable::Type type) {
  int count = 0;
  int num_of_var = 0;
  std::set<EquivalenceClass_ptr> unique_ones;
  for (auto& equiv_entry : variable_equivalence_table_[scope]) {
    unique_ones.insert(equiv_entry.second);
  }
  for (auto& equiv_class : unique_ones) {
    if (equiv_class->get_type() == type) {
      num_of_var = equiv_class->get_number_of_variables();
      if (num_of_var > 1 and !equiv_class->has_constant()) {
        count = count + num_of_var - 1;
      } else {
        count = count + num_of_var;
      }
    }
  }
  return count;
}

EquivClassTable& SymbolTable::get_equivalance_class_table() {
  return variable_equivalence_table_;
}

/**
 * Get equivalence class for variable if exists
 * If it is found in upper scopes return a clone of it
 */
EquivalenceClass_ptr SymbolTable::get_equivalence_class_of(Variable_ptr variable) {
  auto entry = variable_equivalence_table_[scope_stack_.back()].find(variable);
  if (entry != variable_equivalence_table_[scope_stack_.back()].end()) {
    return entry->second; // return equiv class from current scope
  }

  if (scope_stack_.size() > 1) { // search in upper scopes
    for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); it++) {
      auto entry = variable_equivalence_table_[(*it)].find(variable);
      if (entry != variable_equivalence_table_[(*it)].end()) {
        // clone equiv class from parent and put it to the current scope
        auto equiv_class = entry->second->clone();
        add_variable_equiv_class_mapping(variable, equiv_class);
        return equiv_class;
      }
    }
  }

  return nullptr;
}

EquivalenceClass_ptr SymbolTable::get_equivalence_class_of_at_scope(Visitable_ptr scope, Variable_ptr variable) {
  auto it = variable_equivalence_table_[scope].find(variable);
  if (it != variable_equivalence_table_[scope].end()) {
    return it->second;
  }
  return nullptr;
}

void SymbolTable::add_variable_equiv_class_mapping(Variable_ptr variable, EquivalenceClass_ptr equiv_class) {
  variable_equivalence_table_[scope_stack_.back()][variable] = equiv_class;
}

Variable_ptr SymbolTable::get_representative_variable_of_at_scope(Visitable_ptr scope, Variable_ptr variable) {
  EquivalenceClass_ptr equiv_class = get_equivalence_class_of_at_scope(scope, variable);
  if (equiv_class != nullptr) {
    return equiv_class->get_representative_variable();
  }
  return variable;
}

void SymbolTable::add_variable_group_mapping(std::string variable_name, std::string group_name) {
  auto variable = get_variable_unsafe(variable_name);
  if (variable not_eq nullptr) {
    return add_variable_group_mapping(get_variable(variable_name), get_variable(group_name));
  }
  return;
}

void SymbolTable::add_variable_group_mapping(Variable_ptr variable, Variable_ptr group_variable) {
  auto it = variable_group_map_.find(variable);
  if (it != variable_group_map_.end() and it->second != group_variable) {
    LOG(FATAL) << "duplicate mapping!, fix me";
  }
  variable_group_map_[variable] = group_variable;
}

Variable_ptr SymbolTable::get_group_variable_of(Variable_ptr variable) {
  const auto& el = variable_group_map_.find(variable);
  if (el != variable_group_map_.end()) {
    return el->second;
  }
  return variable;
}

Value_ptr SymbolTable::get_value(std::string var_name) {
  return get_value(get_variable(var_name));
}

Value_ptr SymbolTable::get_value(Variable_ptr variable) {
  for (auto it = scope_stack_.rbegin(); it != scope_stack_.rend(); it++) {
    auto representative_variable = get_representative_variable_of_at_scope((*it), variable);
//    auto group_variable = get_group_variable_of(representative_variable);
//    auto entry = variable_value_table_[(*it)].find(group_variable);
    auto entry = variable_value_table_[(*it)].find(representative_variable);
    if (entry != variable_value_table_[(*it)].end()) {
      return entry->second;
    }
  }

  Value_ptr result = nullptr;

  switch (variable->getType()) {
  case Variable::Type::BOOL:
    LOG(FATAL) << "bool variables are not supported explicitly yet: " << *variable;
    break;
  case Variable::Type::INT:
    result = new Value(Theory::IntAutomaton::makeAnyInt());
    DVLOG(VLOG_LEVEL) << "initialized variable as any integer: " << *variable;
    break;
  case Variable::Type::STRING:
    result = new Value(Theory::StringAutomaton::makeAnyString());
    DVLOG(VLOG_LEVEL) << "initialized variable as any string: " << *variable;
    break;
  case Variable::Type::NONE:
    return nullptr;
    break;
  default:
    LOG(FATAL) << "unknown variable type" << *variable;
    break;
  }

  set_value(variable, result);
  return result;
}

Value_ptr SymbolTable::get_value_at_scope(Visitable_ptr scope, Variable_ptr variable) {
  auto representative_variable = get_representative_variable_of_at_scope(scope, variable);
//  auto group_variable = get_group_variable_of(representative_variable);
//  auto it = variable_value_table_[scope].find(group_variable);
  auto it = variable_value_table_[scope].find(representative_variable);
  if (it != variable_value_table_[scope].end()) {
    return it->second;
  }
  return nullptr;
}

Value_ptr SymbolTable::get_projected_value_at_scope(Visitable_ptr scope, Variable_ptr variable) {
  auto representative_variable = get_representative_variable_of_at_scope(scope, variable);
  auto it = variable_value_table_[scope].find(representative_variable);
  if (it != variable_value_table_[scope].end()) {
    return it->second;
  }

  // if projected value is computed return it
  auto pit = variable_projected_value_table_[scope].find(representative_variable);
  if (pit != variable_projected_value_table_[scope].end()) {
    return pit->second;
  }

  // compute projected value if the variable is in a group
  auto group_variable = get_group_variable_of(representative_variable);
  it = variable_value_table_[scope].find(group_variable);
  if (it != variable_value_table_[scope].end()) {
    Value_ptr result = nullptr;
    if (Value::Type::BINARYINT_AUTOMATON == it->second->getType()) {
      auto relational_auto = it->second->getBinaryIntAutomaton();
      auto projected_auto = relational_auto->GetBinaryAutomatonFor(representative_variable->getName());
      result = new Value(projected_auto);
    } else if (Value::Type::MULTITRACK_AUTOMATON == it->second->getType()) {
      auto relational_auto = it->second->getMultiTrackAutomaton();
      auto string_relation = relational_auto->getRelation();
      auto projected_auto = relational_auto->getKTrack(string_relation->get_variable_index(representative_variable->getName()));
      result = new Value(projected_auto);
    } else {
      LOG(FATAL) << "Value error, fix me";
    }
    variable_projected_value_table_[scope][representative_variable] = result;
    return result;
  }
  // unconstrainted variable
  return nullptr;
}


VariableValueMap& SymbolTable::get_values_at_scope(Visitable_ptr scope) {
  return variable_value_table_[scope];
}

bool SymbolTable::set_value(std::string var_name, Value_ptr value) {
  return set_value(get_variable(var_name), value);
}

bool SymbolTable::set_value(Variable_ptr variable, Value_ptr value) {
  auto& current_scope_values = variable_value_table_[top_scope()];
  auto it = current_scope_values.find(variable);
  if (it not_eq current_scope_values.end()) {
    delete it->second;
    it->second = value;
  } else {
    current_scope_values[variable] = value;
  }
  return value->is_satisfiable();
}

/**
 * Intersect old value of the variable with new value and sets the
 * intersection as newest value.
 */
bool SymbolTable::IntersectValue(std::string var_name, Value_ptr value) {
  return IntersectValue(get_variable(var_name), value);
}

/**
 * Intersect old value of the variable with new value and sets the
 * intersection as newest value.
 * Deletes old value if it is read from same scope
 */
bool SymbolTable::IntersectValue(Variable_ptr variable, Value_ptr value) {
  Value_ptr variable_old_value = get_value(variable);
  Value_ptr variable_new_value = nullptr;
  if (variable_old_value not_eq nullptr) {
    variable_new_value = variable_old_value->intersect(value);
  } else {
    variable_new_value = value->clone();
  }
  return set_value(variable, variable_new_value);
}

bool SymbolTable::UnionValue(std::string var_name, Value_ptr value) {
  return UnionValue(get_variable(var_name), value);
}

bool SymbolTable::UnionValue(Variable_ptr variable, Value_ptr value) {
  Value_ptr variable_old_value = get_value(variable);
  Value_ptr variable_new_value = nullptr;
  if (variable_old_value not_eq nullptr) {
    variable_new_value = variable_old_value->union_(value);
    auto it = variable_value_table_[top_scope()].find(variable);
    if (it != variable_value_table_[top_scope()].end() and it->second == variable_old_value) {
      delete variable_old_value;
    }
  } else {
    variable_new_value = value->clone();
  }
  return set_value(variable, variable_new_value);
}

bool SymbolTable::clear_value(std::string var_name, Visitable_ptr scope) {
  Variable_ptr variable = get_variable(var_name);
  return clear_value(variable,scope);
}

bool SymbolTable::clear_value(Variable_ptr variable, Visitable_ptr scope) {
  auto it = variable_value_table_[scope].find(variable);
  if (it != variable_value_table_[scope].end()) {
    delete it->second;
    variable_value_table_[scope].erase(it);
  }
  return true;
}

/**
 * @returns a name for the expression using its string version
 */
std::string SymbolTable::get_var_name_for_expression(Visitable_ptr node, Variable::Type type) {
  std::string str_value = Ast2Dot::toString(node);
  std::hash<std::string> hash_func;
  std::stringstream ss;
  ss << hash_func(str_value);
  return generate_internal_name(ss.str(), type);
}

/**
 * @returns a name for the node identify by memory address of the node
 */
std::string SymbolTable::get_var_name_for_node(Visitable_ptr node, Variable::Type type) {
  std::stringstream ss;
  ss << node;
  return generate_internal_name(ss.str(), type);
}

std::string SymbolTable::generate_internal_name(std::string name, Variable::Type type) {
  std::stringstream ss;
  ss << "__vlab__";
  switch (type) {
  case Variable::Type::BOOL:
    ss << "bool";
    break;
  case Variable::Type::INT:
    ss << "int";
    break;
  case Variable::Type::STRING:
    ss << "str";
    break;
  default:
    break;
  }
  ss << "__" << name;
  return ss.str();
}

} /* namespace Solver */
} /* namespace Vlab */
