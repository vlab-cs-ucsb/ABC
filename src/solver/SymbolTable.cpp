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
  : global_assertion_result(true), bound(50) {
}

SymbolTable::~SymbolTable() {
  for (auto& map_pair : variable_value_table) {
    for (auto& value_pair : map_pair.second) {
      delete value_pair.second;
    }
  }
  variable_value_table.clear();

  for (auto& entry : variables) {
    delete entry.second;
  }
}

bool SymbolTable::isSatisfiable() {
  return global_assertion_result;
}

void SymbolTable::updateSatisfiability(bool value) {
  global_assertion_result = global_assertion_result and value;
}

void SymbolTable::setScopeSatisfiability(bool value) {
  is_scope_satisfiable[scope_stack.back()] = value;
}

/**
 * Unions values of variables if there is disjunction in DNF form
 * (May need a fix when doing union for binary int automaton)
 *
 */
void SymbolTable::UnionValuesOfVariables(Script_ptr script) {
  if (scopes.size() < 2) {
    return;
  } else if (variable_value_table[script].size() > 0) { // a union operation is done before
    return;
  }

  push_scope(script);
  for (auto variable_entry : variables) {
    Value_ptr value = nullptr;
    for (auto scope : scopes) { // dnf form
      // union values
      if (is_scope_satisfiable[scope]) {
        auto variable = variable_entry.second;
        auto top_equiv_class = get_equivalence_class_of(variable);
        auto local_equiv_class = get_equivalence_class_of_at_scope(scope, variable);
        Value_ptr scope_var_value = nullptr;
        if (top_equiv_class or local_equiv_class) {
          variable = local_equiv_class->get_representative_variable();
        }
        scope_var_value = get_value_at_scope(scope, variable);

        if (value) {
          Value_ptr tmp = value;
          value = tmp->union_(scope_var_value);
          delete tmp;
        } else {
          value = scope_var_value->clone();
        }
      }
    }
    if (value) {
      setValue(variable_entry.second, value);
    }
  }
  pop_scope();
}

/**
 * Removes let scope and all its data
 */
void SymbolTable::clearLetScopes() {
  for (auto sit = scopes.begin(); sit != scopes.end(); ) {
    if (dynamic_cast<Let_ptr>(*sit) not_eq nullptr) {
      for (auto it = variable_value_table[*sit].begin(); it != variable_value_table[*sit].end(); ) {
        delete it->second; it->second = nullptr;
        it = variable_value_table[*sit].erase(it);
      }
      variable_value_table.erase(*sit);
      sit = scopes.erase(sit);
    } else {
      sit++;
    }
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

Variable_ptr SymbolTable::getVariable(Term_ptr term_ptr) {
  if (QualIdentifier_ptr variable_identifier = dynamic_cast<QualIdentifier_ptr>(term_ptr)) {
    return getVariable(variable_identifier->getVarName());
  }
  return nullptr;
}

SMT::Variable_ptr SymbolTable::get_variable_unsafe(std::string name) {
  if(variables.find(name) != variables.end()) {
    return variables[name];
  }
  return nullptr;
}

VariableMap& SymbolTable::getVariables() {
  return variables;
}

/*int SymbolTable::getReuse(){
  return reuse;
}

void SymbolTable::incrementReuse(){
  reuse++;
}*/


Variable_ptr SymbolTable::getSymbolicVariable() {
  auto it = std::find_if(variables.begin(), variables.end(),
  [](std::pair<std::string, Variable_ptr> entry) -> bool {
    return entry.second->isSymbolic();
  });
  if (it != variables.end()) {
    return it->second;
  }
  DVLOG(VLOG_LEVEL) << "no symbolic variable found";
  return nullptr;
}

int SymbolTable::get_num_of_variables(Variable::Type type) {
  int count = 0;
  for (auto entry : variables) {
    if (type == entry.second->getType()) {
      ++count;
    }
  }

  return count;
}

void SymbolTable::setBound(int bound) {
  this->bound = bound;
}

int SymbolTable::getBound() {
  return bound;
}

void SymbolTable::push_scope(Visitable_ptr key, bool save_scope) {
  scope_stack.push_back(key);
  if (save_scope) {
    scopes.insert(key);
  }
}

Visitable_ptr SymbolTable::top_scope() {
  return scope_stack.back();
}

void SymbolTable::pop_scope() {
  scope_stack.pop_back();
}



void SymbolTable::increment_count(Variable_ptr variable) {
  variable_counts_table[scope_stack.back()][variable]++;
}

void SymbolTable::decrement_count(Variable_ptr variable) {
  variable_counts_table[scope_stack.back()][variable]--;
}

int SymbolTable::get_local_count(Variable_ptr variable) {
  return variable_counts_table[scope_stack.back()][variable];
}

int SymbolTable::get_total_count(Variable_ptr variable) {
  int total = 0;
  for (auto& counters : variable_counts_table) {
    total += counters.second[variable];
  }
  return total;
}
void SymbolTable::reset_count() {
  variable_counts_table.clear();
}

int SymbolTable::get_num_of_substituted_variables(Visitable_ptr scope, Variable::Type type) {
  int count = 0;
  int num_of_var = 0;
  for (auto& equiv_entry : variable_equivalence_table[scope]) {
      if (equiv_entry.second->get_type() == type) {
        num_of_var = equiv_entry.second->get_number_of_variables();
        if (num_of_var > 1) {
          count = count + num_of_var - 1;
        } else {
          count = count + 1;
        }
      }
  }
  return count;
}

EquivClassTable& SymbolTable::get_equivalance_class_table() {
  return variable_equivalence_table;
}

/**
 * Get equivalence class for variable if exists
 * If it is found in upper scopes return a clone of it
 */
EquivalenceClass_ptr SymbolTable::get_equivalence_class_of(Variable_ptr variable) {
  auto entry = variable_equivalence_table[scope_stack.back()].find(variable);
  if (entry != variable_equivalence_table[scope_stack.back()].end()) {
    return entry->second; // return equiv class from current scope
  }

  if (scope_stack.size() > 1) { // search in upper scopes
    for (auto it = scope_stack.rbegin(); it != scope_stack.rend(); it++) {
      auto entry = variable_equivalence_table[(*it)].find(variable);
      if (entry != variable_equivalence_table[(*it)].end()) {
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
  auto it = variable_equivalence_table[scope].find(variable);
  if (it != variable_equivalence_table[scope].end()) {
    return it->second;
  }
  return nullptr;
}

void SymbolTable::add_variable_equiv_class_mapping(SMT::Variable_ptr variable, EquivalenceClass_ptr equiv_class) {
  variable_equivalence_table[scope_stack.back()][variable] = equiv_class;
}

Variable_ptr SymbolTable::get_representative_variable_of_at_scope(Visitable_ptr scope, Variable_ptr variable) {
  EquivalenceClass_ptr equiv_class = get_equivalence_class_of_at_scope(scope, variable);
  if (equiv_class != nullptr) {
    return equiv_class->get_representative_variable();
  }
  return variable;
}

Value_ptr SymbolTable::getValue(std::string var_name) {
  return getValue(getVariable(var_name));
}

Value_ptr SymbolTable::getValue(Variable_ptr variable) {

  for (auto it = scope_stack.rbegin(); it != scope_stack.rend(); it++) {
    auto representative_variable = get_representative_variable_of_at_scope((*it), variable);
    auto entry = variable_value_table[(*it)].find(representative_variable);
    if (entry != variable_value_table[(*it)].end()) {
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
  default:
    LOG(FATAL) << "unknown variable type" << *variable;
    break;
  }
  setValue(variable, result);
  return result;
}

Value_ptr SymbolTable::get_value_at_scope(Visitable_ptr scope, Variable_ptr variable) {
  auto it = variable_value_table[scope].find(variable);
  if (it != variable_value_table[scope].end()) {
    return it->second;
  }
  return nullptr;
}

VariableValueMap& SymbolTable::getValuesAtScope(Visitable_ptr scope) {
  return variable_value_table[scope];
}

bool SymbolTable::setValue(std::string var_name, Value_ptr value) {
  return setValue(getVariable(var_name), value);
}

bool SymbolTable::setValue(Variable_ptr variable, Value_ptr value) {
  variable_value_table[scope_stack.back()][variable] = value;
  return true;
}

/**
 * Intersect old value of the variable with new value and sets the
 * intersection as newest value.
 */
bool SymbolTable::updateValue(std::string var_name, Value_ptr value) {
  return updateValue(getVariable(var_name), value);
}

/**
 * Intersect old value of the variable with new value and sets the
 * intersection as newest value.
 * Deletes old value if it is read from same scope
 */
bool SymbolTable::updateValue(Variable_ptr variable, Value_ptr value) {
  Value_ptr variable_old_value = getValue(variable);
  Value_ptr variable_new_value = variable_old_value->intersect(value);

  if (variable_value_table[scope_stack.back()][variable] == variable_old_value) {
    setValue(variable, variable_new_value);
    delete variable_old_value; variable_old_value = nullptr;
  } else {
    setValue(variable, variable_new_value);
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

std::string SymbolTable::generate_internal_name(std::string name, SMT::Variable::Type type) {
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

