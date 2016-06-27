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
 * Unions values of variables if there is disjunction
 * (May need a fix when doing union for binary int automaton)
 * TODO Test with disjunctions
 */
void SymbolTable::unionValuesOfVariables(Script_ptr script) {
  if (scopes.size() < 2) {
    return;
  } else if (variable_value_table[script].size() > 0) { // a union operation is done before
    return;
  }

  push_scope(script);
  for (auto variable_entry : variables) {
    Value_ptr value = nullptr;
    for (auto scope : scopes) {

      // first check and merge substitution rules
      auto substituted_variable = get_substituted_variable(scope, variable_entry.second);
      if (substituted_variable != nullptr) { // update rule in the global scope
        merge_variable_substitution_rule_into_current_scope(scope, variable_entry.second);
      } else {
        substituted_variable = variable_entry.second;
      }

      // union values
      if (is_scope_satisfiable[scope]) {
        auto scope_var_value = variable_value_table[scope].find(substituted_variable);
        if (scope_var_value != variable_value_table[scope].end()) {
          if (value) {
            Value_ptr tmp = value;
            value = tmp->union_(scope_var_value->second);
            delete tmp;
          } else {
            value = scope_var_value->second->clone();
          }
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
  std::cout << "calling clear let scope " << std::endl;
  for (auto sit = scopes.begin(); sit != scopes.end(); ) {
    if (dynamic_cast<Let_ptr>(*sit) not_eq nullptr) {
      LOG(FATAL) << "trying to cler a let scope";
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
    LOG(FATAL)<< "Duplicate variable definition: " << *variable;
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
  LOG(FATAL) << "no symbolic variable found";
  return nullptr;
}

int SymbolTable::get_num_of_variables(Variable::Type type) {
  int count = 0;
  for (auto entry : variables) {
    if (type == entry.second->getType()) {
      ++count;
    }
  }

  if (Variable::Type::INT == type) {
    --count; // exclude artificial int variable
  }

  return count;
}

void SymbolTable::setBound(int bound) {
  this->bound = bound;
}

int SymbolTable::getBound() {
  return bound;
}

void SymbolTable::push_scope(Visitable_ptr key) {
  scope_stack.push_back(key);
  scopes.insert(key);
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

bool SymbolTable::add_variable_substitution_rule(Variable_ptr subject_variable, Variable_ptr target_variable) {
  auto result = variable_substitution_table[scope_stack.back()].insert(std::make_pair(subject_variable, target_variable));
  return result.second;
}

bool SymbolTable::remove_variable_substitution_rule(SMT::Variable_ptr variable) {
  auto it = variable_substitution_table[scope_stack.back()].find(variable);
  if (it != variable_substitution_table[scope_stack.back()].end()) {
    variable_substitution_table[scope_stack.back()].erase(it);
    return true;
  }
  return false;
}

bool SymbolTable::is_variable_substituted(Visitable_ptr scope, Variable_ptr variable) {
  auto it = variable_substitution_table[scope].find(variable);
  if (it != variable_substitution_table[scope].end()) {
    return true;
  }
  return false;
}

bool SymbolTable::is_variable_substituted(Variable_ptr variable) {
  return is_variable_substituted(scope_stack.back(), variable);
}

Variable_ptr SymbolTable::get_substituted_variable(Visitable_ptr scope, Variable_ptr variable) {
  auto it = variable_substitution_table[scope].find(variable);
  if (it != variable_substitution_table[scope].end()) {
    return it->second;
  }
  return nullptr;
}

Variable_ptr SymbolTable::get_substituted_variable(Variable_ptr variable) {
  return get_substituted_variable(scope_stack.back(), variable);
}

int SymbolTable::get_num_of_substituted_variables(Visitable_ptr scope, Variable::Type type) {
  int count = 0;
  for (auto& rule : variable_substitution_table[scope]) {
      if (rule.first->getType() == type and rule.second->getType() == type) {
        ++count;
      }
  }
  return count;
}

void SymbolTable::merge_variable_substitution_rule_into_current_scope(Visitable_ptr scope, Variable_ptr variable) {
  auto substituted_variable = get_substituted_variable(scope, variable);
  if (substituted_variable != nullptr) { // update rule in the global scope
    auto current_scope_substitution = get_substituted_variable(substituted_variable);
    if (current_scope_substitution != nullptr) { // if there is a reverse rule already in global scope, remove rule, do not add any rule
      remove_variable_substitution_rule(substituted_variable);
    } else {
      add_variable_substitution_rule(variable, substituted_variable); // adds rule to global scope
    }
  }
}

Value_ptr SymbolTable::getValue(std::string var_name) {
  return getValue(getVariable(var_name));
}

Value_ptr SymbolTable::getValue(Variable_ptr variable) {
  Value_ptr result = nullptr;

  for (auto it = scope_stack.rbegin(); it != scope_stack.rend(); it++) {
    auto entry = variable_value_table[(*it)].find(variable);
    if (entry != variable_value_table[(*it)].end()) {
      return entry->second;
    }
  }

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

