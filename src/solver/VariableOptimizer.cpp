/*
 * VariableOptimizer.cpp
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#include "VariableOptimizer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int VariableOptimizer::VLOG_LEVEL = 15;

VariableOptimizer::VariableOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
        : AstTraverser(script), symbol_table(symbol_table), target_type(Variable::Type::NONE),
          existential_elimination_phase(true) {
  setCallbacks();
}

VariableOptimizer::~VariableOptimizer() {
}

/**
 * Apply the following sequentially for Bool, Int, String variables
 * 1 - Collect existential elimination rules and apply them
 * 2 - Collect variable reduction rules and apply them
 */
void VariableOptimizer::start() {
  Counter counter(root, symbol_table);

  DVLOG(VLOG_LEVEL) << "Bool existential elimination";
  existential_elimination_phase = true;

  counter.start();
  target_type = Variable::Type::BOOL;
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();

  DVLOG(VLOG_LEVEL) << "Bool variable reduction";
  existential_elimination_phase = false;

  counter.start();
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();

  end();

  DVLOG(VLOG_LEVEL) << "Int existential elimination";
  existential_elimination_phase = true;

  counter.start();
  target_type = Variable::Type::INT;
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();

  DVLOG(VLOG_LEVEL) << "String existential elimination";
  counter.start();
  target_type = Variable::Type::STRING;
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();

//	Ast2Dot ast2dot(&std::cout);
//	ast2dot.start(root);
}

void VariableOptimizer::end() {
  if (VLOG_IS_ON(VLOG_LEVEL)) {
    for (auto& rule_map : symbol_table->get_variable_substitution_table()) {
      DVLOG(VLOG_LEVEL) << "Substitution map for scope: " << rule_map.first;
      for (auto& rule : rule_map.second) {
        DVLOG(VLOG_LEVEL) << "\t" << *rule.first << " (" << rule.first << ") -> " << *rule.second << " ("
                                   << rule.second << " )";
      }
    }
  }

  OptimizationRuleRunner rule_runner(root, symbol_table);
  rule_runner.start();

  eq_constraint_count.clear();
  symbol_table->reset_substitution_rules();
}

void VariableOptimizer::setCallbacks() {
  auto term_callback = [] (Term_ptr term) -> bool {
    return false;
  };

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  setCommandPreCallback(command_callback);
  setTermPreCallback(term_callback);
}

void VariableOptimizer::visitAnd(And_ptr and_term) {
  visit_children_of(and_term);
}

void VariableOptimizer::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void VariableOptimizer::visitEq(Eq_ptr eq_term) {
  if (existential_elimination_phase) {
    if (Term::Type::QUALIDENTIFIER == eq_term->left_term->getType()
            and Term::Type::QUALIDENTIFIER == eq_term->right_term->getType()) {

      Variable_ptr left_var = symbol_table->getVariable(eq_term->left_term);
      Variable_ptr right_var = symbol_table->getVariable(eq_term->right_term);
//			std::cout << "rule add = " << *left_var << " " << *right_var << std::endl;
//			std::cout << *left_var << ": " << symbol_table -> get_local_count(left_var->getName()) << ", " << symbol_table -> get_total_count(left_var->getName()) << std::endl;
//			std::cout << *right_var << ": " << symbol_table -> get_local_count(right_var->getName()) << ", " << symbol_table -> get_total_count(right_var->getName()) << std::endl;

      if (left_var->getType() == target_type) {
        int left_var_total_count = symbol_table->get_total_count(left_var);
        int left_var_local_count = symbol_table->get_local_count(left_var);
        int right_var_total_count = symbol_table->get_total_count(right_var);
        int right_var_local_count = symbol_table->get_local_count(right_var);

        if (left_var_total_count == left_var_local_count and right_var_total_count == right_var_local_count) {
          if (left_var_total_count <= right_var_total_count) {
            add_variable_substitution_rule(left_var, right_var, eq_term->right_term);
          } else {
            add_variable_substitution_rule(right_var, left_var, eq_term->left_term);
          }
        } else if (left_var_total_count == left_var_local_count) {
          add_variable_substitution_rule(left_var, right_var, eq_term->right_term);
        } else if (right_var_total_count == right_var_local_count) {
          add_variable_substitution_rule(right_var, left_var, eq_term->left_term);
        }
      }
    }
  }
  /**
   * We can eliminate boolean variables that are used for asserting some other constraints
   * Following are the conditions to do reduction
   * 1 - Variable may appear in only at most one constraint with other theories
   * 2 - Variable may appear in other places with some other boolean variables
   */
  else if (Variable::Type::BOOL == target_type) {
    if ((Term::Type::QUALIDENTIFIER == eq_term->left_term->getType()
            or Term::Type::QUALIDENTIFIER == eq_term->right_term->getType())
            and (Term::Type::QUALIDENTIFIER != eq_term->left_term->getType()
                    or Term::Type::QUALIDENTIFIER != eq_term->right_term->getType())) {

      Variable_ptr target_variable =
              (Term::Type::QUALIDENTIFIER == eq_term->left_term->getType()) ?
                      symbol_table->getVariable(eq_term->left_term) : symbol_table->getVariable(eq_term->right_term);

      if (target_variable->getType() == target_type) {
        Term_ptr target_term =
                (Term::Type::QUALIDENTIFIER == eq_term->left_term->getType()) ?
                        eq_term->right_term : eq_term->left_term;

//				std::cout << "rule add = " << *target_variable << " " << *target_term << std::endl;
        int target_var_total_count = symbol_table->get_total_count(target_variable);
        int target_var_local_count = symbol_table->get_local_count(target_variable);

        if (target_var_total_count == target_var_local_count) {
          add_variable_substitution_rule(target_variable, target_term);
        }
      }
    }
  }
}

void VariableOptimizer::add_variable_substitution_rule(Variable_ptr subject_var, Variable_ptr target_var,
        Term_ptr target_term) {
  if (subject_var->isSymbolic()) {
    return;
  }

  /* 1 - Update the target if the target variable is already a subject in the substitution map (rule transition) */
  for (auto& substitution_rule : symbol_table->get_variable_substitution_map()) {
    if (target_var == substitution_rule.first) {
      target_term = substitution_rule.second;
      break;
    }
  }

  /* 2 - Insert substitution rule */
  if (not symbol_table->add_var_substitution_rule(subject_var, target_term->clone())) {
    LOG(FATAL)<< "A variable cannot have multiple substitution rule: " << *subject_var;
  }

  /* 3 - Update a rule with the target if the subject variable is already a target */
  for (auto& substitution_rule : symbol_table->get_variable_substitution_map()) {
    if (Term::Type::QUALIDENTIFIER == substitution_rule.second->getType()) {
      if (subject_var == symbol_table->getVariable(substitution_rule.second)) {
        Term_ptr tmp_term = substitution_rule.second;
        substitution_rule.second = target_term->clone();
        delete tmp_term;
      }
    }
  }
}

void VariableOptimizer::add_variable_substitution_rule(Variable_ptr subject_var, Term_ptr target_term) {
  if (subject_var->isSymbolic()) {
    return;
  }
  eq_constraint_count[subject_var]++;
  switch (eq_constraint_count[subject_var]) {
  case 1:
    symbol_table->add_var_substitution_rule(subject_var, target_term->clone());
    break;
  case 2:
    symbol_table->remove_var_substitution_rule(subject_var);
    break;
  default:
    break;
  }
}

} /* namespace Solver */
} /* namespace Vlab */

