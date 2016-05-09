/*
 * FormulaOptimizer.cpp
 *
 *  Created on: May 12, 2015
 *      Author: baki
 */

#include "FormulaOptimizer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int FormulaOptimizer::VLOG_LEVEL = 14;

FormulaOptimizer::FormulaOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
        : AstTraverser(script), symbol_table(symbol_table) {
  setCallbacks();
}

FormulaOptimizer::~FormulaOptimizer() {
}

void FormulaOptimizer::start() {
  push_scope(root);
  visitScript(root);
  pop_scope();
  end();
}

void FormulaOptimizer::end() {
  SyntacticOptimizer syntactic_optimizer(root, symbol_table);
  syntactic_optimizer.start();
}

void FormulaOptimizer::setCallbacks() {
  auto term_callback = [] (Term_ptr term) -> bool {
    return false;
  };
  setTermPreCallback(term_callback);
}

void FormulaOptimizer::visitAssert(Assert_ptr assert_command) {
  visit_and_callback(assert_command->term);
}

void FormulaOptimizer::visitAnd(And_ptr and_term) {
  bool remove_and_term = false;
  for (auto& term : *(and_term->term_list)) {
    if (check_term(term)) {
      remove_and_term = true;
      break;
    }
  }

  if (remove_and_term) {
    DVLOG(VLOG_LEVEL) << "replace: 'and' with constant 'false'";
    callback = [and_term](Term_ptr& term) mutable {
      term = new TermConstant(new Primitive("false", Primitive::Type::BOOL));
      delete and_term;
    };
  } else {
    add_terms_to_check_list(and_term->term_list);
    for (auto& term : *(and_term->term_list)) {
      visit_and_callback(term);
    }
  }
}

void FormulaOptimizer::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    push_scope(term);
    visit_and_callback(term);
    pop_scope();
  }
}

void FormulaOptimizer::push_scope(Visitable_ptr key) {
  scope_stack.push_back(key);
}

Visitable_ptr FormulaOptimizer::pop_scope() {
  Visitable_ptr scope = scope_stack.back();
  auto it = check_table.find(scope);
  if (it != check_table.end()) {
    it = check_table.erase(it);
  }
  scope_stack.pop_back();
  return scope;
}

void FormulaOptimizer::add_term_to_check_list(Term_ptr term) {
  check_table[scope_stack.back()].push_back(term);
}
void FormulaOptimizer::add_terms_to_check_list(TermList_ptr term_list) {
  check_table[scope_stack.back()].insert(check_table[scope_stack.back()].end(), term_list->begin(), term_list->end());
}

bool FormulaOptimizer::check_term(Term_ptr term) {
  for (auto& scope : scope_stack) {
    for (auto& other_term : check_table[scope]) {
      if (term->type() == Term::Type::NOT and other_term->type() != Term::Type::NOT) {
        Not_ptr not_term = dynamic_cast<Not_ptr>(term);
        if (Ast2Dot::isEquivalent(not_term->term, other_term)) {
          return true;
        }
      } else if (term->type() != Term::Type::NOT and other_term->type() == Term::Type::NOT) {
        Not_ptr not_term = dynamic_cast<Not_ptr>(other_term);
        if (Ast2Dot::isEquivalent(not_term->term, term)) {
          return true;
        }
      }
    }
  }
  return false;
}

void FormulaOptimizer::visit_and_callback(Term_ptr& term) {
  visit(term);
  if (callback) {
    callback(term);
    callback = nullptr;
  }
}

} /* namespace Solver */
} /* namespace Vlab */
