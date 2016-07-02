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
        : AstTraverser(script), symbol_table_(symbol_table), delete_term_(false) {
  setCallbacks();
}

FormulaOptimizer::~FormulaOptimizer() {
}

void FormulaOptimizer::start() {
  visitScript(root);
  end();
}

void FormulaOptimizer::end() {
//  SyntacticOptimizer syntactic_optimizer(root, symbol_table);
//  syntactic_optimizer.start();
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
  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;
  for (auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
    visit_and_callback(*iter);
    if (delete_term_) {
      delete (*iter);
      iter = and_term->term_list->erase(iter);
    } else {
      iter++;
    }
    delete_term_ = false;
  }
  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;
  reset_sets();
  // add check for and term
}

void FormulaOptimizer::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;
  for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
    visit_and_callback(*iter);
    if (delete_term_) {
      delete (*iter);
      iter = or_term->term_list->erase(iter);
    } else {
      iter++;
    }
    delete_term_ = false;
  }
  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;
  reset_sets();
  // add check for or term
}


void FormulaOptimizer::visitEq(Eq_ptr eq_term) {
  std::string left_expr = symbol_table_->get_var_name_for_expression(eq_term->left_term, Variable::Type::NONE);
  std::string right_expr = symbol_table_->get_var_name_for_expression(eq_term->right_term, Variable::Type::NONE);

  std::stringstream ss;
  ss << left_expr << right_expr;
  std::string term_expr = ss.str();
  ss.str("");
  ss.clear();

  // Dublicate check TODO handle a = b  b = a case
  if (eq_terms_.find(term_expr) != eq_terms_.end()) {
    delete_term_ = true;
  } else {
    eq_terms_.insert(term_expr);
  }
}

void FormulaOptimizer::visitNotEq(NotEq_ptr not_eq_term) {
  std::string left_expr = symbol_table_->get_var_name_for_expression(not_eq_term->left_term, Variable::Type::NONE);
  std::string right_expr = symbol_table_->get_var_name_for_expression(not_eq_term->right_term, Variable::Type::NONE);

  std::stringstream ss;
  ss << left_expr << right_expr;
  std::string term_expr = ss.str();
  ss.str("");
  ss.clear();

  // Dublicate check TODO handle a != b  b != a case
  if (not_eq_terms_.find(term_expr) != not_eq_terms_.end()) {
    delete_term_ = true;
  } else {
    not_eq_terms_.insert(term_expr);
  }

}

void FormulaOptimizer::visitGt(Gt_ptr gt_term) {
}

void FormulaOptimizer::visitGe(Ge_ptr ge_term) {
}

void FormulaOptimizer::visitLt(Lt_ptr lt_term) {
}

void FormulaOptimizer::visitLe(Le_ptr le_term) {
}

void FormulaOptimizer::visitIn(In_ptr in_term) {
}

void FormulaOptimizer::visitNotIn(NotIn_ptr not_in_term) {
}

void FormulaOptimizer::visitContains(Contains_ptr contains_term) {
}

void FormulaOptimizer::visitNotContains(NotContains_ptr not_contains_term) {
}

void FormulaOptimizer::visitBegins(Begins_ptr begins_term) {
}

void FormulaOptimizer::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void FormulaOptimizer::visitEnds(Ends_ptr ends_term) {
}

void FormulaOptimizer::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void FormulaOptimizer::reset_sets() {
  and_terms_.clear();
  or_terms_.clear();
  eq_terms_.clear();
  not_eq_terms_.clear();
  in_terms_.clear();
  not_in_terms_.clear();
  contains_terms_.clear();
  not_contains_terms_.clear();
  begins_terms_.clear();
  not_begins_terms_.clear();
  ends_terms_.clear();
  not_ends_terms_.clear();
  gt_terms_.clear();
  ge_terms_.clear();
  lt_terms_.clear();
  le_terms_.clear();
}

void FormulaOptimizer::visit_and_callback(Term_ptr& term) {
  visit(term);
  if (callback_) {
    callback_(term);
    callback_ = nullptr;
  }
}

} /* namespace Solver */
} /* namespace Vlab */
