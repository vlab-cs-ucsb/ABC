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
        : AstTraverser(script), symbol_table_(symbol_table) {
  setCallbacks();
}

FormulaOptimizer::~FormulaOptimizer() {
}

void FormulaOptimizer::start() {
  visitScript(root_);
  end();
}

void FormulaOptimizer::end() {
//  SyntacticOptimizer syntactic_optimizer(root_, symbol_table_);
//  syntactic_optimizer.start();
}

void FormulaOptimizer::setCallbacks() {
  auto term_callback = [] (Term_ptr term) -> bool {
    return false;
  };
  setTermPreCallback(term_callback);
}

void FormulaOptimizer::visitAssert(Assert_ptr assert_command) {
  visit(assert_command->term);
}

void FormulaOptimizer::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;
  visit_term_list(and_term->term_list);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

  if (and_term->term_list->size() != terms_.size()) {
    // duplicate constraints remove them
    and_term->term_list->clear();
    for (auto& entry : terms_) {
      and_term->term_list->push_back(entry.second.back());
      entry.second.pop_back();
      for(auto term : entry.second) {
        delete term; // delete duplicate terms
      }
    }
  }

  terms_.clear();
  // TODO add and term check
}

void FormulaOptimizer::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;
  visit_term_list(or_term->term_list);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;

  if (or_term->term_list->size() != terms_.size()) {
    // duplicate constraints remove them
    or_term->term_list->clear();
    for (auto& entry : terms_) {
      or_term->term_list->push_back(entry.second.back());
      entry.second.pop_back();
      for(auto term : entry.second) {
        delete term; // delete duplicate terms
      }
    }
  }

  terms_.clear();
  // TODO add or term check
}


void FormulaOptimizer::visitEq(Eq_ptr eq_term) {
  const std::string left_expr = Ast2Dot::toString(eq_term->left_term);
  const std::string right_expr = Ast2Dot::toString(eq_term->right_term);

  if (right_expr < left_expr) {
    std::swap(eq_term->left_term, eq_term->right_term);
  }

  std::stringstream ss;
  ss << *eq_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(eq_term);
}

void FormulaOptimizer::visitNotEq(NotEq_ptr not_eq_term) {
  const std::string left_expr = Ast2Dot::toString(not_eq_term->left_term);
  const std::string right_expr = Ast2Dot::toString(not_eq_term->right_term);

  if (right_expr < left_expr) {
    std::swap(not_eq_term->left_term, not_eq_term->right_term);
  }

  std::stringstream ss;
  ss << *not_eq_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(not_eq_term);
}

void FormulaOptimizer::visitGt(Gt_ptr gt_term) {
  const std::string left_expr = Ast2Dot::toString(gt_term->left_term);
  const std::string right_expr = Ast2Dot::toString(gt_term->right_term);

  std::stringstream ss;
  ss << *gt_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(gt_term);
}

void FormulaOptimizer::visitGe(Ge_ptr ge_term) {
  const std::string left_expr = Ast2Dot::toString(ge_term->left_term);
  const std::string right_expr = Ast2Dot::toString(ge_term->right_term);

  std::stringstream ss;
  ss << *ge_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(ge_term);
}

void FormulaOptimizer::visitLt(Lt_ptr lt_term) {
  const std::string left_expr = Ast2Dot::toString(lt_term->left_term);
  const std::string right_expr = Ast2Dot::toString(lt_term->right_term);

  std::stringstream ss;
  ss << *lt_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(lt_term);
}

void FormulaOptimizer::visitLe(Le_ptr le_term) {
  const std::string left_expr = Ast2Dot::toString(le_term->left_term);
  const std::string right_expr = Ast2Dot::toString(le_term->right_term);

  std::stringstream ss;
  ss << *le_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(le_term);
}

void FormulaOptimizer::visitIn(In_ptr in_term) {
  const std::string left_expr = Ast2Dot::toString(in_term->left_term);
  const std::string right_expr = Ast2Dot::toString(in_term->right_term);

  std::stringstream ss;
  ss << *in_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(in_term);
}

void FormulaOptimizer::visitNotIn(NotIn_ptr not_in_term) {
  const std::string left_expr = Ast2Dot::toString(not_in_term->left_term);
  const std::string right_expr = Ast2Dot::toString(not_in_term->right_term);

  std::stringstream ss;
  ss << *not_in_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(not_in_term);
}

void FormulaOptimizer::visitContains(Contains_ptr contains_term) {
  const std::string left_expr = Ast2Dot::toString(contains_term->subject_term);
  const std::string right_expr = Ast2Dot::toString(contains_term->search_term);

  std::stringstream ss;
  ss << *contains_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(contains_term);
}

void FormulaOptimizer::visitNotContains(NotContains_ptr not_contains_term) {
  const std::string left_expr = Ast2Dot::toString(not_contains_term->subject_term);
  const std::string right_expr = Ast2Dot::toString(not_contains_term->search_term);

  std::stringstream ss;
  ss << *not_contains_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(not_contains_term);
}

void FormulaOptimizer::visitBegins(Begins_ptr begins_term) {
  const std::string left_expr = Ast2Dot::toString(begins_term->subject_term);
  const std::string right_expr = Ast2Dot::toString(begins_term->search_term);

  std::stringstream ss;
  ss << *begins_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(begins_term);
}

void FormulaOptimizer::visitNotBegins(NotBegins_ptr not_begins_term) {
  const std::string left_expr = Ast2Dot::toString(not_begins_term->subject_term);
  const std::string right_expr = Ast2Dot::toString(not_begins_term->search_term);

  std::stringstream ss;
  ss << *not_begins_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(not_begins_term);
}

void FormulaOptimizer::visitEnds(Ends_ptr ends_term) {
  const std::string left_expr = Ast2Dot::toString(ends_term->subject_term);
  const std::string right_expr = Ast2Dot::toString(ends_term->search_term);

  std::stringstream ss;
  ss << *ends_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(ends_term);
}

void FormulaOptimizer::visitNotEnds(NotEnds_ptr not_ends_term) {
  const std::string left_expr = Ast2Dot::toString(not_ends_term->subject_term);
  const std::string right_expr = Ast2Dot::toString(not_ends_term->search_term);

  std::stringstream ss;
  ss << *not_ends_term << left_expr << right_expr;
  const std::string term_expr = ss.str();

  terms_[term_expr].push_back(not_ends_term);
}

} /* namespace Solver */
} /* namespace Vlab */
