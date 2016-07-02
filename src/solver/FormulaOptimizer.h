/*
 * FormulaOptimizer.h
 *
 *  Created on: May 12, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_FORMULAOPTIMIZER_H_
#define SRC_SOLVER_FORMULAOPTIMIZER_H_

#include <iostream>
#include <sstream>
#include <queue>
#include <vector>
#include <map>
#include <functional>

#include <glog/logging.h>
#include "smt/ast.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"
#include "AstTraverser.h"
#include "SyntacticOptimizer.h"

namespace Vlab {
namespace Solver {

class FormulaOptimizer: public AstTraverser {
public:
  FormulaOptimizer(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~FormulaOptimizer();
  void start();
  void end();

  void setCallbacks();
  void visitAssert(SMT::Assert_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;
  void visitEq(SMT::Eq_ptr) override;
  void visitNotEq(SMT::NotEq_ptr) override;
  void visitGt(SMT::Gt_ptr) override;
  void visitGe(SMT::Ge_ptr) override;
  void visitLt(SMT::Lt_ptr) override;
  void visitLe(SMT::Le_ptr) override;
  void visitIn(SMT::In_ptr) override;
  void visitNotIn(SMT::NotIn_ptr) override;
  void visitContains(SMT::Contains_ptr) override;
  void visitNotContains(SMT::NotContains_ptr) override;
  void visitBegins(SMT::Begins_ptr) override;
  void visitNotBegins(SMT::NotBegins_ptr) override;
  void visitEnds(SMT::Ends_ptr) override;
  void visitNotEnds(SMT::NotEnds_ptr) override;

protected:
  bool check_term(SMT::Term_ptr);
  void reset_sets();
  void visit_and_callback(SMT::Term_ptr&);

  SymbolTable_ptr symbol_table_;
  bool delete_term_;

  std::set<std::string> and_terms_;
  std::set<std::string> or_terms_;
  std::set<std::string> eq_terms_;
  std::set<std::string> not_eq_terms_;
  std::set<std::string> in_terms_;
  std::set<std::string> not_in_terms_;
  std::set<std::string> contains_terms_;
  std::set<std::string> not_contains_terms_;
  std::set<std::string> begins_terms_;
  std::set<std::string> not_begins_terms_;
  std::set<std::string> ends_terms_;
  std::set<std::string> not_ends_terms_;
  std::set<std::string> gt_terms_;
  std::set<std::string> ge_terms_;
  std::set<std::string> lt_terms_;
  std::set<std::string> le_terms_;

  std::function<void(SMT::Term_ptr&)> callback_;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_FORMULAOPTIMIZER_H_ */
