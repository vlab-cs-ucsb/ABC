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
  void visitAssert(SMT::Assert_ptr);
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);

protected:
  void push_scope(SMT::Visitable_ptr);
  SMT::Visitable_ptr pop_scope();
  void add_term_to_check_list(SMT::Term_ptr);
  void add_terms_to_check_list(SMT::TermList_ptr);
  bool check_term(SMT::Term_ptr);
  void visit_and_callback(SMT::Term_ptr&);
  bool is_equivalent(SMT::Term_ptr, SMT::Term_ptr);
  std::string to_string(SMT::Visitable_ptr);

  SymbolTable_ptr symbol_table;

  std::vector<SMT::Visitable_ptr> scope_stack;
  std::map<SMT::Visitable_ptr, std::vector<SMT::Term_ptr>> check_table;
  std::function<void(SMT::Term_ptr&)> callback;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_FORMULAOPTIMIZER_H_ */
