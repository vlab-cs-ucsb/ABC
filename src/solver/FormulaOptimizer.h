/*
 * FormulaOptimizer.h
 *
 *  Created on: May 12, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_FORMULAOPTIMIZER_H_
#define SRC_SOLVER_FORMULAOPTIMIZER_H_

#include <iterator>
#include <map>
#include <functional>
#include <set>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include <glog/logging.h>

#include "../smt/ast.h"
#include "../smt/typedefs.h"
#include "Ast2Dot.h"
#include "AstTraverser.h"
#include "SymbolTable.h"

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
  SymbolTable_ptr symbol_table_;
  bool delete_term_;
  std::map<std::string, bool> term_strs_;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_FORMULAOPTIMIZER_H_ */
