/*
 * ImplicationRunner.h
 *
 *  Created on: July 3, 2015
 *      Author: baki, tegan
 */

#ifndef SOLVER_ImplicationRunner_H_
#define SOLVER_ImplicationRunner_H_

#include <map>
#include <set>
#include <vector>
#include <cstdbool>
#include <iostream>
#include <iterator>
#include <string>
#include <utility>

#include <glog/logging.h>
#include <glog/vlog_is_on.h>

#include "../smt/typedefs.h"
#include "../smt/ast.h"
#include "../smt/Visitor.h"
#include "../utils/List.h"
#include "AstTraverser.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {
class ImplicationRunner : public AstTraverser {
 public:
  ImplicationRunner(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~ImplicationRunner();
  void start() override;
  void end() override;
  void setCallbacks();

  void visitAssert(SMT::Assert_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;

  void visitEq(SMT::Eq_ptr) override;
  void visitContains(SMT::Contains_ptr) override;
  void visitNotContains(SMT::NotContains_ptr) override;
  void visitEnds(SMT::Ends_ptr) override;
  void visitNotEnds(SMT::NotEnds_ptr) override;


 protected:
  SymbolTable_ptr symbol_table_;
  SMT::And_ptr current_and_;

  bool is_precise(SMT::Concat_ptr);
  SMT::Term_ptr get_length(SMT::Term_ptr);
  SMT::TermConstant_ptr get_length_constant(SMT::TermConstant_ptr);
  SMT::Plus_ptr get_length_concat(SMT::Concat_ptr);


 private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_ImplicationRunner_H_ */
