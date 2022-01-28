/*
 * RegexDivideConquer.h
 *
 *  Created on: July 14, 2021
 *      Author: Will
 */

#ifndef SOLVER_REGEXDIVIDECONQUER_H_
#define SOLVER_REGEXDIVIDECONQUER_H_



#include <glog/logging.h>

#include <regex>
#include <tuple>

#include "../smt/ast.h"
#include "../smt/typedefs.h"
#include "../smt/Visitor.h"
#include "../utils/RegularExpression.h"
#include "Ast2Dot.h"
#include "AstTraverser.h"
#include "SymbolTable.h"
#include "SyntacticOptimizer.h"
#include "SyntacticProcessor.h"
#include "RegexDivideConquerTransformer.h"

namespace Vlab {
namespace Solver {

// TODO There may be a bug when we try to add multiple callbacks in one visit
// check that behaviour especially for relational operations and
// 'not' operation (add more optimization for not)
class RegexDivideConquer: public AstTraverser {
public:
  RegexDivideConquer(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~RegexDivideConquer();

  void start() override;
  void end() override;

  void setCallbacks();
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;
  void visitEq(SMT::Eq_ptr) override;
  void visitNotEq(SMT::NotEq_ptr) override;
  void visitIn(SMT::In_ptr) override;
  void visitNotIn(SMT::NotIn_ptr) override;

  std::string get_computed_prefix();
  
protected:
  void visit_and_callback(SMT::Term_ptr&);

  std::vector<SMT::Term_ptr> analyze_regexes();

  void shorten_prefixes();


  SymbolTable_ptr symbol_table_;
  std::function<void(SMT::Term_ptr&)> callback_;

  std::vector<SMT::Term_ptr> in_term_regexes_;
  std::map<SMT::Term_ptr,SMT::Visitable_ptr> in_term_parent_scope_; // either AND or term itself

  std::vector<SMT::Term_ptr> prefix_shorten_terms_;

  SMT::And_ptr and_term_;
  std::vector<SMT::Term_ptr> constraints_to_add;

private:
  std::string computed_prefix_;
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_REGEXDIVIDECONQUER_H_ */
