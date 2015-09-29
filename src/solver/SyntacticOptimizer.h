/*
 * SyntacticOptimizer.h
 *
 *  Created on: Apr 28, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYNTACTICOPTIMIZER_H_
#define SOLVER_SYNTACTICOPTIMIZER_H_

#include <iostream>
#include <sstream>
#include <queue>
#include <functional>

#include <glog/logging.h>
#include "smt/ast.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {

// TODO There may be a bug when we try to add multiple callbacks in one visit
// check that behaviour especially for relational operations and
// 'not' operation (add more optimizaiton for not)
class SyntacticOptimizer: public SMT::Visitor {
public:
  SyntacticOptimizer(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~SyntacticOptimizer();

  void start();
  void end();

  void visitScript(SMT::Script_ptr);
  void visitCommand(SMT::Command_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitTerm(SMT::Term_ptr);
  void visitExclamation(SMT::Exclamation_ptr);
  void visitExists(SMT::Exists_ptr);
  void visitForAll(SMT::ForAll_ptr);
  void visitLet(SMT::Let_ptr);
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void visitNot(SMT::Not_ptr);
  void visitUMinus(SMT::UMinus_ptr);
  void visitMinus(SMT::Minus_ptr);
  void visitPlus(SMT::Plus_ptr);
  void visitEq(SMT::Eq_ptr);
  void visitNotEq(SMT::NotEq_ptr);
  void visitGt(SMT::Gt_ptr);
  void visitGe(SMT::Ge_ptr);
  void visitLt(SMT::Lt_ptr);
  void visitLe(SMT::Le_ptr);
  void visitConcat(SMT::Concat_ptr);
  void visitIn(SMT::In_ptr);
  void visitNotIn(SMT::NotIn_ptr);
  void visitLen(SMT::Len_ptr);
  void visitContains(SMT::Contains_ptr);
  void visitNotContains(SMT::NotContains_ptr);
  void visitBegins(SMT::Begins_ptr);
  void visitNotBegins(SMT::NotBegins_ptr);
  void visitEnds(SMT::Ends_ptr);
  void visitNotEnds(SMT::NotEnds_ptr);
  void visitIndexOf(SMT::IndexOf_ptr);
  void visitLastIndexOf(SMT::LastIndexOf_ptr);
  void visitCharAt(SMT::CharAt_ptr);
  void visitSubString(SMT::SubString_ptr);
  void visitToUpper(SMT::ToUpper_ptr);
  void visitToLower(SMT::ToLower_ptr);
  void visitTrim(SMT::Trim_ptr);
  void visitReplace(SMT::Replace_ptr);
  void visitCount(SMT::Count_ptr);
  void visitIte(SMT::Ite_ptr);
  void visitReConcat(SMT::ReConcat_ptr);
  void visitToRegex(SMT::ToRegex_ptr);
  void visitUnknownTerm(SMT::Unknown_ptr);
  void visitAsQualIdentifier(SMT::AsQualIdentifier_ptr);
  void visitQualIdentifier(SMT::QualIdentifier_ptr);
  void visitTermConstant(SMT::TermConstant_ptr);
  void visitSort(SMT::Sort_ptr);
  void visitTVariable(SMT::TVariable_ptr);
  void visitTBool(SMT::TBool_ptr);
  void visitTInt(SMT::TInt_ptr);
  void visitTString(SMT::TString_ptr);
  void visitAttribute(SMT::Attribute_ptr);
  void visitSortedVar(SMT::SortedVar_ptr);
  void visitVarBinding(SMT::VarBinding_ptr);
  void visitIdentifier(SMT::Identifier_ptr);
  void visitPrimitive(SMT::Primitive_ptr);
  void visitVariable(SMT::Variable_ptr);
protected:
  void visit_and_callback(SMT::Term_ptr&);
  bool is_equivalent(SMT::Term_ptr, SMT::Term_ptr);
  std::string to_string(SMT::Visitable_ptr);
  std::string escape_regex(std::string regex);
  std::string regex_to_str(std::string regex);
  void pre_concat_constants(SMT::TermConstant_ptr, SMT::TermConstant_ptr);
  bool check_and_process_in_transformation(SMT::Term_ptr, bool is_complement);
  // TODO check len transformation later when pres. arith. added.
  bool check_and_process_len_transformation(SMT::Term_ptr, SMT::Term_ptr&, SMT::Term_ptr&);
  bool __check_and_process_len_transformation(std::string operation, SMT::Term_ptr&, SMT::Term_ptr&);
  std::string syntactic_reverse_relation(std::string operation);
  SMT::Term_ptr generate_term_constant(std::string data, SMT::Primitive::Type type);
  SMT::Term_ptr generate_dummy_term();
  void add_callback_to_replace_with_bool(SMT::Term_ptr, std::string value);
  bool check_bool_constant_value(SMT::Term_ptr, std::string value);

  SMT::Script_ptr root;
  SymbolTable_ptr symbol_table;
  SMT::Assert_ptr current_assert;
  std::queue<std::function<void(SMT::Term_ptr&)>> callbacks;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYNTACTICOPTIMIZER_H_ */
