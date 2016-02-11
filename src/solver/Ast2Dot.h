/*
 * Ast2Dot.h
 *
 *  Created on: Nov 23, 2014
 *      Author: baki
 */

#ifndef SOLVER_AST2DOT_H_
#define SOLVER_AST2DOT_H_

#include <iostream>
#include <stack>
#include <fstream>
#include <sstream>
#include <string>

#include <glog/logging.h>
#include "smt/ast.h"

namespace Vlab {
namespace Solver {

class Ast2Dot: public SMT::Visitor {
public:
  Ast2Dot(std::ostream* out = &std::cout);
  ~Ast2Dot();

  void add_edge(u_int64_t p, u_int64_t c);
  void add_node(u_int64_t c, std::string label);
  void draw(std::string label, SMT::Visitable_ptr p);
  void draw_terminal(std::string label);

  void start(SMT::Visitable_ptr);
  void start() override;
  void end() override;
  void visitScript(SMT::Script_ptr) override;
  void visitCommand(SMT::Command_ptr) override;
  void visitAssert(SMT::Assert_ptr) override;
  void visitTerm(SMT::Term_ptr) override;
  void visitExclamation(SMT::Exclamation_ptr) override;
  void visitExists(SMT::Exists_ptr) override;
  void visitForAll(SMT::ForAll_ptr) override;
  void visitLet(SMT::Let_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;
  void visitNot(SMT::Not_ptr) override;
  void visitUMinus(SMT::UMinus_ptr) override;
  void visitMinus(SMT::Minus_ptr) override;
  void visitPlus(SMT::Plus_ptr) override;
  void visitTimes(SMT::Times_ptr) override;
  void visitEq(SMT::Eq_ptr) override;
  void visitNotEq(SMT::NotEq_ptr) override;
  void visitGt(SMT::Gt_ptr) override;
  void visitGe(SMT::Ge_ptr) override;
  void visitLt(SMT::Lt_ptr) override;
  void visitLe(SMT::Le_ptr) override;
  void visitConcat(SMT::Concat_ptr) override;
  void visitIn(SMT::In_ptr) override;
  void visitNotIn(SMT::NotIn_ptr) override;
  void visitLen(SMT::Len_ptr) override;
  void visitContains(SMT::Contains_ptr) override;
  void visitNotContains(SMT::NotContains_ptr) override;
  void visitBegins(SMT::Begins_ptr) override;
  void visitNotBegins(SMT::NotBegins_ptr) override;
  void visitEnds(SMT::Ends_ptr) override;
  void visitNotEnds(SMT::NotEnds_ptr) override;
  void visitIndexOf(SMT::IndexOf_ptr) override;
  void visitLastIndexOf(SMT::LastIndexOf_ptr) override;
  void visitCharAt(SMT::CharAt_ptr) override;
  void visitSubString(SMT::SubString_ptr) override;
  void visitToUpper(SMT::ToUpper_ptr) override;
  void visitToLower(SMT::ToLower_ptr) override;
  void visitTrim(SMT::Trim_ptr) override;
  void visitToString(SMT::ToString_ptr) override;
  void visitToInt(SMT::ToInt_ptr) override;
  void visitReplace(SMT::Replace_ptr) override;
  void visitCount(SMT::Count_ptr) override;
  void visitIte(SMT::Ite_ptr) override;
  void visitReConcat(SMT::ReConcat_ptr) override;
  void visitToRegex(SMT::ToRegex_ptr) override;
  void visitUnknownTerm(SMT::Unknown_ptr) override;
  void visitAsQualIdentifier(SMT::AsQualIdentifier_ptr) override;
  void visitQualIdentifier(SMT::QualIdentifier_ptr) override;
  void visitTermConstant(SMT::TermConstant_ptr) override;
  void visitSort(SMT::Sort_ptr) override;
  void visitTVariable(SMT::TVariable_ptr) override;
  void visitTBool(SMT::TBool_ptr) override;
  void visitTInt(SMT::TInt_ptr) override;
  void visitTString(SMT::TString_ptr) override;
  void visitAttribute(SMT::Attribute_ptr) override;
  void visitSortedVar(SMT::SortedVar_ptr) override;
  void visitVarBinding(SMT::VarBinding_ptr) override;
  void visitIdentifier(SMT::Identifier_ptr) override;
  void visitPrimitive(SMT::Primitive_ptr) override;
  void visitVariable(SMT::Variable_ptr) override;

  int inspectAST(SMT::Visitable_ptr node);
  static std::string toString(SMT::Visitable_ptr node);
  static bool isEquivalent(SMT::Visitable_ptr x, SMT::Visitable_ptr y);

private:
  std::ostream* m_out; //file for writting output
  u_int64_t count; //used to give each node a uniq id
  std::stack<u_int64_t> s; //stack for tracking parent/child pairs
  static int name_counter;

};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_AST2DOT_H_ */
