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
  void visitTimes(SMT::Times_ptr);
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
  void visitSubStringFirstOf(SMT::SubStringFirstOf_ptr);
  void visitSubStringLastOf(SMT::SubStringLastOf_ptr);
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

  int inspectAST(SMT::Visitable_ptr node);
  std::string toString(SMT::Visitable_ptr node);
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
