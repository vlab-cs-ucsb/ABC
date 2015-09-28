/*
 * PreOrderTraversal.h
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_PREORDERTRAVERSAL_H_
#define SRC_SOLVER_PREORDERTRAVERSAL_H_

#include <functional>
#include <stack>

#include <glog/logging.h>
#include "smt/Visitable.h"
#include "smt/Visitor.h"
#include "smt/ast.h"

namespace Vlab {
namespace Solver {

class PreOrderTraversal : public SMT::Visitor {
public:
  PreOrderTraversal(SMT::Script_ptr script);
  virtual ~PreOrderTraversal();

  void setCommandCallback(std::function<bool (SMT::Command_ptr)> command_callback);
  void setTermCallback(std::function<bool (SMT::Term_ptr)> term_callback);

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

  void push(SMT::Term_ptr*);
  void pop();
  SMT::Term_ptr* top();
private:
  SMT::Script_ptr root;
  std::stack<SMT::Term_ptr*> parent_term_stack;
  std::function<bool (SMT::Command_ptr)> command_callback;
  std::function<bool (SMT::Term_ptr)> term_callback;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_PREORDERTRAVERSAL_H_ */
