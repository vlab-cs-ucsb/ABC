/*
 * Visitor.h
 *
 *  Created on: Apr 9, 2015
 *      Author: baki
 */

#ifndef SMT_VISITOR_H_
#define SMT_VISITOR_H_

#include <vector>

#include "typedefs.h"

namespace Vlab {
namespace SMT {

class Visitor {
public:
  virtual ~Visitor() {
  }
  virtual void start() = 0;
  virtual void end() = 0;
  virtual void visitScript(Script_ptr) = 0;
  virtual void visitCommand(Command_ptr) = 0;
  virtual void visitTerm(Term_ptr) = 0;
  virtual void visitExclamation(Exclamation_ptr) = 0;
  virtual void visitExists(Exists_ptr) = 0;
  virtual void visitForAll(ForAll_ptr) = 0;
  virtual void visitLet(Let_ptr) = 0;
  virtual void visitAnd(And_ptr) = 0;
  virtual void visitOr(Or_ptr) = 0;
  virtual void visitNot(Not_ptr) = 0;
  virtual void visitUMinus(UMinus_ptr) = 0;
  virtual void visitMinus(Minus_ptr) = 0;
  virtual void visitPlus(Plus_ptr) = 0;
  virtual void visitEq(Eq_ptr) = 0;
  virtual void visitNotEq(NotEq_ptr) = 0;
  virtual void visitGt(Gt_ptr) = 0;
  virtual void visitGe(Ge_ptr) = 0;
  virtual void visitLt(Lt_ptr) = 0;
  virtual void visitLe(Le_ptr) = 0;
  virtual void visitConcat(Concat_ptr) = 0;
  virtual void visitIn(In_ptr) = 0;
  virtual void visitNotIn(NotIn_ptr) = 0;
  virtual void visitLen(Len_ptr) = 0;
  virtual void visitContains(Contains_ptr) = 0;
  virtual void visitNotContains(NotContains_ptr) = 0;
  virtual void visitBegins(Begins_ptr) = 0;
  virtual void visitNotBegins(NotBegins_ptr) = 0;
  virtual void visitEnds(Ends_ptr) = 0;
  virtual void visitNotEnds(NotEnds_ptr) = 0;
  virtual void visitIndexOf(IndexOf_ptr) = 0;
  virtual void visitLastIndexOf(LastIndexOf_ptr) = 0;
  virtual void visitCharAt(CharAt_ptr) = 0;
  virtual void visitSubString(SubString_ptr) = 0;
  virtual void visitToUpper(ToUpper_ptr) = 0;
  virtual void visitToLower(ToLower_ptr) = 0;
  virtual void visitTrim(Trim_ptr) = 0;
  virtual void visitReplace(Replace_ptr) = 0;
  virtual void visitCount(Count_ptr) = 0;
  virtual void visitIte(Ite_ptr) = 0;
  virtual void visitReConcat(ReConcat_ptr) = 0;
  virtual void visitToRegex(ToRegex_ptr) = 0;
  virtual void visitUnknownTerm(Unknown_ptr) = 0;
  virtual void visitAsQualIdentifier(AsQualIdentifier_ptr) = 0;
  virtual void visitQualIdentifier(QualIdentifier_ptr) = 0;
  virtual void visitTermConstant(TermConstant_ptr) = 0;
  virtual void visitSort(Sort_ptr) = 0;
  virtual void visitTVariable(TVariable_ptr) = 0;
  virtual void visitTBool(TBool_ptr) = 0;
  virtual void visitTInt(TInt_ptr) = 0;
  virtual void visitTString(TString_ptr) = 0;
  virtual void visitAttribute(Attribute_ptr) = 0;
  virtual void visitSortedVar(SortedVar_ptr) = 0;
  virtual void visitVarBinding(VarBinding_ptr) = 0;
  virtual void visitIdentifier(Identifier_ptr) = 0;
  virtual void visitPrimitive(Primitive_ptr) = 0;
  virtual void visitVariable(Variable_ptr) = 0;

  void visit(Visitable_ptr p) {
    if (p == nullptr)
      return;
    p->accept(this);
  }

  void visit_children_of(Visitable_ptr p) {
    p->visit_children(this);
  }

  template<class T>
  void visit_list(std::vector<T*> *v) {
    if (v == nullptr)
      return;
    for (auto& el : *v) {
      visit(el);
    }
  }

};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SMT_VISITOR_H_ */
