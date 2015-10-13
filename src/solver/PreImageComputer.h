/*
 * PreImageComputer.h
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#ifndef SOLVER_PREIMAGECOMPUTER_H_
#define SOLVER_PREIMAGECOMPUTER_H_

#include <glog/logging.h>
#include "smt/ast.h"
#include "SymbolTable.h"
#include "Value.h"

namespace Vlab {
namespace Solver {

class PreImageComputer: public SMT::Visitor {
  typedef std::map<SMT::Term_ptr, Value_ptr> TermValueMap;
  typedef std::map<SMT::Variable_ptr, std::vector<SMT::Term_ptr>> VariablePathTable;
public:
  PreImageComputer(SymbolTable_ptr, VariablePathTable& variable_path_table, const TermValueMap& post_images );
  virtual ~PreImageComputer();

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
protected:
  Value_ptr getTermPostImage(SMT::Term_ptr term);
  Value_ptr getTermPreImage(SMT::Term_ptr term);
  bool setTermPreImage(SMT::Term_ptr term, Value_ptr value);
  void popTerm(SMT::Term_ptr);

  SymbolTable_ptr symbol_table;
  VariablePathTable& variable_path_table;
  const TermValueMap& post_images;
  TermValueMap pre_images;
  std::vector<SMT::Term_ptr> current_path;


private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_PREIMAGECOMPUTER_H_ */
