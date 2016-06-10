/*
 * Created by will on 3/4/16.
 * Currently, generates mapping between variables and
 * their respective tracks
 * Later, will serve as "phase 1", tracking relations only when needed,
 * and serving to eliminate as much work as possible, while still providing
 * relational analysis
 */

#ifndef SRC_STRINGRELATIONGENERATOR_H
#define SRC_STRINGRELATIONGENERATOR_H

#include <cstdbool>
#include <map>

#include "smt/ast.h"
#include "theory/StringRelation.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {

class StringRelationGenerator : public SMT::Visitor {

 public:
  StringRelationGenerator(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~StringRelationGenerator();

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
  void visitUMinus(SMT::UMinus_ptr);
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
  void visitReUnion(SMT::ReUnion_ptr) override;
  void visitReInter(SMT::ReInter_ptr) override;
  void visitReStar(SMT::ReStar_ptr) override;
  void visitRePlus(SMT::RePlus_ptr) override;
  void visitReOpt(SMT::ReOpt_ptr) override;
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

  Theory::StringRelation_ptr get_term_relation(SMT::Term_ptr term);bool set_term_relation(
      SMT::Term_ptr term, Theory::StringRelation_ptr str_rel);
  void delete_term_relation(SMT::Term_ptr term);
  SMT::Term_ptr get_parent_term(SMT::Variable_ptr variable);bool set_parent_term(SMT::Variable_ptr variable,
                                                                                 SMT::Term_ptr term);
 protected:

  SMT::Script_ptr root;
  SymbolTable_ptr symbol_table;
  std::map<SMT::Term_ptr, Theory::StringRelation_ptr> relations;
  // for interplay between single/multitrack
  std::map<SMT::Variable_ptr, SMT::Term_ptr> variable_term_map;
 private:
  SMT::Term_ptr current_term;
  static const int VLOG_LEVEL;

};

} /* namespace Solver */
} /* namespace Vlab */

#endif //SRC_STRINGRELATIONGENERATOR_H
