/*
 * StringFormulaGenerator.h
 *
 *  Created on: Jan 22, 2017
 *      Author: baki
 */

#ifndef SRC_SOLVER_STRINGFORMULAGENERATOR_H_
#define SRC_SOLVER_STRINGFORMULAGENERATOR_H_

#include <map>
#include <iostream>
#include <string>
#include <utility>
#include <vector>

#include <glog/logging.h>

#include "../smt/ast.h"
#include "../smt/typedefs.h"
#include "../smt/Visitor.h"
#include "../theory/StringFormula.h"
#include "../theory/Formula.h"
#include "../theory/StringAutomaton.h"
#include "ConstraintInformation.h"
#include "options/Solver.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {

using VariableGroupMap = std::map<std::string,std::string>;
using VariableGroupTable = std::map<SMT::Term_ptr,VariableGroupMap>;

class StringFormulaGenerator: public SMT::Visitor {
 public:
  StringFormulaGenerator(SMT::Script_ptr, SymbolTable_ptr, ConstraintInformation_ptr);
  virtual ~StringFormulaGenerator();

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
  void visitDiv(SMT::Div_ptr) override;
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

  Theory::StringFormula_ptr get_term_formula(SMT::Term_ptr term);
  Theory::StringFormula_ptr get_group_formula(std::string group_name);
  bool has_integer_terms(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::TermList> get_integer_terms_map();
  SMT::TermList& get_integer_terms_in(SMT::Term_ptr term);
  void clear_term_formula(SMT::Term_ptr term);
  void clear_term_formulas();

  std::string get_term_group_name(SMT::Term_ptr term);
  std::string get_variable_group_name(SMT::Variable_ptr variable);
  std::set<std::string> get_group_subgroups(std::string group_name);

protected:
  void add_string_variables(std::string group_name, SMT::Term_ptr term);
  std::string generate_group_name(SMT::Term_ptr term, std::string var_name);

  bool set_term_formula(SMT::Term_ptr term, Theory::StringFormula_ptr formula);
  void delete_term_formula(SMT::Term_ptr);
  void set_group_mappings();

  SMT::Script_ptr root_;
  SymbolTable_ptr symbol_table_;
  ConstraintInformation_ptr constraint_information_;
  bool has_mixed_constraint_;
  std::string current_group_;

  std::map<SMT::Term_ptr, Theory::StringFormula_ptr> term_formula_;

  /**
   * TODO instead of keeping that maps, add a pre-processing step
   * to have a auxiliary variable for mixed terms
   */
  SMT::TermList integer_terms_;
  std::map<SMT::Term_ptr, SMT::TermList> integer_terms_map_;

  std::map<std::string,std::set<std::string>> subgroups_;
  std::map<std::string,std::string> variable_group_map_;
  std::map<SMT::Term_ptr, std::string> term_group_map_;
  std::map<std::string, Theory::StringFormula_ptr> group_formula_;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_STRINGFORMULAGENERATOR_H_ */
