/*
 * SyntacticOptimizer.h
 *
 *  Created on: Apr 28, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYNTACTICOPTIMIZER_H_
#define SOLVER_SYNTACTICOPTIMIZER_H_

#include <algorithm>
#include <cctype>
#include <functional>
#include <initializer_list>
#include <iterator>
#include <sstream>
#include <string>
#include <vector>

#include <glog/logging.h>

#include "../smt/ast.h"
#include "../smt/typedefs.h"
#include "../smt/Visitor.h"
#include "../utils/RegularExpression.h"
#include "Ast2Dot.h"
#include "optimization/CharAtOptimization.h"
#include "optimization/ConstantTermChecker.h"
#include "optimization/ConstantTermOptimization.h"
#include "optimization/SubstringOptimization.h"
#include "SymbolTable.h"


namespace Vlab {
namespace Solver {

// TODO There may be a bug when we try to add multiple callbacks in one visit
// check that behaviour especially for relational operations and
// 'not' operation (add more optimization for not)
class SyntacticOptimizer: public SMT::Visitor {
public:
  SyntacticOptimizer(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~SyntacticOptimizer();

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
protected:
  void visit_and_callback(SMT::Term_ptr&);
  void append_constant(SMT::TermConstant_ptr, SMT::TermConstant_ptr);
  bool check_and_process_constant_string(std::initializer_list<SMT::Term_ptr> terms);
  bool check_and_process_len_transformation(SMT::Term_ptr, SMT::Term_ptr&, SMT::Term_ptr&);
  bool __check_and_process_len_transformation(SMT::Term::Type, SMT::Term_ptr&, SMT::Term_ptr&);
  SMT::Term::Type syntactic_reverse_relation(SMT::Term::Type operation);
  bool check_and_process_for_contains_transformation(SMT::Term_ptr&, SMT::Term_ptr&, int compare_value);
  SMT::SubString::Mode check_and_process_subString(SMT::SubString_ptr sub_string_term, SMT::Term_ptr &index_term);
  SMT::SubString::Mode check_and_process_subString(SMT::SubString_ptr sub_string_term, SMT::Term_ptr &start_index_term, SMT::Term_ptr &end_index_term );
  SMT::Let_ptr generateLetTermFor(SMT::SubString_ptr sub_string_term, SMT::SubString::Mode local_substring_mode, SMT::LastIndexOf_ptr last_index_of_term, SMT::Term_ptr &index_term);
  SMT::Let_ptr generateLetTermFor(SMT::SubString_ptr sub_string_term, SMT::SubString::Mode local_substring_mode, SMT::IndexOf_ptr index_of_term, SMT::Term_ptr &index_term);
  int check_and_process_index_operation(SMT::Term_ptr current_term, SMT::Term_ptr subject_term, SMT::Term_ptr &index_term);
  SMT::Let_ptr generateLetTermFor(SMT::IndexOf_ptr index_of_term, SMT::SubString::Mode local_substring_mode, SMT::IndexOf_ptr param_index_of_term, SMT::Term_ptr &index_term);
  SMT::Let_ptr generateLetTermFor(SMT::IndexOf_ptr index_of_term, SMT::SubString::Mode local_substring_mode, SMT::LastIndexOf_ptr param_last_index_of_term, SMT::Term_ptr &index_term);
  SMT::Let_ptr generateLetTermFor(SMT::LastIndexOf_ptr index_of_term, SMT::SubString::Mode local_substring_mode, SMT::IndexOf_ptr param_index_of_term, SMT::Term_ptr &index_term);
  SMT::Let_ptr generateLetTermFor(SMT::LastIndexOf_ptr index_of_term, SMT::SubString::Mode local_substring_mode, SMT::LastIndexOf_ptr param_last_index_of_term, SMT::Term_ptr &index_term);
  SMT::Term_ptr generate_term_constant(std::string data, SMT::Primitive::Type type);
  void add_callback_to_replace_with_bool(SMT::Term_ptr, bool value);
  bool check_bool_constant_value(SMT::Term_ptr, std::string value);
  SMT::Variable_ptr generate_local_var(SMT::Variable::Type type);
  SMT::QualIdentifier_ptr generate_qual_identifier(std::string var_name);
  bool match_prefix(SMT::Term_ptr, SMT::Term_ptr);
  bool match_suffix(SMT::Term_ptr, SMT::Term_ptr);

  void record_ite_relation(SMT::Term_ptr);

  SMT::Script_ptr root_;
  SymbolTable_ptr symbol_table_;
  std::function<void(SMT::Term_ptr&)> callback_;
  static unsigned name_counter;
private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYNTACTICOPTIMIZER_H_ */
