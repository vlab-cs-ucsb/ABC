/*
 * ConstraintSorter.h
 *
 *  Created on: May 18, 2015
 *      Author: baki, will
 */

#ifndef SOLVER_CONSTRAINTSORTER_H_
#define SOLVER_CONSTRAINTSORTER_H_

#include <iostream>
#include <sstream>
#include <vector>
#include <queue>
#include <stack>
#include <map>
#include <algorithm>

#include <glog/logging.h>
#include "smt/ast.h"
#include "SymbolTable.h"
#include "Counter.h"

namespace Vlab {
namespace Solver {
// TODO fix sorting algorithm based on latest updates
class ConstraintSorter: public SMT::Visitor {
public:
  ConstraintSorter(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~ConstraintSorter();
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
  void visitIsDigit(SMT::IsDigit_ptr) override {};
  void visitToCode(SMT::ToCode_ptr) override {};
  void visitFromCode(SMT::FromCode_ptr) override {};
  void visitReConcat(SMT::ReConcat_ptr) override;
  void visitReUnion(SMT::ReUnion_ptr) override;
  void visitReInter(SMT::ReInter_ptr) override;
  void visitReStar(SMT::ReStar_ptr) override;
  void visitRePlus(SMT::RePlus_ptr) override;
  void visitReOpt(SMT::ReOpt_ptr) override;
  void visitReLoop(SMT::ReLoop_ptr) override;
  void visitReComp(SMT::ReComp_ptr) override {};
  void visitReDiff(SMT::ReDiff_ptr) override {};
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
  class VariableNode;
  class TermNode;
  typedef VariableNode* VariableNode_ptr;
  typedef TermNode* TermNode_ptr;

  VariableNode_ptr get_variable_node(SMT::Variable_ptr);
  TermNode_ptr process_child_nodes(TermNode_ptr, TermNode_ptr);
  void sort_terms(std::vector<TermNode_ptr>& term_list);

  SMT::Script_ptr root;
  SymbolTable_ptr symbol_table;
  TermNode_ptr term_node;

  std::vector<TermNode_ptr> dependency_node_list;
  std::map<SMT::Variable_ptr, VariableNode_ptr> variable_nodes;

  class TermNode {
  public:
    TermNode();
    TermNode(SMT::Term_ptr node);
    ~TermNode();
    std::string str();

    void setNode(SMT::Term_ptr node);
    SMT::Term_ptr getNode();
    void addVariableNode(VariableNode_ptr variable, bool is_left_side);
    void addVariableNodes(std::vector<VariableNode_ptr>&, bool is_left_side);
    std::vector<VariableNode_ptr>& getLeftNodes();
    std::vector<VariableNode_ptr>& getRightNodes();
    std::vector<VariableNode_ptr>& getAllNodes();
    void shiftToLeft();
    void shiftToRight();
    void addMeToChildVariableNodes();
    int numOfTotalVars();
    int numOfLeftVars();
    int numOfRightVars();
    void updateSymbolicVariableInfo();
    bool hasSymbolicVarOnLeft();
    bool hasSymbolicVarOnRight();
    bool hasSymbolicVar();

    static std::string count_var;
  protected:
    SMT::Term_ptr _node;
    bool _has_symbolic_var_on_left;
    bool _has_symbolic_var_on_right;
    std::vector<SMT::Term_ptr> _next_node_list;
    std::vector<VariableNode_ptr> _all_child_node_list;
    std::vector<VariableNode_ptr> _left_child_node_list;
    std::vector<VariableNode_ptr> _right_child_node_list;
  private:
    void merge_vectors(std::vector<VariableNode_ptr>&, std::vector<VariableNode_ptr>&);
  };

  class VariableNode {
  public:
    VariableNode(SMT::Variable_ptr variable);
    ~VariableNode();
    std::string str();

    SMT::Variable_ptr getVariable();
    void addTermNode(TermNode_ptr node, bool is_left_side);
  protected:
    SMT::Variable_ptr variable;
    std::vector<TermNode_ptr> all_var_appearance_list;
    std::vector<TermNode_ptr> left_side_var_appearance_list;
    std::vector<TermNode_ptr> right_side_var_appearance_list;
  };

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_CONSTRAINTSORTER_H_ */
