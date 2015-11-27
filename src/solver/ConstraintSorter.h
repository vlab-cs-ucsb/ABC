/*
 * ConstraintSorter.h
 *
 *  Created on: May 18, 2015
 *      Author: baki
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
