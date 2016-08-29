/*
 * ConstraintSorter.cpp
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#include "ConstraintSorter.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int ConstraintSorter::VLOG_LEVEL = 13;

ConstraintSorter::ConstraintSorter(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table), term_node(nullptr) {
}

ConstraintSorter::~ConstraintSorter() {
  for(auto it = variable_nodes.cbegin(); it != variable_nodes.cend(); it++) {
    delete variable_nodes[it->first];
    variable_nodes[it->first] = nullptr;
  }
  if(term_node != nullptr) {
    delete term_node;
    term_node = nullptr;
  }
}

void ConstraintSorter::start() {
  Counter counter(root, symbol_table);
  counter.start();

  symbol_table->push_scope(root);
  visit(root);
  symbol_table->pop_scope();

  end();
}

void ConstraintSorter::end() {

//  if (VLOG_IS_ON(VLOG_LEVEL)) {
//    DVLOG(VLOG_LEVEL) << "global dependency info: " << root;
//    for (auto& node : dependency_node_list) {
//      DVLOG(VLOG_LEVEL) << node->str();
//    }
//
//    for (auto& node : variable_nodes) {
//      DVLOG(VLOG_LEVEL) << node.second->str();
//    }
//  }
}

void ConstraintSorter::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void ConstraintSorter::visitCommand(Command_ptr command) {
}

void ConstraintSorter::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void ConstraintSorter::visitTerm(Term_ptr term) {
}

void ConstraintSorter::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ConstraintSorter::visitExists(Exists_ptr exists_term) {
}

void ConstraintSorter::visitForAll(ForAll_ptr for_all_term) {
}

void ConstraintSorter::visitLet(Let_ptr let_term) {
  TermNode_ptr binding_node = nullptr;
  for (auto& term : *(let_term->var_binding_list)) {
    term_node = nullptr;
    visit(term);
    if (binding_node == nullptr and term_node != nullptr) {
      binding_node = term_node;
      binding_node->shiftToRight();
    } else if (term_node != nullptr) {
      binding_node->addVariableNodes(term_node->getAllNodes(), false);
    }
  }
  term_node = nullptr;
  visit(let_term->term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(binding_node, right_node);
}

void ConstraintSorter::visitAnd(And_ptr and_term) {
  std::vector<TermNode_ptr> local_dependency_node_list;
  for (auto& term : *(and_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (term_node == nullptr) {
      term_node = new TermNode(term);
    } else {
      term_node->setNode(term);
    }
    term_node->addMeToChildVariableNodes();
    term_node->updateSymbolicVariableInfo();
    local_dependency_node_list.push_back(term_node);
  }
  term_node = nullptr;

  sort_terms(local_dependency_node_list);

  if (VLOG_IS_ON(VLOG_LEVEL)) {
    for (auto& node : local_dependency_node_list) {
      DVLOG(VLOG_LEVEL) << node->str();
    }

    for (auto& node : variable_nodes) {
      DVLOG(VLOG_LEVEL) << node.second->str();
    }
  }

  and_term->term_list->clear();
  for(auto it = local_dependency_node_list.cbegin(); it != local_dependency_node_list.cend(); it++) {
    and_term->term_list->push_back((*it)->getNode());
    delete *it;
  }
}

void ConstraintSorter::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void ConstraintSorter::visitNot(Not_ptr not_term) {
  term_node = nullptr;
  visit_children_of(not_term);
}

void ConstraintSorter::visitUMinus(UMinus_ptr u_minus_term) {
  term_node = nullptr;
  visit_children_of(u_minus_term);
}

void ConstraintSorter::visitMinus(Minus_ptr minus_term) {
  term_node = nullptr;
  visit(minus_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(minus_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitPlus(Plus_ptr plus_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(plus_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
      delete term_node;
    }
  }
  term_node = result_node;
}

void ConstraintSorter::visitTimes(Times_ptr times_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(times_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
      delete term_node;
    }
  }
  term_node = result_node;
}

void ConstraintSorter::visitEq(Eq_ptr eq_term) {
  term_node = nullptr;
  visit(eq_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(eq_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotEq(NotEq_ptr not_eq_term) {
  term_node = nullptr;
  visit(not_eq_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_eq_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}


void ConstraintSorter::visitGt(Gt_ptr gt_term) {
  term_node = nullptr;
  visit(gt_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(gt_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitGe(Ge_ptr ge_term) {
  term_node = nullptr;
  visit(ge_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(ge_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLt(Lt_ptr lt_term) {
  term_node = nullptr;
  visit(lt_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(lt_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLe(Le_ptr le_term) {
  term_node = nullptr;
  visit(le_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(le_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitConcat(Concat_ptr concat_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(concat_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
      delete term_node;
    }
  }
  term_node = result_node;
}

void ConstraintSorter::visitIn(In_ptr in_term) {
  term_node = nullptr;
  visit(in_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(in_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}


void ConstraintSorter::visitNotIn(NotIn_ptr not_in_term) {
  term_node = nullptr;
  visit(not_in_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_in_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLen(Len_ptr len_term) {
  term_node = nullptr;
  visit_children_of(len_term);
  if (term_node != nullptr) {
    term_node->shiftToRight();
  }
}

void ConstraintSorter::visitContains(Contains_ptr contains_term) {
  term_node = nullptr;
  visit(contains_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(contains_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotContains(NotContains_ptr not_contains_term) {
  term_node = nullptr;
  visit(not_contains_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_contains_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitBegins(Begins_ptr begins_term) {
  term_node = nullptr;
  visit(begins_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(begins_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotBegins(NotBegins_ptr not_begins_term) {
  term_node = nullptr;
  visit(not_begins_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_begins_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitEnds(Ends_ptr ends_term) {
  term_node = nullptr;
  visit(ends_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(ends_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotEnds(NotEnds_ptr not_ends_term) {
  term_node = nullptr;
  visit(not_ends_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_ends_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitIndexOf(IndexOf_ptr index_of_term) {
  term_node = nullptr;
  visit(index_of_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(index_of_term->search_term);
  TermNode_ptr right_node = term_node;
  if (index_of_term->from_index) {
    term_node = nullptr;
    visit(index_of_term->from_index);
    TermNode_ptr right_node_1 = right_node;
    TermNode_ptr right_node_2 = term_node;
    right_node = process_child_nodes(right_node_1, right_node_2);
    if (right_node != nullptr) {
      right_node->shiftToRight();
    }
  }
  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  term_node = nullptr;
  visit(last_index_of_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(last_index_of_term->search_term);
  TermNode_ptr right_node = term_node;
  if (last_index_of_term->from_index) {
    term_node = nullptr;
    visit(last_index_of_term->from_index);
    TermNode_ptr right_node_1 = right_node;
    TermNode_ptr right_node_2 = term_node;
    right_node = process_child_nodes(right_node_1, right_node_2);
    if (right_node != nullptr) {
      right_node->shiftToRight();
    }
  }

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitCharAt(CharAt_ptr char_at_term) {
  term_node = nullptr;
  visit(char_at_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(char_at_term->index_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitSubString(SubString_ptr sub_string_term) {
  term_node = nullptr;
  visit(sub_string_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(sub_string_term->start_index_term);
  TermNode_ptr right_node = term_node;
  if (sub_string_term->end_index_term) {
    term_node = nullptr;
    visit(sub_string_term->end_index_term);
    TermNode_ptr right_node_1 = right_node;
    TermNode_ptr right_node_2 = term_node;
    right_node = process_child_nodes(right_node_1, right_node_2);
    if (right_node != nullptr) {
      right_node->shiftToRight();
    }
  }

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitToUpper(ToUpper_ptr to_upper_term) {
  term_node = nullptr;
  visit_children_of(to_upper_term);
}

void ConstraintSorter::visitToLower(ToLower_ptr to_lower_term) {
  term_node = nullptr;
  visit_children_of(to_lower_term);
}

void ConstraintSorter::visitTrim(Trim_ptr trim_term) {
  term_node = nullptr;
  visit_children_of(trim_term);
}

void ConstraintSorter::visitToString(ToString_ptr to_string_term) {
  term_node = nullptr;
  visit_children_of(to_string_term);
}

void ConstraintSorter::visitToInt(ToInt_ptr to_int_term) {
  term_node = nullptr;
  visit_children_of(to_int_term);
}

void ConstraintSorter::visitReplace(Replace_ptr replace_term) {
  term_node = nullptr;
  visit(replace_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(replace_term->search_term);
  TermNode_ptr right_node_1 = term_node;
  term_node = nullptr;
  visit(replace_term->replace_term);
  TermNode_ptr right_node_2 = term_node;

  TermNode_ptr right_node = process_child_nodes(right_node_1, right_node_2);
  if (right_node != nullptr) {
    right_node->shiftToRight();
  }
  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitCount(Count_ptr count_term) {
  term_node = nullptr;
  visit(count_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(count_term->bound_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitIte(Ite_ptr ite_term) {
}

void ConstraintSorter::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstraintSorter::visitReUnion(ReUnion_ptr re_union_term) {
}

void ConstraintSorter::visitReInter(ReInter_ptr re_inter_term) {
}

void ConstraintSorter::visitReStar(ReStar_ptr re_star_term) {
}

void ConstraintSorter::visitRePlus(RePlus_ptr re_plus_term) {
}

void ConstraintSorter::visitReOpt(ReOpt_ptr re_opt_term) {
}

void ConstraintSorter::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstraintSorter::visitUnknownTerm(Unknown_ptr unknown_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(unknown_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
    }
  }
  term_node = result_node;
}

void ConstraintSorter::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ConstraintSorter::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  if (not variable->isLocalLetVar()) {
    VariableNode_ptr variable_node = get_variable_node(variable);
    term_node = new TermNode();
    term_node->addVariableNode(variable_node, false);
  }
}

void ConstraintSorter::visitTermConstant(TermConstant_ptr term_constant) {
}

void ConstraintSorter::visitIdentifier(Identifier_ptr identifier) {
}

void ConstraintSorter::visitPrimitive(Primitive_ptr primitive) {
}

void ConstraintSorter::visitTVariable(TVariable_ptr t_variable) {
}

void ConstraintSorter::visitTBool(TBool_ptr t_bool) {
}

void ConstraintSorter::visitTInt(TInt_ptr t_int) {
}

void ConstraintSorter::visitTString(TString_ptr t_string) {
}

void ConstraintSorter::visitVariable(Variable_ptr variable) {
}

void ConstraintSorter::visitSort(Sort_ptr sort) {
}

void ConstraintSorter::visitAttribute(Attribute_ptr attribute) {
}

void ConstraintSorter::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ConstraintSorter::visitVarBinding(VarBinding_ptr var_binding) {
  term_node = nullptr;
  visit_children_of(var_binding);
}

ConstraintSorter::VariableNode_ptr ConstraintSorter::get_variable_node(Variable_ptr variable) {
  auto it = variable_nodes.find(variable);
  if (it != variable_nodes.end()) {
    return it->second;
  }
  VariableNode_ptr variable_node = new VariableNode(variable);
  variable_nodes[variable] = variable_node;
  return variable_node;
}

ConstraintSorter::TermNode_ptr ConstraintSorter::process_child_nodes(TermNode_ptr left_node,
        TermNode_ptr right_node) {
  TermNode_ptr result_node = nullptr;
  if (left_node != nullptr and right_node != nullptr) {
    right_node->shiftToRight();
    right_node->addVariableNodes(left_node->getAllNodes(), true);
    delete left_node;
    result_node = right_node;
  } else if (left_node != nullptr) {
    left_node->shiftToLeft();
    result_node = left_node;
  } else if (right_node != nullptr) {
    right_node->shiftToRight();
    result_node = right_node;
  }
  return result_node;
}

void ConstraintSorter::sort_terms(std::vector<TermNode_ptr>& term_node_list) {
  std::vector<TermNode_ptr> sorted_term_node_list;

  for (auto it = term_node_list.begin(); it != term_node_list.end(); ) {
    if ((*it)->numOfTotalVars() == 0) {
      sorted_term_node_list.push_back((*it));
      it = term_node_list.erase(it);
    } else {
      it++;
    }
  }

  std::sort(term_node_list.begin(), term_node_list.end(),
          [](TermNode_ptr left_node, TermNode_ptr right_node) -> bool {
            return (left_node->numOfTotalVars() < right_node->numOfTotalVars());
          });

  for (auto it = term_node_list.begin(); it != term_node_list.end(); ) {
    if (not (*it)->hasSymbolicVar()) {
      sorted_term_node_list.push_back((*it));
      it = term_node_list.erase(it);
    } else {
      it++;
    }
  }

  term_node_list.insert(term_node_list.begin(), sorted_term_node_list.begin(), sorted_term_node_list.end());

/**
 * TODO Apply better heuristic to break dependency cycles
 * while term node list is not empty do that again and again
 */
//  int num_of_variable_counter = 1;
//  while (not term_node_list.empty()) {
//
//    std::queue<TermNode_ptr> work_list;
//    for (auto it = term_node_list.begin(); it != term_node_list.end(); ) {
//      if ((*it)->numOfTotalVars() == num_of_variable_counter) {
//        work_list.push(*it);
//        it = term_node_list.erase(it);
//      } else {
//        it++;
//      }
//
//      while (not work_list.empty()) {
//        TermNode_ptr curr_term_node = work_list.front(); work_list.pop();
//
//      }
//    }
//
//
//    num_of_variable_counter++;
//  }

  DVLOG(VLOG_LEVEL) << "node list sorted";
}

ConstraintSorter::TermNode::TermNode()
        : _node(nullptr), _has_symbolic_var_on_left(false), _has_symbolic_var_on_right(false) {
}

ConstraintSorter::TermNode::TermNode(Term_ptr node)
        : _node(node), _has_symbolic_var_on_left(false), _has_symbolic_var_on_right(false) {
}

ConstraintSorter::TermNode::~TermNode() {
}

std::string ConstraintSorter::TermNode::str() {
  std::stringstream ss;
  ss << this->_node << " -> l:" << _left_child_node_list.size() << " r:" << _right_child_node_list.size();

  ss << " l:";
  for (auto& variable_node : _left_child_node_list) {
    ss << " " << *(variable_node->getVariable());
  }

  ss << " r:";
  for (auto& variable_node : _right_child_node_list) {
    ss << " " << *(variable_node->getVariable());
  }

  return ss.str();
}

void ConstraintSorter::TermNode::setNode(Term_ptr node) {
  this->_node = node;
}

Term_ptr ConstraintSorter::TermNode::getNode() {
  return _node;
}

void ConstraintSorter::TermNode::addVariableNode(ConstraintSorter::VariableNode_ptr variable, bool is_left_side) {
  is_left_side ? _left_child_node_list.push_back(variable) : _right_child_node_list.push_back(variable);
}

void ConstraintSorter::TermNode::addVariableNodes(std::vector<VariableNode_ptr>& var_node_list, bool is_left_side) {
  is_left_side ?
          merge_vectors(_left_child_node_list, var_node_list) : merge_vectors(_right_child_node_list, var_node_list);
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::TermNode::getAllNodes() {
  _all_child_node_list.clear();
  _all_child_node_list.insert(_all_child_node_list.begin(), _left_child_node_list.begin(), _left_child_node_list.end());
  _all_child_node_list.insert(_all_child_node_list.end(), _right_child_node_list.begin(), _right_child_node_list.end());
  return _all_child_node_list;
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::TermNode::getLeftNodes() {
  return _left_child_node_list;
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::TermNode::getRightNodes() {
  return _right_child_node_list;
}

void ConstraintSorter::TermNode::shiftToLeft() {
  _left_child_node_list.insert(_left_child_node_list.end(), _right_child_node_list.begin(),
          _right_child_node_list.end());
  _right_child_node_list.clear();
}

void ConstraintSorter::TermNode::shiftToRight() {
  _right_child_node_list.insert(_right_child_node_list.begin(), _left_child_node_list.begin(),
          _left_child_node_list.end());
  _left_child_node_list.clear();
}

void ConstraintSorter::TermNode::addMeToChildVariableNodes() {
  for (auto& left_node : _left_child_node_list) {
    left_node->addTermNode(this, true);
  }
  for (auto& right_node : _right_child_node_list) {
    right_node->addTermNode(this, false);
  }
}

int ConstraintSorter::TermNode::numOfTotalVars() {
  return _left_child_node_list.size() + _right_child_node_list.size();
}

int ConstraintSorter::TermNode::numOfLeftVars() {
  return _left_child_node_list.size();
}

int ConstraintSorter::TermNode::numOfRightVars() {
  return _right_child_node_list.size();
}

void ConstraintSorter::TermNode::updateSymbolicVariableInfo() {
  for (auto& left_node : _left_child_node_list) {
    if (left_node->getVariable()->isSymbolic()) {
      _has_symbolic_var_on_left = true;
      break;
    }
  }
  for (auto& right_node : _right_child_node_list) {
    if (right_node->getVariable()->isSymbolic()) {
      _has_symbolic_var_on_right = true;
      break;
    }
  }
}

bool ConstraintSorter::TermNode::hasSymbolicVarOnLeft() {
  return _has_symbolic_var_on_left;
}

bool ConstraintSorter::TermNode::hasSymbolicVarOnRight() {
  return _has_symbolic_var_on_right;
}

bool ConstraintSorter::TermNode::hasSymbolicVar() {
  return _has_symbolic_var_on_left || _has_symbolic_var_on_right;
}

void ConstraintSorter::TermNode::merge_vectors(std::vector<VariableNode_ptr>& vector_1,
        std::vector<VariableNode_ptr>& vector_2) {
  vector_1.insert(vector_1.end(), vector_2.begin(), vector_2.end());
}

ConstraintSorter::VariableNode::VariableNode(Variable_ptr variable)
        : variable(variable) {
}

ConstraintSorter::VariableNode::~VariableNode() {
}

std::string ConstraintSorter::VariableNode::str() {
  std::stringstream ss;
  ss << *(this->variable) << " -> l:" << left_side_var_appearance_list.size() << " r:"
          << right_side_var_appearance_list.size();

  ss << " l:";
  for (auto& node : left_side_var_appearance_list) {
    ss << " " << node->getNode();
  }

  ss << " r:";
  for (auto& node : right_side_var_appearance_list) {
    ss << " " << node->getNode();
  }
  return ss.str();
}

Variable_ptr ConstraintSorter::VariableNode::getVariable() {
  return variable;
}

void ConstraintSorter::VariableNode::addTermNode(ConstraintSorter::TermNode_ptr node, bool is_left_side) {
  all_var_appearance_list.push_back(node);
  is_left_side ? left_side_var_appearance_list.push_back(node) : right_side_var_appearance_list.push_back(node);
}

} /* namespace Solver */
} /* namespace Vlab */
