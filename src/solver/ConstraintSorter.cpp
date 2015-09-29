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
        : root(script), symbol_table(symbol_table), visitable_node(nullptr) {
}

ConstraintSorter::~ConstraintSorter() {
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
}

void ConstraintSorter::visitScript(Script_ptr script) {
  for (auto& command : *(script->command_list)) {
    visitable_node = nullptr;
    visit(command);
    if (visitable_node == nullptr) {
      visitable_node = new VisitableNode(command);
    } else {
      visitable_node->set_node(command);
    }
    visitable_node->add_me_to_child_variable_nodes();
    dependency_node_list.push_back(visitable_node);
  }

  sort_visitable_nodes(dependency_node_list);

  if (VLOG_IS_ON(VLOG_LEVEL)) {
    DVLOG(VLOG_LEVEL) << "global dependency info: " << script;
    for (auto& node : dependency_node_list) {
      DVLOG(VLOG_LEVEL) << node->str();
    }

    for (auto& node : variable_nodes) {
      DVLOG(VLOG_LEVEL) << node.second->str();
    }
  }

  // figure out what will be the next commands in dependency node

  // do topological sort

  // update command list
  script->command_list->clear();
  for (auto& visitable_node : dependency_node_list) {
    script->command_list->push_back(dynamic_cast<Command_ptr>(visitable_node->get_node()));
  }
}

void ConstraintSorter::visitCommand(Command_ptr command) {
  switch (command->getType()) {
  case Command::Type::ASSERT: {
    visit_children_of(command);
    break;
  }
  default:
    LOG(FATAL)<< "'" << *command<< "' is not expected.";
    break;
  }
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
}

void ConstraintSorter::visitAnd(And_ptr and_term) {
  std::vector<VisitableNode_ptr> local_dependency_node_list;
  for (auto& term : *(and_term->term_list)) {
    visitable_node = nullptr;
    visit(term);
    if (visitable_node == nullptr) {
      visitable_node = new VisitableNode(term);
    } else {
      visitable_node->set_node(term);
    }
    visitable_node->add_me_to_child_variable_nodes();
    local_dependency_node_list.push_back(visitable_node);
  }

  sort_visitable_nodes(local_dependency_node_list);

//	if (VLOG_IS_ON(VLOG_LEVEL)) {
//		for (auto& node : local_dependency_node_list) {
//			DVLOG(VLOG_LEVEL) << node->str();
//		}
//
//		for (auto& node : variable_nodes) {
//			DVLOG(VLOG_LEVEL) << node.second->str();
//		}
//	}

// figure out what will be the next commands in dependency node

// do topological sort
  visitable_node = new VisitableNode();
  for (auto& node : local_dependency_node_list) {
    for (auto& var_node : node->get_left_nodes()) {
      if (symbol_table->get_total_count(var_node->get_variable())
              != symbol_table->get_local_count(var_node->get_variable())) {
        visitable_node->add_node(var_node, true);
      }
    }
    for (auto& var_node : node->get_right_nodes()) {
      if (symbol_table->get_total_count(var_node->get_variable())
              != symbol_table->get_local_count(var_node->get_variable())) {
        visitable_node->add_node(var_node, false);
      }
    }
    VisitableNode_ptr tmp = node;
    node = nullptr;
    delete tmp;
  }
}

void ConstraintSorter::visitOr(Or_ptr or_term) {
  VisitableNode_ptr result_node = nullptr;
  for (auto& term : *(or_term->term_list)) {
    visitable_node = nullptr;
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
    if (result_node == nullptr and visitable_node != nullptr) {
      result_node = visitable_node;
    } else if (visitable_node != nullptr) {
      for (auto& var_node : visitable_node->get_left_nodes()) {
        if (symbol_table->get_total_count(var_node->get_variable())
                != symbol_table->get_local_count(var_node->get_variable())) {
          result_node->add_node(var_node, true);
        }
      }
      for (auto& var_node : visitable_node->get_right_nodes()) {
        if (symbol_table->get_total_count(var_node->get_variable())
                != symbol_table->get_local_count(var_node->get_variable())) {
          result_node->add_node(var_node, false);
        }
      }
      VisitableNode_ptr tmp = visitable_node;
      visitable_node = nullptr;
      delete tmp;
    }
  }
  visitable_node = result_node;
}

void ConstraintSorter::visitNot(Not_ptr not_term) {
  visitable_node = nullptr;
  visit_children_of(not_term);
}

void ConstraintSorter::visitUMinus(UMinus_ptr u_minus_term) {
  visitable_node = nullptr;
  visit_children_of(u_minus_term);
}

void ConstraintSorter::visitMinus(Minus_ptr minus_term) {
  visitable_node = nullptr;
  visit(minus_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(minus_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitPlus(Plus_ptr plus_term) {
  visitable_node = nullptr;
  visit(plus_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(plus_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitEq(Eq_ptr eq_term) {
  visitable_node = nullptr;
  visit(eq_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(eq_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotEq(NotEq_ptr not_eq_term) {
}


void ConstraintSorter::visitGt(Gt_ptr gt_term) {
  visitable_node = nullptr;
  visit(gt_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(gt_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitGe(Ge_ptr ge_term) {
  visitable_node = nullptr;
  visit(ge_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(ge_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLt(Lt_ptr lt_term) {
  visitable_node = nullptr;
  visit(lt_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(lt_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLe(Le_ptr le_term) {
  visitable_node = nullptr;
  visit(le_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(le_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitConcat(Concat_ptr concat_term) {
  VisitableNode_ptr result_node = nullptr;
  for (auto& term : *(concat_term->term_list)) {
    visitable_node = nullptr;
    visit(term);
    if (result_node == nullptr and visitable_node != nullptr) {
      result_node = visitable_node;
      result_node->shift_to_right();
    } else if (visitable_node != nullptr) {
      result_node->add_nodes(visitable_node->get_all_nodes(), false);
    }
  }
  visitable_node = result_node;
}

void ConstraintSorter::visitIn(In_ptr in_term) {
  visitable_node = nullptr;
  visit(in_term->left_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(in_term->right_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}


void ConstraintSorter::visitNotIn(NotIn_ptr not_in_term) {
}

void ConstraintSorter::visitLen(Len_ptr len_term) {
  visitable_node = nullptr;
  visit_children_of(len_term);
  if (visitable_node != nullptr) {
    visitable_node->shift_to_right();
  }
}

void ConstraintSorter::visitContains(Contains_ptr contains_term) {
  visitable_node = nullptr;
  visit(contains_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(contains_term->search_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotContains(NotContains_ptr not_contains_term) {
}

void ConstraintSorter::visitBegins(Begins_ptr begins_term) {
  visitable_node = nullptr;
  visit(begins_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(begins_term->search_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void ConstraintSorter::visitEnds(Ends_ptr ends_term) {
  visitable_node = nullptr;
  visit(ends_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(ends_term->search_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void ConstraintSorter::visitIndexOf(IndexOf_ptr index_of_term) {
  visitable_node = nullptr;
  visit(index_of_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(index_of_term->search_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visitable_node = nullptr;
  visit(last_index_of_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(last_index_of_term->search_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visitable_node = nullptr;
  visit(char_at_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(char_at_term->index_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitSubString(SMT::SubString_ptr sub_string_term) {
  visitable_node = nullptr;
  visit(sub_string_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(sub_string_term->start_index_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visitable_node = nullptr;
  visit_children_of(to_upper_term);
}

void ConstraintSorter::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visitable_node = nullptr;
  visit_children_of(to_lower_term);
}

void ConstraintSorter::visitTrim(SMT::Trim_ptr trim_term) {
  visitable_node = nullptr;
  visit_children_of(trim_term);
}

void ConstraintSorter::visitReplace(Replace_ptr replace_term) {
  visitable_node = nullptr;
  visit(replace_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(replace_term->search_term);
  VisitableNode_ptr right_node_1 = visitable_node;
  visitable_node = nullptr;
  visit(replace_term->replace_term);
  VisitableNode_ptr right_node_2 = visitable_node;

  VisitableNode_ptr right_node = process_child_nodes(right_node_1, right_node_2);
  if (right_node != nullptr) {
    right_node->shift_to_right();
  }
  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitCount(Count_ptr count_term) {
  visitable_node = nullptr;
  visit(count_term->subject_term);
  VisitableNode_ptr left_node = visitable_node;
  visitable_node = nullptr;
  visit(count_term->bound_term);
  VisitableNode_ptr right_node = visitable_node;

  visitable_node = process_child_nodes(left_node, right_node);
}

void ConstraintSorter::visitIte(Ite_ptr ite_term) {
}

void ConstraintSorter::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstraintSorter::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstraintSorter::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void ConstraintSorter::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ConstraintSorter::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  VariableNode_ptr variable_node = get_variable_node(variable);

  visitable_node = new VisitableNode();
  visitable_node->add_node(variable_node, false);
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

ConstraintSorter::VisitableNode_ptr ConstraintSorter::process_child_nodes(VisitableNode_ptr left_node,
        VisitableNode_ptr right_node) {
  VisitableNode_ptr result_node = nullptr;
  if (left_node != nullptr and right_node != nullptr) {
    right_node->shift_to_right();
    right_node->add_nodes(left_node->get_all_nodes(), true);
    delete left_node;
    result_node = right_node;
  } else if (left_node != nullptr) {
    left_node->shift_to_left();
    result_node = left_node;
  } else if (right_node != nullptr) {
    right_node->shift_to_right();
    result_node = right_node;
  }
  return result_node;
}

void ConstraintSorter::sort_visitable_nodes(std::vector<VisitableNode_ptr>& visitable_node_list) {
  std::sort(visitable_node_list.begin(), visitable_node_list.end(),
          [](VisitableNode_ptr left_node, VisitableNode_ptr right_node) -> bool {
            if (left_node->num_of_total_vars() == 0) {return true;}
            if (left_node->num_of_left_vars() < right_node->num_of_left_vars()) {return true;}
            if (left_node->num_of_total_vars() < right_node->num_of_total_vars()) {return true;}
            return false;
          });

  auto begin = std::find_if(visitable_node_list.begin(), visitable_node_list.end(), [](VisitableNode_ptr node) -> bool {
    return node->num_of_total_vars() == 1;
  });

  auto end = std::find_if(begin, visitable_node_list.end(), [](VisitableNode_ptr node) -> bool {
    return node->num_of_total_vars() == 2;
  });

  std::sort(begin, end, [](VisitableNode_ptr left_node, VisitableNode_ptr right_node) -> bool {
    if (left_node->num_of_left_vars() < right_node->num_of_right_vars()) {return false;}
    return true;
  });

  DVLOG(VLOG_LEVEL) << "node list sorted";
}

ConstraintSorter::VisitableNode::VisitableNode()
        : _node(nullptr), _has_symbolic_var_on_left(false), _has_symbolic_var_on_right(false) {
}

ConstraintSorter::VisitableNode::VisitableNode(Visitable_ptr node)
        : _node(node), _has_symbolic_var_on_left(false), _has_symbolic_var_on_right(false) {
}

ConstraintSorter::VisitableNode::~VisitableNode() {
}

std::string ConstraintSorter::VisitableNode::str() {
  std::stringstream ss;
  ss << this->_node << " -> l:" << _left_child_node_list.size() << " r:" << _right_child_node_list.size();

  ss << " l:";
  for (auto& variable_node : _left_child_node_list) {
    ss << " " << *(variable_node->get_variable());
  }

  ss << " r:";
  for (auto& variable_node : _right_child_node_list) {
    ss << " " << *(variable_node->get_variable());
  }

  return ss.str();
}

void ConstraintSorter::VisitableNode::set_node(Visitable_ptr node) {
  this->_node = node;
}

Visitable_ptr ConstraintSorter::VisitableNode::get_node() {
  return _node;
}

void ConstraintSorter::VisitableNode::add_node(ConstraintSorter::VariableNode_ptr variable, bool is_left_side) {
  is_left_side ? _left_child_node_list.push_back(variable) : _right_child_node_list.push_back(variable);
}

void ConstraintSorter::VisitableNode::add_nodes(std::vector<VariableNode_ptr>& var_node_list, bool is_left_side) {
  is_left_side ?
          merge_vectors(_left_child_node_list, var_node_list) : merge_vectors(_right_child_node_list, var_node_list);
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::VisitableNode::get_all_nodes() {
  _all_child_node_list.clear();
  _all_child_node_list.insert(_all_child_node_list.begin(), _left_child_node_list.begin(), _left_child_node_list.end());
  _all_child_node_list.insert(_all_child_node_list.end(), _right_child_node_list.begin(), _right_child_node_list.end());
  return _all_child_node_list;
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::VisitableNode::get_left_nodes() {
  return _left_child_node_list;
}

std::vector<ConstraintSorter::VariableNode_ptr>& ConstraintSorter::VisitableNode::get_right_nodes() {
  return _right_child_node_list;
}

void ConstraintSorter::VisitableNode::shift_to_left() {
  _left_child_node_list.insert(_left_child_node_list.end(), _right_child_node_list.begin(),
          _right_child_node_list.end());
  _right_child_node_list.clear();
}

void ConstraintSorter::VisitableNode::shift_to_right() {
  _right_child_node_list.insert(_right_child_node_list.begin(), _left_child_node_list.begin(),
          _left_child_node_list.end());
  _left_child_node_list.clear();
}

void ConstraintSorter::VisitableNode::add_me_to_child_variable_nodes() {
  for (auto& left_node : _left_child_node_list) {
    left_node->add_node(this, true);
  }
  for (auto& right_node : _right_child_node_list) {
    right_node->add_node(this, false);
  }
}

int ConstraintSorter::VisitableNode::num_of_total_vars() {
  return _left_child_node_list.size() + _right_child_node_list.size();
}

int ConstraintSorter::VisitableNode::num_of_left_vars() {
  return _left_child_node_list.size();
}

int ConstraintSorter::VisitableNode::num_of_right_vars() {
  return _right_child_node_list.size();
}

void ConstraintSorter::VisitableNode::check_for_symbolic_variables() {
  for (auto& left_node : _left_child_node_list) {
    if (left_node->get_variable()->isSymbolic()) {
      _has_symbolic_var_on_left = true;
      break;
    }
  }
  for (auto& right_node : _right_child_node_list) {
    if (right_node->get_variable()->isSymbolic()) {
      _has_symbolic_var_on_right = true;
      break;
    }
  }
}

bool ConstraintSorter::VisitableNode::has_symbolic_var_on_left() {
  return _has_symbolic_var_on_left;
}

bool ConstraintSorter::VisitableNode::has_symbolic_var_on_right() {
  return _has_symbolic_var_on_right;
}

bool ConstraintSorter::VisitableNode::has_symbolic_var() {
  return _has_symbolic_var_on_left || _has_symbolic_var_on_right;
}

void ConstraintSorter::VisitableNode::merge_vectors(std::vector<VariableNode_ptr>& vector_1,
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
    ss << " " << node->get_node();
  }

  ss << " r:";
  for (auto& node : right_side_var_appearance_list) {
    ss << " " << node->get_node();
  }
  return ss.str();
}

Variable_ptr ConstraintSorter::VariableNode::get_variable() {
  return variable;
}

void ConstraintSorter::VariableNode::add_node(ConstraintSorter::VisitableNode_ptr node, bool is_left_side) {
  all_var_appearance_list.push_back(node);
  is_left_side ? left_side_var_appearance_list.push_back(node) : right_side_var_appearance_list.push_back(node);
}

} /* namespace Solver */
} /* namespace Vlab */
