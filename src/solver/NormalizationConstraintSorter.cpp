/*
 * ConstraintSorter.cpp
 *
 *  Created on: May 18, 2015
 *      Author: baki, will
 */

#include "NormalizationConstraintSorter.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int NormalizationConstraintSorter::VLOG_LEVEL = 13;
std::string NormalizationConstraintSorter::TermNode::count_var;

NormalizationConstraintSorter::NormalizationConstraintSorter(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table), term_node(nullptr) {

	if(symbol_table->has_count_variable()) {
		auto var = symbol_table->get_count_variable();
		NormalizationConstraintSorter::TermNode::count_var = var->getName();
	}
}

NormalizationConstraintSorter::~NormalizationConstraintSorter() {
  for(auto it = variable_nodes.cbegin(); it != variable_nodes.cend(); it++) {
    delete variable_nodes[it->first];
    variable_nodes[it->first] = nullptr;
  }
  if(term_node != nullptr) {
    delete term_node;
    term_node = nullptr;
  }
}

void NormalizationConstraintSorter::start() {
  Counter counter(root, symbol_table);
  counter.start();

  symbol_table->push_scope(root);
  visit(root);
  symbol_table->pop_scope();

  end();
}

void NormalizationConstraintSorter::end() {

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

void NormalizationConstraintSorter::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void NormalizationConstraintSorter::visitCommand(Command_ptr command) {
}

void NormalizationConstraintSorter::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void NormalizationConstraintSorter::visitTerm(Term_ptr term) {
}

void NormalizationConstraintSorter::visitExclamation(Exclamation_ptr exclamation_term) {
}

void NormalizationConstraintSorter::visitExists(Exists_ptr exists_term) {
}

void NormalizationConstraintSorter::visitForAll(ForAll_ptr for_all_term) {
}

void NormalizationConstraintSorter::visitLet(Let_ptr let_term) {
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

void NormalizationConstraintSorter::visitAnd(And_ptr and_term) {
  std::vector<TermNode_ptr> local_dependency_node_list;
  std::vector<Term_ptr> unsorted_constraints;

  if(symbol_table->has_count_variable()) {
		auto count_var = symbol_table->get_count_variable();
		auto rep_count_var = symbol_table->get_representative_variable_of_at_scope(symbol_table->top_scope(),count_var);
		NormalizationConstraintSorter::TermNode::count_var = rep_count_var->getName();
	}

  for(auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
  //for (auto& term : *(and_term->term_list)) {
//  	if(symbol_table->is_unsorted_constraint(*iter) and false) {
//  		unsorted_constraints.push_back((*iter)->clone());
//  		delete (*iter);
//			iter = and_term->term_list->erase(iter);
//  	} else {
			term_node = nullptr;
			visit(*iter);
			if (term_node == nullptr) {
				term_node = new TermNode(*iter);
			} else {
				term_node->setNode(*iter);
			}
			term_node->addMeToChildVariableNodes();
			term_node->updateSymbolicVariableInfo();
			local_dependency_node_list.push_back(term_node);
			iter++;
//  	}
  }
  term_node = nullptr;

  // LOG(INFO) << "total size: " << and_term->term_list->size();
  sort_terms(local_dependency_node_list);
  // std::cin.get();

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

  for(auto it = unsorted_constraints.cbegin(); it != unsorted_constraints.cend(); it++) {
		and_term->term_list->push_back((*it)->clone());
		delete *it;
	}
}

void NormalizationConstraintSorter::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void NormalizationConstraintSorter::visitNot(Not_ptr not_term) {
  term_node = nullptr;
  visit_children_of(not_term);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitUMinus(UMinus_ptr u_minus_term) {
  term_node = nullptr;
  visit_children_of(u_minus_term);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitMinus(Minus_ptr minus_term) {
  term_node = nullptr;
  visit(minus_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(minus_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::INT);
  term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitPlus(Plus_ptr plus_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(plus_term->term_list)) {
    term_node = nullptr;
    visit(term);
    
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->num_ops++;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
      result_node->num_ops = result_node->num_ops + term_node->num_ops +1;
      delete term_node;
    }
  }
  term_node = result_node;
  term_node->setType(TermNode::Type::INT);

}

void NormalizationConstraintSorter::visitTimes(Times_ptr times_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(times_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->num_ops++;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
      result_node->num_ops = result_node->num_ops + term_node->num_ops +1;
      delete term_node;
    }
  }
  term_node = result_node;
  term_node->setType(TermNode::Type::INT);
}

void NormalizationConstraintSorter::visitDiv(Div_ptr div_term) {
	LOG(FATAL) << "Implement me";
}

void NormalizationConstraintSorter::visitEq(Eq_ptr eq_term) {
  term_node = nullptr;
  visit(eq_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(eq_term->right_term);
  TermNode_ptr right_node = term_node;

  TermNode::Type term_type = TermNode::Type::NONE;
  if(left_node != nullptr and right_node != nullptr) {
    if(left_node->getType() != right_node->getType()) {
      LOG(FATAL) << "Term Types do not match, can't sort properly!";
    }
    term_type = left_node->getType();
  } else if(left_node != nullptr) {
    term_type = left_node->getType();
  } else if(right_node != nullptr) {
    term_type = right_node->getType();
  }


  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(term_type);

  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitNotEq(NotEq_ptr not_eq_term) {
  term_node = nullptr;
  visit(not_eq_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_eq_term->right_term);
  TermNode_ptr right_node = term_node;

  TermNode::Type term_type = TermNode::Type::NONE;
  if(left_node != nullptr and right_node != nullptr) {
    if(left_node->getType() != right_node->getType()) {
      LOG(FATAL) << "Term Types do not match, can't sort properly!";
    }
    term_type = left_node->getType();
  } else if(left_node != nullptr) {
    term_type = left_node->getType();
  } else if(right_node != nullptr) {
    term_type = right_node->getType();
  }

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(term_type);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
//  term_node->setNode(not_eq_term);
}


void NormalizationConstraintSorter::visitGt(Gt_ptr gt_term) {
  term_node = nullptr;
  visit(gt_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(gt_term->right_term);
  TermNode_ptr right_node = term_node;

  TermNode::Type term_type = TermNode::Type::NONE;
  if(left_node != nullptr and right_node != nullptr) {
    if(left_node->getType() != right_node->getType()) {
      LOG(FATAL) << "Term Types do not match, can't sort properly!";
    }
    term_type = left_node->getType();
  } else if(left_node != nullptr) {
    term_type = left_node->getType();
  } else if(right_node != nullptr) {
    term_type = right_node->getType();
  }

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(term_type);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitGe(Ge_ptr ge_term) {
  term_node = nullptr;
  visit(ge_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(ge_term->right_term);
  TermNode_ptr right_node = term_node;

  TermNode::Type term_type = TermNode::Type::NONE;
  if(left_node != nullptr and right_node != nullptr) {
    if(left_node->getType() != right_node->getType()) {
      LOG(FATAL) << "Term Types do not match, can't sort properly!";
    }
    term_type = left_node->getType();
  } else if(left_node != nullptr) {
    term_type = left_node->getType();
  } else if(right_node != nullptr) {
    term_type = right_node->getType();
  }

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(term_type);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitLt(Lt_ptr lt_term) {
  term_node = nullptr;
  visit(lt_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(lt_term->right_term);
  TermNode_ptr right_node = term_node;

  TermNode::Type term_type = TermNode::Type::NONE;
  if(left_node != nullptr and right_node != nullptr) {
    if(left_node->getType() != right_node->getType()) {
      LOG(FATAL) << "Term Types do not match, can't sort properly!";
    }
    term_type = left_node->getType();
  } else if(left_node != nullptr) {
    term_type = left_node->getType();
  } else if(right_node != nullptr) {
    term_type = right_node->getType();
  }

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(term_type);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitLe(Le_ptr le_term) {
  term_node = nullptr;
  visit(le_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(le_term->right_term);
  TermNode_ptr right_node = term_node;

  TermNode::Type term_type = TermNode::Type::NONE;
  if(left_node != nullptr and right_node != nullptr) {
    if(left_node->getType() != right_node->getType()) {
      LOG(FATAL) << "Term Types do not match, can't sort properly!";
    }
    term_type = left_node->getType();
  } else if(left_node != nullptr) {
    term_type = left_node->getType();
  } else if(right_node != nullptr) {
    term_type = right_node->getType();
  }

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(term_type);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitConcat(Concat_ptr concat_term) {
  TermNode_ptr result_node = nullptr;
  for (auto& term : *(concat_term->term_list)) {
    term_node = nullptr;
    visit(term);
    if (result_node == nullptr and term_node != nullptr) {
      result_node = term_node;
      result_node->num_ops++;
      result_node->shiftToRight();
    } else if (term_node != nullptr) {
      result_node->addVariableNodes(term_node->getAllNodes(), false);
      result_node->num_ops = result_node->num_ops + term_node->num_ops+1;
      delete term_node;
    }
  }
  term_node = result_node;
  term_node->setType(TermNode::Type::STRING);
}

void NormalizationConstraintSorter::visitIn(In_ptr in_term) {
  term_node = nullptr;
  visit(in_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(in_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}


void NormalizationConstraintSorter::visitNotIn(NotIn_ptr not_in_term) {
  term_node = nullptr;
  visit(not_in_term->left_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_in_term->right_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitLen(Len_ptr len_term) {
  term_node = nullptr;
  visit_children_of(len_term);
  if (term_node != nullptr) {
    term_node->shiftToRight();
  }
  term_node->setType(TermNode::Type::INT);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitContains(Contains_ptr contains_term) {
  term_node = nullptr;
  visit(contains_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(contains_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitNotContains(NotContains_ptr not_contains_term) {
  term_node = nullptr;
  visit(not_contains_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_contains_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitBegins(Begins_ptr begins_term) {
  term_node = nullptr;
  visit(begins_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(begins_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitNotBegins(NotBegins_ptr not_begins_term) {
  term_node = nullptr;
  visit(not_begins_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_begins_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitEnds(Ends_ptr ends_term) {
  term_node = nullptr;
  visit(ends_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(ends_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitNotEnds(NotEnds_ptr not_ends_term) {
  term_node = nullptr;
  visit(not_ends_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(not_ends_term->search_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitIndexOf(IndexOf_ptr index_of_term) {
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
  term_node->setType(TermNode::Type::INT);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
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
  term_node->setType(TermNode::Type::INT);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitCharAt(CharAt_ptr char_at_term) {
  term_node = nullptr;
  visit(char_at_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(char_at_term->index_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitSubString(SubString_ptr sub_string_term) {
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
  term_node->setType(TermNode::Type::STRING);
  //term_node->num_ops = left_node->num_ops+right_node->num_ops +1;
}

void NormalizationConstraintSorter::visitToUpper(ToUpper_ptr to_upper_term) {
  term_node = nullptr;
  visit_children_of(to_upper_term);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitToLower(ToLower_ptr to_lower_term) {
  term_node = nullptr;
  visit_children_of(to_lower_term);
}

void NormalizationConstraintSorter::visitTrim(Trim_ptr trim_term) {
  term_node = nullptr;
  visit_children_of(trim_term);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitToString(ToString_ptr to_string_term) {
  term_node = nullptr;
  visit_children_of(to_string_term);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitToInt(ToInt_ptr to_int_term) {
  term_node = nullptr;
  visit_children_of(to_int_term);
  term_node->num_ops++;
}

void NormalizationConstraintSorter::visitReplace(Replace_ptr replace_term) {
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
  //term_node->num_ops = left_node->num_ops+right_node_1->num_ops;
  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::STRING);
 // term_node->num_ops += right_node_1->num_ops;
}

void NormalizationConstraintSorter::visitCount(Count_ptr count_term) {
  term_node = nullptr;
  visit(count_term->subject_term);
  TermNode_ptr left_node = term_node;
  term_node = nullptr;
  visit(count_term->bound_term);
  TermNode_ptr right_node = term_node;

  term_node = process_child_nodes(left_node, right_node);
  term_node->setType(TermNode::Type::INT);
  //term_node->num_ops++;
}

void NormalizationConstraintSorter::visitIte(Ite_ptr ite_term) {
}

void NormalizationConstraintSorter::visitReConcat(ReConcat_ptr re_concat_term) {
}

void NormalizationConstraintSorter::visitReUnion(ReUnion_ptr re_union_term) {
}

void NormalizationConstraintSorter::visitReInter(ReInter_ptr re_inter_term) {
}

void NormalizationConstraintSorter::visitReStar(ReStar_ptr re_star_term) {
}

void NormalizationConstraintSorter::visitRePlus(RePlus_ptr re_plus_term) {
}

void NormalizationConstraintSorter::visitReOpt(ReOpt_ptr re_opt_term) {
}

void NormalizationConstraintSorter::visitToRegex(ToRegex_ptr to_regex_term) {
}

void NormalizationConstraintSorter::visitUnknownTerm(Unknown_ptr unknown_term) {
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

void NormalizationConstraintSorter::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void NormalizationConstraintSorter::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table->get_variable(qi_term->getVarName());
  if (not variable->isLocalLetVar()) {
    VariableNode_ptr variable_node = get_variable_node(variable);
    term_node = new TermNode();
    term_node->addVariableNode(variable_node, false);
    if(variable->getType() == Variable::Type::INT) {
      term_node->setType(TermNode::Type::INT);
    } else if(variable->getType() == Variable::Type::STRING) {
      term_node->setType(TermNode::Type::STRING);
    }
    term_node->num_ops++;
  }

}

void NormalizationConstraintSorter::visitTermConstant(TermConstant_ptr term_constant) {
  term_node = new TermNode(term_constant);
  switch(term_constant->getValueType()) {
    case Primitive::Type::STRING:
    case Primitive::Type::REGEX:
      term_node->setType(TermNode::Type::STRING);
      break;
    case Primitive::Type::NUMERAL:
      term_node->setType(TermNode::Type::INT);
      break;
    case Primitive::Type::BOOL:
      term_node->setType(TermNode::Type::BOOL);
      break;
    default:
      break;
  }
  term_node->num_ops++;
  
}

void NormalizationConstraintSorter::visitIdentifier(Identifier_ptr identifier) {
}

void NormalizationConstraintSorter::visitPrimitive(Primitive_ptr primitive) {
}

void NormalizationConstraintSorter::visitTVariable(TVariable_ptr t_variable) {
}

void NormalizationConstraintSorter::visitTBool(TBool_ptr t_bool) {
}

void NormalizationConstraintSorter::visitTInt(TInt_ptr t_int) {
}

void NormalizationConstraintSorter::visitTString(TString_ptr t_string) {
}

void NormalizationConstraintSorter::visitVariable(Variable_ptr variable) {
}

void NormalizationConstraintSorter::visitSort(Sort_ptr sort) {
}

void NormalizationConstraintSorter::visitAttribute(Attribute_ptr attribute) {
}

void NormalizationConstraintSorter::visitSortedVar(SortedVar_ptr sorted_var) {
}

void NormalizationConstraintSorter::visitVarBinding(VarBinding_ptr var_binding) {
  term_node = nullptr;
  visit_children_of(var_binding);
}

NormalizationConstraintSorter::VariableNode_ptr NormalizationConstraintSorter::get_variable_node(Variable_ptr variable) {
  auto it = variable_nodes.find(variable);
  if (it != variable_nodes.end()) {
    return it->second;
  }
  VariableNode_ptr variable_node = new VariableNode(variable);
  variable_nodes[variable] = variable_node;
  return variable_node;
}

NormalizationConstraintSorter::TermNode_ptr NormalizationConstraintSorter::process_child_nodes(TermNode_ptr left_node,
        TermNode_ptr right_node) {
  TermNode_ptr result_node = nullptr;
  if (left_node != nullptr and right_node != nullptr) {
    right_node->shiftToRight();
    right_node->addVariableNodes(left_node->getAllNodes(), true);
    right_node->num_ops += left_node->num_ops + 1;
    delete left_node;
    result_node = right_node;
  } else if (left_node != nullptr) {
    left_node->shiftToLeft();
    left_node->num_ops ++;
    result_node = left_node;
  } else if (right_node != nullptr) {
    right_node->shiftToRight();
    right_node->num_ops++;
    result_node = right_node;
  }
  return result_node;
}

void NormalizationConstraintSorter::sort_terms(std::vector<TermNode_ptr>& term_node_list) {

//  LOG(INFO) << "-- Before size = " << term_node_list.size();

  std::vector<TermNode_ptr> temp_term_node_list;

  std::queue<std::vector<TermNode_ptr>> terms_to_process;
  std::vector<TermNode_ptr> term_group;
  for(auto iter = term_node_list.begin(); iter != term_node_list.end();) {
    if((*iter)->hasSymbolicVar()) {
      term_group.push_back(*iter);
    } else {
      temp_term_node_list.push_back(*iter);
    }
    iter++;
  }

  terms_to_process.push(term_group);
//  LOG(INFO) << "-- terms_to_process.size() = " << terms_to_process.size();

  // compute dependency graph
  // compute graph for the nodes, starting with terms that have query variable
  // all other terms that share variables other than query variable, add edges between the nodes
//  int hops = 1;
  while(not terms_to_process.empty()) {
    auto current_group = terms_to_process.front();
    terms_to_process.pop();
    std::vector<TermNode_ptr> next_group;

    for(auto iter = temp_term_node_list.begin(); iter != temp_term_node_list.end();) {
      bool edge_added = false;
      for(auto current_group_iter : current_group) {
        if(has_shared_variables(*iter, current_group_iter)) {
          edge_added = true;
          (*iter)->setDepth(current_group_iter->getDepth()+1);
          break;
        }
      }

      if(edge_added) {
//        (*iter)->setDepth(hops);
        next_group.push_back(*iter);
        iter = temp_term_node_list.erase(iter);
      } else {
        iter++;
      }
    }

    if(not next_group.empty()) {
      terms_to_process.push(next_group);
    }
//    hops++;
  }

//  if(not temp_term_node_list.empty()) {
//    LOG(FATAL) << "Not empty";
//  }

	/*
	 * compare by
	 * (0) dependency hops to count variable
	 * (1) operation type (string/int)
	 * (2) operator
	 * -- NOT DOING -- (3) length of operation
	 * -- NOT DOING -- (4) left length
	 * -- NOT DOING -- (5) right length
	 * (6) num vars
	 * (7) num vars on left side
	 * (8) num vars on right side
	 * -- NOT DOING -- (9) operation vector length
	 * -- NOT DOING -- (10) operation vector types
	 * (11) lexigraphic string
	 */
	auto compare_function = [](TermNode_ptr left_node, TermNode_ptr right_node) -> bool {

	  // topo sort depth level; sort in decreasing depth




    if(left_node->getDepth() < right_node->getDepth()) {
      return 0;
    }
    if(left_node->getDepth() > right_node->getDepth()) {
      return 1;
    }

    if(left_node->getType() < right_node->getType()) {
     return 0;
	  }
	  if(left_node->getType() > right_node->getType()) {
	    return 1;
	  }

   if(left_node->getNode()->type() < right_node->getNode()->type()) {
     if(left_node->getNode()->type() == Term::Type::CONCAT and right_node->getNode()->type() == Term::Type::NOTEQ) {
       LOG(FATAL) << "WAT";
     }
     return 1;
   }
   if(left_node->getNode()->type() > right_node->getNode()->type()) {
     if(left_node->getNode()->type() == Term::Type::CONCAT and right_node->getNode()->type() == Term::Type::NOTEQ) {
       LOG(FATAL) << " GOOD WAT";
     }
     return 0;
   }

   if(left_node->numOfTotalVars() < right_node->numOfTotalVars()) {
     return 1;
   }
   if(left_node->numOfTotalVars() > right_node->numOfTotalVars()) {
     return 0;
   }

   if(left_node->numOfLeftVars() < right_node->numOfLeftVars()) {
     return 1;
   }
   if(left_node->numOfLeftVars() > right_node->numOfLeftVars()) {
     return 0;
   }

   if(left_node->numOfRightVars() < right_node->numOfRightVars()) {
     return 1;
   }
   if(left_node->numOfRightVars() > right_node->numOfRightVars()) {
     return 0;
   }

   if(left_node->num_ops < right_node->num_ops) {
     return 1 ;
   }
   if(left_node->num_ops > right_node->num_ops) {
     return 0;
   }

   return Ast2Dot::toString(left_node->getNode()) <= Ast2Dot::toString(right_node->getNode());
	};

  std::stable_sort(term_node_list.begin(), term_node_list.end(),compare_function);

  DVLOG(VLOG_LEVEL) << "node list sorted";
}

bool NormalizationConstraintSorter::has_shared_variables(TermNode_ptr term1, TermNode_ptr term2) {
  for(auto iter1 : term1->getAllNodes()) {
    for(auto iter2 : term2->getAllNodes()) {
      if(iter1 == iter2) {
//        LOG(INFO) << "Var pointers equal";
        return true;
      } else if(iter1->getVariable()->getName() == iter2->getVariable()->getName()) {
//        LOG(INFO) << "Var names equal";
        return true;
      }
    }
  }
  return false;
}

NormalizationConstraintSorter::TermNode::TermNode()
        : _node(nullptr), _has_symbolic_var_on_left(false), _has_symbolic_var_on_right(false), _type(Type::NONE), _depth(0) {
  this->num_ops = 0;
}

NormalizationConstraintSorter::TermNode::TermNode(Term_ptr node)
        : _node(node), _has_symbolic_var_on_left(false), _has_symbolic_var_on_right(false), _type(Type::NONE),_depth(0) {
  this->num_ops = 0;
}

NormalizationConstraintSorter::TermNode::~TermNode() {
}

std::string NormalizationConstraintSorter::TermNode::str() {
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

void NormalizationConstraintSorter::TermNode::setType(TermNode::Type type) {
  _type = type;
}

NormalizationConstraintSorter::TermNode::Type NormalizationConstraintSorter::TermNode::getType() {
  return _type;
}

void NormalizationConstraintSorter::TermNode::setNode(Term_ptr node) {
  this->_node = node;
}

Term_ptr NormalizationConstraintSorter::TermNode::getNode() {
  return _node;
}

void NormalizationConstraintSorter::TermNode::addVariableNode(NormalizationConstraintSorter::VariableNode_ptr variable, bool is_left_side) {
  is_left_side ? _left_child_node_list.push_back(variable) : _right_child_node_list.push_back(variable);
}

void NormalizationConstraintSorter::TermNode::addVariableNodes(std::vector<VariableNode_ptr>& var_node_list, bool is_left_side) {
  is_left_side ?
          merge_vectors(_left_child_node_list, var_node_list) : merge_vectors(_right_child_node_list, var_node_list);
}

std::vector<NormalizationConstraintSorter::VariableNode_ptr>& NormalizationConstraintSorter::TermNode::getAllNodes() {
  _all_child_node_list.clear();
  _all_child_node_list.insert(_all_child_node_list.begin(), _left_child_node_list.begin(), _left_child_node_list.end());
  _all_child_node_list.insert(_all_child_node_list.end(), _right_child_node_list.begin(), _right_child_node_list.end());
  return _all_child_node_list;
}

std::vector<NormalizationConstraintSorter::VariableNode_ptr>& NormalizationConstraintSorter::TermNode::getLeftNodes() {
  return _left_child_node_list;
}

std::vector<NormalizationConstraintSorter::VariableNode_ptr>& NormalizationConstraintSorter::TermNode::getRightNodes() {
  return _right_child_node_list;
}

void NormalizationConstraintSorter::TermNode::shiftToLeft() {
  _left_child_node_list.insert(_left_child_node_list.end(), _right_child_node_list.begin(),
          _right_child_node_list.end());
  _right_child_node_list.clear();
}

void NormalizationConstraintSorter::TermNode::shiftToRight() {
  _right_child_node_list.insert(_right_child_node_list.begin(), _left_child_node_list.begin(),
          _left_child_node_list.end());
  _left_child_node_list.clear();
}

void NormalizationConstraintSorter::TermNode::addMeToChildVariableNodes() {
  for (auto& left_node : _left_child_node_list) {
    left_node->addTermNode(this, true);
  }
  for (auto& right_node : _right_child_node_list) {
    right_node->addTermNode(this, false);
  }
}

int NormalizationConstraintSorter::TermNode::numOfTotalVars() {
  return _left_child_node_list.size() + _right_child_node_list.size();
}

int NormalizationConstraintSorter::TermNode::numOfLeftVars() {
  return _left_child_node_list.size();
}

int NormalizationConstraintSorter::TermNode::numOfRightVars() {
  return _right_child_node_list.size();
}

void NormalizationConstraintSorter::TermNode::updateSymbolicVariableInfo() {
	if(count_var.empty()) {
  	return;
  }

	for (auto& left_node : _left_child_node_list) {
    if (left_node->getVariable()->getName() == count_var) {
      _has_symbolic_var_on_left = true;
      break;
    }
  }
  for (auto& right_node : _right_child_node_list) {
    if (right_node->getVariable()->getName() == count_var) {
      _has_symbolic_var_on_right = true;
      break;
    }
  }
}

bool NormalizationConstraintSorter::TermNode::hasSymbolicVarOnLeft() {
  return _has_symbolic_var_on_left;
}

bool NormalizationConstraintSorter::TermNode::hasSymbolicVarOnRight() {
  return _has_symbolic_var_on_right;
}

bool NormalizationConstraintSorter::TermNode::hasSymbolicVar() {
  return _has_symbolic_var_on_left || _has_symbolic_var_on_right;
}

int NormalizationConstraintSorter::TermNode::getDepth() {
  return _depth;
}

void NormalizationConstraintSorter::TermNode::setDepth(int depth) {
  _depth = depth;
}

void NormalizationConstraintSorter::TermNode::merge_vectors(std::vector<VariableNode_ptr>& vector_1,
        std::vector<VariableNode_ptr>& vector_2) {
  vector_1.insert(vector_1.end(), vector_2.begin(), vector_2.end());
}

NormalizationConstraintSorter::VariableNode::VariableNode(Variable_ptr variable)
        : variable(variable) {
}

NormalizationConstraintSorter::VariableNode::~VariableNode() {
}

std::string NormalizationConstraintSorter::VariableNode::str() {
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

Variable_ptr NormalizationConstraintSorter::VariableNode::getVariable() {
  return variable;
}

void NormalizationConstraintSorter::VariableNode::addTermNode(NormalizationConstraintSorter::TermNode_ptr node, bool is_left_side) {
  all_var_appearance_list.push_back(node);
  is_left_side ? left_side_var_appearance_list.push_back(node) : right_side_var_appearance_list.push_back(node);
}

} /* namespace Solver */
} /* namespace Vlab */
