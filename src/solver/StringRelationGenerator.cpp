//
// Created by will on 3/4/16.
//

#include "StringRelationGenerator.h"

#include <glog/logging.h>
#include <iostream>
#include <utility>
#include <vector>

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringRelationGenerator::VLOG_LEVEL = 14;

StringRelationGenerator::StringRelationGenerator(Script_ptr script, SymbolTable_ptr symbol_table)
    : root_(script),
      symbol_table_(symbol_table) {
  current_term_ = nullptr;
  current_trackmap_ = std::shared_ptr<std::map<std::string,int>>(new std::map<std::string,int>);
}

StringRelationGenerator::~StringRelationGenerator() {
  // delete var track map ptr?
}

void StringRelationGenerator::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "String relation extraction starts at node: " << node;
  visit(node);
  end();
}

void StringRelationGenerator::start() {
  DVLOG(VLOG_LEVEL) << "String relation extraction starts at root";
  visit(root_);
  end();
}

void StringRelationGenerator::end() {
}

void StringRelationGenerator::visitScript(Script_ptr script) {
  symbol_table_->push_scope(script);
  visit_children_of(script);
  symbol_table_->pop_scope();
}

void StringRelationGenerator::visitCommand(Command_ptr command) {

}

void StringRelationGenerator::visitAssert(Assert_ptr assert_command) {
  current_term_ = assert_command->term;
  visit_children_of(assert_command);
}

void StringRelationGenerator::visitTerm(Term_ptr term) {
}

void StringRelationGenerator::visitExclamation(Exclamation_ptr exclamation) {
}

void StringRelationGenerator::visitExists(Exists_ptr exists_term) {
}

void StringRelationGenerator::visitForAll(ForAll_ptr for_all_term) {
}

void StringRelationGenerator::visitLet(Let_ptr let_term) {
}

void StringRelationGenerator::visitAnd(And_ptr and_term) {
  current_term_ = and_term;
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;

  //
  // clear coefficient maps at the end of possible component
  current_trackmap_ = std::shared_ptr<std::map<std::string,int>>(new std::map<std::string,int>);
}

void StringRelationGenerator::visitOr(Or_ptr or_term) {
  current_term_ = or_term;
  for (auto &term : *(or_term->term_list)) {
    visit(term);
  }
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
}

void StringRelationGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  // implement here
}

void StringRelationGenerator::visitUMinus(UMinus_ptr uminus_term) {
}

void StringRelationGenerator::visitMinus(Minus_ptr minus_term) {
}

void StringRelationGenerator::visitPlus(Plus_ptr plus_term) {
}

void StringRelationGenerator::visitTimes(Times_ptr times_term) {
}

void StringRelationGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(eq_term->left_term);
  right_relation = get_term_relation(eq_term->right_term);

  if (left_relation not_eq nullptr and right_relation not_eq nullptr) {
    StringRelation::Subrelation left_subrelation = left_relation->get_subrelation_list()[0];
    StringRelation::Subrelation right_subrelation = right_relation->get_subrelation_list()[0];
    StringRelation::Subrelation subrelation;
    subrelation.type = StringRelation::Type::EQ;
    subrelation.names = left_subrelation.names;
    subrelation.names.insert(subrelation.names.end(), right_subrelation.names.begin(), right_subrelation.names.end());

    relation = new StringRelation();
    relation->set_type(StringRelation::Type::EQ);
    relation->add_subrelation(subrelation);
    relation->set_variable_track_map(left_relation->get_variable_track_map());
    relation->set_num_tracks(left_relation->get_num_tracks());

    if (left_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table_->getVariable(left_subrelation.names[0]);
      if (current_trackmap_->find(var->getName()) == current_trackmap_->end()) {
        int track = current_trackmap_->size();
        (*current_trackmap_)[var->getName()] = track;
      }
    }
    if (right_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table_->getVariable(right_subrelation.names[0]);
      if (current_trackmap_->find(var->getName()) == current_trackmap_->end()) {
        int track = current_trackmap_->size();
        (*current_trackmap_)[var->getName()] = track;
      }
    }

    delete_term_relation(eq_term->left_term);
    delete_term_relation(eq_term->right_term);
    set_term_relation(eq_term, relation);
  }
}

void StringRelationGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(not_eq_term->left_term);
  right_relation = get_term_relation(not_eq_term->right_term);

  if (left_relation not_eq nullptr and right_relation not_eq nullptr) {
    StringRelation::Subrelation left_subrelation = left_relation->get_subrelation_list()[0];
    StringRelation::Subrelation right_subrelation = right_relation->get_subrelation_list()[0];
    StringRelation::Subrelation subrelation;
    subrelation.type = StringRelation::Type::NOTEQ;
    subrelation.names = left_subrelation.names;
    subrelation.names.insert(subrelation.names.end(), right_subrelation.names.begin(), right_subrelation.names.end());

    relation = new StringRelation();
    relation->set_type(StringRelation::Type::NOTEQ);
    relation->add_subrelation(subrelation);
    relation->set_variable_track_map(left_relation->get_variable_track_map());  // TODO: Make better
    relation->set_num_tracks(left_relation->get_num_tracks());

    if (left_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table_->getVariable(left_subrelation.names[0]);
      if (current_trackmap_->find(var->getName()) == current_trackmap_->end()) {
        int track = current_trackmap_->size();
        (*current_trackmap_)[var->getName()] = track;
      }
    }
    if (right_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table_->getVariable(right_subrelation.names[0]);
      if (current_trackmap_->find(var->getName()) == current_trackmap_->end()) {
        int track = current_trackmap_->size();
        (*current_trackmap_)[var->getName()] = track;
      }
    }

    delete_term_relation(not_eq_term->left_term);
    delete_term_relation(not_eq_term->right_term);
    set_term_relation(not_eq_term, relation);
  }
}

void StringRelationGenerator::visitGt(Gt_ptr gt_term) {
}

void StringRelationGenerator::visitGe(Ge_ptr ge_term) {
}

void StringRelationGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(lt_term->left_term);
  right_relation = get_term_relation(lt_term->right_term);

  if (left_relation not_eq nullptr and right_relation not_eq nullptr) {
    StringRelation::Subrelation left_subrelation = left_relation->get_subrelation_list()[0];
    StringRelation::Subrelation right_subrelation = right_relation->get_subrelation_list()[0];
    StringRelation::Subrelation subrelation;
    subrelation.type = StringRelation::Type::LT;
    subrelation.names = left_subrelation.names;
    subrelation.names.insert(subrelation.names.end(), right_subrelation.names.begin(), right_subrelation.names.end());

    relation = new StringRelation();
    relation->set_type(StringRelation::Type::LT);
    relation->add_subrelation(subrelation);
    relation->set_variable_track_map(left_relation->get_variable_track_map());
    relation->set_num_tracks(left_relation->get_num_tracks());

    if (left_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table_->getVariable(left_subrelation.names[0]);
      if (current_trackmap_->find(var->getName()) == current_trackmap_->end()) {
        int track = current_trackmap_->size();
        (*current_trackmap_)[var->getName()] = track;
      }
    }
    if (right_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table_->getVariable(right_subrelation.names[0]);
      if (current_trackmap_->find(var->getName()) == current_trackmap_->end()) {
        int track = current_trackmap_->size();
        (*current_trackmap_)[var->getName()] = track;
      }
    }

    delete_term_relation(lt_term->left_term);
    delete_term_relation(lt_term->right_term);
    set_term_relation(lt_term, relation);
  }
}

void StringRelationGenerator::visitLe(Le_ptr le_term) {
}

void StringRelationGenerator::visitConcat(Concat_ptr concat_term) {
}

void StringRelationGenerator::visitIn(In_ptr in_term) {
  // implement
}

void StringRelationGenerator::visitNotIn(NotIn_ptr not_in_term) {
  // implement
}

void StringRelationGenerator::visitLen(Len_ptr len_term) {
  // implement
}

void StringRelationGenerator::visitContains(Contains_ptr contains_term) {
  // implement
}

void StringRelationGenerator::visitNotContains(NotContains_ptr not_contains_term) {
  // implement
}

void StringRelationGenerator::visitBegins(Begins_ptr begins_term) {
  // implement
}

void StringRelationGenerator::visitNotBegins(NotBegins_ptr not_begins_term) {
  // implement
}

void StringRelationGenerator::visitEnds(Ends_ptr ends_term) {
  // implement
}

void StringRelationGenerator::visitNotEnds(NotEnds_ptr not_ends_term) {
  // implement
}

void StringRelationGenerator::visitIndexOf(IndexOf_ptr index_of_term) {
  // implement
}

void StringRelationGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  // implement
}

void StringRelationGenerator::visitCharAt(CharAt_ptr char_at_term) {
  // implement
}

void StringRelationGenerator::visitSubString(SubString_ptr sub_string_term) {
  // implement
}

void StringRelationGenerator::visitToUpper(ToUpper_ptr to_upper_term) {
  // implement
}

void StringRelationGenerator::visitToLower(ToLower_ptr to_lower_term) {
  // implement
}

void StringRelationGenerator::visitTrim(Trim_ptr trim_term) {
  // implement
}

void StringRelationGenerator::visitToString(ToString_ptr to_string_term) {
}

void StringRelationGenerator::visitToInt(ToInt_ptr to_int_term) {
}

void StringRelationGenerator::visitReplace(Replace_ptr replace_term) {
  // implement
}

void StringRelationGenerator::visitCount(Count_ptr count_term) {
  // implement
}

void StringRelationGenerator::visitIte(Ite_ptr ite_term) {
  // implement
}

void StringRelationGenerator::visitReConcat(ReConcat_ptr reconcat_term) {
  // implement
}

void StringRelationGenerator::visitReUnion(ReUnion_ptr re_union_term) {
}

void StringRelationGenerator::visitReInter(ReInter_ptr re_inter_term) {
}

void StringRelationGenerator::visitReStar(ReStar_ptr re_star_term) {
}

void StringRelationGenerator::visitRePlus(RePlus_ptr re_plus_term) {
}

void StringRelationGenerator::visitReOpt(ReOpt_ptr re_opt_term) {
}

void StringRelationGenerator::visitToRegex(ToRegex_ptr to_regex_term) {
  // implement
}

void StringRelationGenerator::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void StringRelationGenerator::visitAsQualIdentifier(AsQualIdentifier_ptr as_qual_id_term) {
}

void StringRelationGenerator::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  StringRelation_ptr str_rel = nullptr;
  Variable_ptr variable = symbol_table_->getVariable(qi_term->getVarName());
  set_parent_term(variable, current_term_);

  if (Variable::Type::STRING == variable->getType()) {
    StringRelation::Subrelation subrel;
    subrel.type = StringRelation::Type::VAR;
    subrel.names = std::vector<std::string>(1, variable->getName());
    str_rel = new StringRelation();
    str_rel->set_type(StringRelation::Type::VAR);
    str_rel->set_variable_track_map(current_trackmap_);
    str_rel->add_subrelation(subrel);
  }
  set_term_relation(qi_term, str_rel);
}

void StringRelationGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  StringRelation_ptr str_rel = nullptr;
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;
  StringRelation::Subrelation subrel;
  subrel.type = StringRelation::Type::CONSTANT;
  subrel.names = std::vector<std::string>(1, term_constant->getValue());
  str_rel = new StringRelation();
  str_rel->set_type(StringRelation::Type::CONSTANT);
  str_rel->add_subrelation(subrel);

  set_term_relation(term_constant, str_rel);
}

void StringRelationGenerator::visitSort(Sort_ptr sort_term) {
}

void StringRelationGenerator::visitTVariable(TVariable_ptr tvar_term) {
}

void StringRelationGenerator::visitTBool(TBool_ptr tbool_term) {
}

void StringRelationGenerator::visitTInt(TInt_ptr tint_term) {
}

void StringRelationGenerator::visitTString(TString_ptr tstring_term) {
}

void StringRelationGenerator::visitAttribute(Attribute_ptr tattr_term) {
}

void StringRelationGenerator::visitSortedVar(SortedVar_ptr sorted_var_term) {
}

void StringRelationGenerator::visitVarBinding(VarBinding_ptr var_binding_term) {
}

void StringRelationGenerator::visitIdentifier(Identifier_ptr id_term) {
}

void StringRelationGenerator::visitPrimitive(Primitive_ptr prim_term) {
}

void StringRelationGenerator::visitVariable(Variable_ptr var_term) {
}

StringRelation_ptr StringRelationGenerator::get_term_relation(Term_ptr term) {
  auto iter = relations_.find(term);
  if (iter == relations_.end()) {
    return nullptr;
  }
  return iter->second;
}

bool StringRelationGenerator::set_term_relation(Term_ptr term, Theory::StringRelation_ptr str_rel) {
  auto result = relations_.insert(std::make_pair(term, str_rel));
  if (result.second == false) {
    LOG(FATAL)<< "relation is already computed for term: " << *term;
  }
  return result.second;
}

void StringRelationGenerator::delete_term_relation(Term_ptr term) {
  auto relation = get_term_relation(term);
  if (relation not_eq nullptr) {
    delete relation;
    relations_.erase(term);
  }
}

Term_ptr StringRelationGenerator::get_parent_term(Variable_ptr variable) {
  auto it = variable_term_map_.find(variable);
  if (it != variable_term_map_.end()) {
    return nullptr;
  }
  return variable_term_map_[variable];
}

bool StringRelationGenerator::set_parent_term(Variable_ptr variable, Term_ptr term) {
  variable_term_map_[variable] = term;
  return true;
}

void StringRelationGenerator::reset_variable_trackmap() {
  current_trackmap_->clear();
}

} /* namespace Solver */
} /* namespace Vlab */
