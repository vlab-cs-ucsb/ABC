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

StringRelationGenerator::StringRelationGenerator(Script_ptr script, SymbolTable_ptr symbol_table, ConstraintInformation_ptr constraint_information)
    : root_(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information) {
  current_term_ = nullptr;
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
  visit_children_of(script);
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

  if (not constraint_information_->is_component(and_term)) {
    return;
  }

  StringRelation_ptr term_relation = nullptr;
  VariableTrackMap_ptr current_trackmap = get_term_trackmap(current_term_);
  for (auto& term : *(and_term->term_list)) {
    term_relation = get_term_relation(term);
    if(term_relation != nullptr) {
      term_relation->set_variable_trackmap(current_trackmap);
    }
  }
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
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(eq_term->left_term);
  right_relation = get_term_relation(eq_term->right_term);
  if (left_relation == nullptr || right_relation == nullptr) {
    return;
  }

  relation = new StringRelation(StringRelation::Type::EQ,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                nullptr);

  if (left_relation->get_type() == StringRelation::Type::STRING_VAR ||
        left_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(left_relation->get_data());
    add_string_variable(var,current_term_);
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR ||
        right_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(right_relation->get_data());
    add_string_variable(var,current_term_);
  }

  delete_term_relation(eq_term->left_term);
  delete_term_relation(eq_term->right_term);
  set_term_relation(eq_term, relation);
}

void StringRelationGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(not_eq_term->left_term);
  right_relation = get_term_relation(not_eq_term->right_term);
  if (left_relation == nullptr || right_relation == nullptr) {
    return;
  }

  relation = new StringRelation(StringRelation::Type::NOTEQ,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                nullptr);

  if (left_relation->get_type() == StringRelation::Type::STRING_VAR ||
        left_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(left_relation->get_data());
    add_string_variable(var,current_term_);
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR ||
        right_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(right_relation->get_data());
    add_string_variable(var,current_term_);
  }

  delete_term_relation(not_eq_term->left_term);
  delete_term_relation(not_eq_term->right_term);
  set_term_relation(not_eq_term, relation);
}

void StringRelationGenerator::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(gt_term->left_term);
  right_relation = get_term_relation(gt_term->right_term);
  if (left_relation == nullptr || right_relation == nullptr) {
    return;
  }

  relation = new StringRelation(StringRelation::Type::GT,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                nullptr);

  if (left_relation->get_type() == StringRelation::Type::STRING_VAR ||
        left_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(left_relation->get_data());
    add_string_variable(var,current_term_);
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR ||
        right_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(right_relation->get_data());
    add_string_variable(var,current_term_);
  }

  delete_term_relation(gt_term->left_term);
  delete_term_relation(gt_term->right_term);
  set_term_relation(gt_term, relation);
}

void StringRelationGenerator::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(ge_term->left_term);
  right_relation = get_term_relation(ge_term->right_term);
  if (left_relation == nullptr || right_relation == nullptr) {
    return;
  }

  relation = new StringRelation(StringRelation::Type::GE,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                nullptr);

  if (left_relation->get_type() == StringRelation::Type::STRING_VAR ||
        left_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(left_relation->get_data());
    add_string_variable(var,current_term_);
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR ||
        right_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(right_relation->get_data());
    add_string_variable(var,current_term_);
  }

  delete_term_relation(ge_term->left_term);
  delete_term_relation(ge_term->right_term);
  set_term_relation(ge_term, relation);
}

void StringRelationGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(lt_term->left_term);
  right_relation = get_term_relation(lt_term->right_term);
  if (left_relation == nullptr || right_relation == nullptr) {
    return;
  }

  relation = new StringRelation(StringRelation::Type::LT,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                nullptr);

  if (left_relation->get_type() == StringRelation::Type::STRING_VAR ||
        left_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(left_relation->get_data());
    add_string_variable(var,current_term_);
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR ||
        right_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(right_relation->get_data());
    add_string_variable(var,current_term_);
  }

  delete_term_relation(lt_term->left_term);
  delete_term_relation(lt_term->right_term);
  set_term_relation(lt_term, relation);
}

void StringRelationGenerator::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(le_term->left_term);
  right_relation = get_term_relation(le_term->right_term);
  if (left_relation == nullptr || right_relation == nullptr) {
    return;
  }

  relation = new StringRelation(StringRelation::Type::LE,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                nullptr);

  if (left_relation->get_type() == StringRelation::Type::STRING_VAR ||
        left_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(left_relation->get_data());
    add_string_variable(var,current_term_);
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR ||
        right_relation->get_type() == StringRelation::Type::INT_VAR) {
    Variable_ptr var = symbol_table_->getVariable(right_relation->get_data());
    add_string_variable(var,current_term_);
  }

  delete_term_relation(le_term->left_term);
  delete_term_relation(le_term->right_term);
  set_term_relation(le_term, relation);
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
  if(get_term_relation(qi_term) != nullptr) {
    return;
  }
  StringRelation_ptr str_rel = nullptr;
  Variable_ptr variable = symbol_table_->getVariable(qi_term->getVarName());
  set_parent_term(variable, current_term_);

  switch(variable->getType()) {
    case Variable::Type::STRING:
      str_rel = new StringRelation();
      str_rel->set_type(StringRelation::Type::STRING_VAR);
      str_rel->set_data(variable->getName());
      break;
    case Variable::Type::INT:
      str_rel = new StringRelation();
      str_rel->set_type(StringRelation::Type::INT_VAR);
      str_rel->set_data(variable->getName());
      break;
    default:
      break;
  }

  set_term_relation(qi_term, str_rel);
}

void StringRelationGenerator::visitTermConstant(TermConstant_ptr term_constant) {

  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;
  if(get_term_relation(term_constant) != nullptr) {
    return;
  }
  StringRelation_ptr str_rel = nullptr;
  switch(term_constant->getValueType()) {
    case Primitive::Type::STRING:
      str_rel = new StringRelation();
      str_rel->set_type(StringRelation::Type::STRING_CONSTANT);
      str_rel->set_data(term_constant->getValue());
      break;
    case Primitive::Type::REGEX:
      str_rel = new StringRelation();
      str_rel->set_type(StringRelation::Type::REGEX);
      str_rel->set_data(term_constant->getValue());
      break;
    default:
      break;
  }

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
  if (it == variable_term_map_.end()) {
    return nullptr;
  }
  return variable_term_map_[variable];
}

bool StringRelationGenerator::set_parent_term(Variable_ptr variable, Term_ptr term) {
  variable_term_map_[variable] = term;
  return true;
}

void StringRelationGenerator::add_string_variable(Variable_ptr variable, Term_ptr term) {
  int id;
  std::string variable_name = variable->getName();
  if(term_trackmap_table_.find(term) == term_trackmap_table_.end()) {
    term_trackmap_table_[term] = new std::map<std::string, int>();
  }
  id = term_trackmap_table_[term]->size();
  (*term_trackmap_table_[term])[variable_name]= id;
}

StringRelationGenerator::VariableTrackMap_ptr StringRelationGenerator::get_term_trackmap(SMT::Term_ptr term) {
  if(term_trackmap_table_.find(term) == term_trackmap_table_.end()) {
    return nullptr;
  }
  return term_trackmap_table_[term];
}

} /* namespace Solver */
} /* namespace Vlab */
