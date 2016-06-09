//
// Created by will on 3/4/16.
//

#include "StringRelationGenerator.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringRelationGenerator::VLOG_LEVEL = 14;

StringRelationGenerator::StringRelationGenerator(Script_ptr script, SymbolTable_ptr st)
  : root(script), symbol_table(st) {
  current_term = nullptr;
}

StringRelationGenerator::~StringRelationGenerator() {
  // delete var track map ptr?
}

void StringRelationGenerator::start() {
  DVLOG(VLOG_LEVEL) << "String relation extraction starts";
  visit(root);
  end();
}

void StringRelationGenerator::end() {
}

void StringRelationGenerator::visitScript(Script_ptr script) {
  symbol_table->push_scope(script);
  visit_children_of(script);
  symbol_table->pop_scope();
}

void StringRelationGenerator::visitCommand(Command_ptr command) {

}

void StringRelationGenerator::visitAssert(Assert_ptr assert_command) {
  current_term = assert_command->term;
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
  current_term = and_term;
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
}

void StringRelationGenerator::visitOr(Or_ptr or_term) {
  current_term = or_term;
  for (auto &term : *(or_term->term_list)) {
    visit(term);
  }
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
}

void StringRelationGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  // do shit here
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
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr,
                     relation = nullptr;
  left_relation = get_term_relation(eq_term->left_term);
  right_relation = get_term_relation(eq_term->right_term);

  if(left_relation not_eq nullptr and right_relation not_eq nullptr) {
    StringRelation::Subrelation left_subrelation = left_relation->get_subrelation_list()[0];
    StringRelation::Subrelation right_subrelation = right_relation->get_subrelation_list()[0];
    StringRelation::Subrelation subrelation;
    subrelation.type = StringRelation::Type::EQ;
    subrelation.names = left_subrelation.names;
    subrelation.names.insert(subrelation.names.end(),right_subrelation.names.begin(),right_subrelation.names.end());

    relation = new StringRelation();
    relation->set_type(StringRelation::Type::EQ);
    relation->add_subrelation(subrelation);
    relation->set_variable_track_map(left_relation->get_variable_track_map()); // TODO: Make better
    relation->set_num_tracks(left_relation->get_num_tracks());

    std::map<std::string,int> *var_map = nullptr;
    if(left_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table->getVariable(left_subrelation.names[0]);
      var_map = &component_trackmaps[var->component];
      if(var_map->find(var->getName()) == var_map->end()) {
        int track = var_map->size();
        (*var_map)[var->getName()] = track;
      }
    }
    if(right_subrelation.type == StringRelation::Type::VAR) {
      Variable_ptr var = symbol_table->getVariable(right_subrelation.names[0]);
      var_map = &component_trackmaps[var->component];
      if(var_map->find(var->getName()) == var_map->end()) {
        int track = var_map->size();
        (*var_map)[var->getName()] = track;
      }
    }

    delete_term_relation(eq_term->left_term);
    delete_term_relation(eq_term->right_term);
    set_term_relation(eq_term,relation);
  }
}

void StringRelationGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr,
                     relation = nullptr;
  left_relation = get_term_relation(not_eq_term->left_term);
  right_relation = get_term_relation(not_eq_term->right_term);

  if(left_relation not_eq nullptr and right_relation not_eq nullptr) {
    StringRelation::Subrelation left_subrelation = left_relation->get_subrelation_list()[0];
    StringRelation::Subrelation right_subrelation = right_relation->get_subrelation_list()[0];
    StringRelation::Subrelation subrelation;
    subrelation.type = StringRelation::Type::NOTEQ;
    subrelation.names = left_subrelation.names;
    subrelation.names.insert(subrelation.names.end(),right_subrelation.names.begin(),right_subrelation.names.end());

    relation = new StringRelation();
    relation->set_type(StringRelation::Type::NOTEQ);
    relation->add_subrelation(subrelation);
    relation->set_variable_track_map(left_relation->get_variable_track_map()); // TODO: Make better
    relation->set_num_tracks(left_relation->get_num_tracks());

    std::map<std::string,int> *var_map = nullptr;
      if(left_subrelation.type == StringRelation::Type::VAR) {
        Variable_ptr var = symbol_table->getVariable(left_subrelation.names[0]);
        var_map = &component_trackmaps[var->component];
        if(var_map->find(var->getName()) == var_map->end()) {
          int track = var_map->size();
          (*var_map)[var->getName()] = track;
        }
      }
      if(right_subrelation.type == StringRelation::Type::VAR) {
        Variable_ptr var = symbol_table->getVariable(right_subrelation.names[0]);
        var_map = &component_trackmaps[var->component];
        if(var_map->find(var->getName()) == var_map->end()) {
          int track = var_map->size();
          (*var_map)[var->getName()] = track;
        }
      }


    delete_term_relation(not_eq_term->left_term);
    delete_term_relation(not_eq_term->right_term);
    set_term_relation(not_eq_term,relation);
  }
}

void StringRelationGenerator::visitGt(Gt_ptr gt_term) {
}

void StringRelationGenerator::visitGe(Ge_ptr ge_term) {
}

void StringRelationGenerator::visitLt(Lt_ptr lt_term) {
}

void StringRelationGenerator::visitLe(Le_ptr le_term) {
}

void StringRelationGenerator::visitConcat(Concat_ptr concat_term) {
}

void StringRelationGenerator::visitIn(In_ptr in_term) {
  // do shit
}

void StringRelationGenerator::visitNotIn(NotIn_ptr not_in_term) {
  // do shit
}

void StringRelationGenerator::visitLen(Len_ptr len_term) {
  // do shit
}

void StringRelationGenerator::visitContains(Contains_ptr contains_term) {
  // do shit
}

void StringRelationGenerator::visitNotContains(NotContains_ptr not_contains_term) {
  // do shit
}

void StringRelationGenerator::visitBegins(Begins_ptr begins_term) {
  // do shit
}

void StringRelationGenerator::visitNotBegins(NotBegins_ptr not_begins_term) {
  // do shit
}

void StringRelationGenerator::visitEnds(Ends_ptr ends_term) {
  // do shit
}

void StringRelationGenerator::visitNotEnds(NotEnds_ptr not_ends_term) {
  // do shit
}

void StringRelationGenerator::visitIndexOf(IndexOf_ptr index_of_term) {
  // do shit
}

void StringRelationGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  // do shit
}

void StringRelationGenerator::visitCharAt(CharAt_ptr char_at_term) {
  // do shit
}

void StringRelationGenerator::visitSubString(SubString_ptr sub_string_term) {
  // do shit
}

void StringRelationGenerator::visitToUpper(ToUpper_ptr to_upper_term) {
  // do shit
}

void StringRelationGenerator::visitToLower(ToLower_ptr to_lower_term) {
  // do shit
}

void StringRelationGenerator::visitTrim(Trim_ptr trim_term) {
  // do shit
}

void StringRelationGenerator::visitToString(ToString_ptr to_string_term) {
}

void StringRelationGenerator::visitToInt(ToInt_ptr to_int_term) {
}

void StringRelationGenerator::visitReplace(Replace_ptr replace_term) {
  // do shit
}

void StringRelationGenerator::visitCount(Count_ptr count_term) {
  // do shit
}

void StringRelationGenerator::visitIte(Ite_ptr ite_term) {
  // do shit
}

void StringRelationGenerator::visitReConcat(ReConcat_ptr reconcat_term) {
  // do shit
}

void StringRelationGenerator::visitToRegex(ToRegex_ptr to_regex_term) {
  // do shit
}

void StringRelationGenerator::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void StringRelationGenerator::visitAsQualIdentifier(AsQualIdentifier_ptr as_qual_id_term) {
}

void StringRelationGenerator::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;

  Component_ptr var_component = nullptr;
  StringRelation_ptr str_rel = nullptr;
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());
  set_parent_term(variable,current_term);
  var_component = variable->component;

  if(var_component == nullptr) {
    LOG(ERROR) << "StringRelationGenerator: variable has no component...";
  }
  if(component_trackmaps.find(var_component) == component_trackmaps.end()) {
    component_trackmaps[var_component] = std::map<std::string,int>();
  }

  if (Variable::Type::STRING == variable->getType()) {
    StringRelation::Subrelation subrel;
    subrel.type = StringRelation::Type::VAR;
    subrel.names = std::vector<std::string>(1,variable->getName());
    str_rel = new StringRelation();
    str_rel->set_type(StringRelation::Type::VAR);
    str_rel->add_subrelation(subrel);
    str_rel->set_variable_track_map(&component_trackmaps[var_component]);
  }
  set_term_relation(qi_term,str_rel);
}

void StringRelationGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  StringRelation_ptr str_rel = nullptr;
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;
  StringRelation::Subrelation subrel;
  subrel.type = StringRelation::Type::CONSTANT;
  subrel.names = std::vector<std::string>(1,term_constant->getValue());
  str_rel = new StringRelation();
  str_rel->set_type(StringRelation::Type::CONSTANT);
  str_rel->add_subrelation(subrel);

  set_term_relation(term_constant,str_rel);
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
  auto iter = relations.find(term);
  if(iter == relations.end()) {
    return nullptr;
  }
  return iter->second;
}

bool StringRelationGenerator::set_term_relation(Term_ptr term, Theory::StringRelation_ptr str_rel) {
  auto result = relations.insert(std::make_pair(term,str_rel));
  if(result.second == false) {
    LOG(FATAL) << "relation is already computed for term: " << *term;
  }
  return result.second;
}

void StringRelationGenerator::delete_term_relation(Term_ptr term) {
  auto relation = get_term_relation(term);
  if(relation not_eq nullptr) {
    delete relation;
    relations.erase(term);
  }
}

Term_ptr StringRelationGenerator::get_parent_term(Variable_ptr variable) {
  auto it = variable_term_map.find(variable);
  if (it != variable_term_map.end()) {
    return nullptr;
  }
  return variable_term_map[variable];
}

bool StringRelationGenerator::set_parent_term(Variable_ptr variable, Term_ptr term) {
  variable_term_map[variable] = term;
  return true;
}

} /* namespace Solver */
} /* namespace Vlab */