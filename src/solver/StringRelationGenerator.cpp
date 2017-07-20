//
// Created by will on 3/4/16.
//

#include "StringRelationGenerator.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringRelationGenerator::VLOG_LEVEL = 14;

StringRelationGenerator::StringRelationGenerator(Script_ptr script, SymbolTable_ptr symbol_table, ConstraintInformation_ptr constraint_information)
    : root_(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      has_string_formula_{false},
      has_mixed_constraint_(false),
      current_term_{nullptr} {
}

StringRelationGenerator::~StringRelationGenerator() {
  for(auto it = relations_.cbegin(); it != relations_.cend();) {
    if(relations_[it->first] != nullptr) {
      delete relations_[it->first];
      relations_[it->first] = nullptr;
    }
    it++;
  }
}

void StringRelationGenerator::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "String relation extraction starts at node: " << node;
  has_string_formula_ = false;
  has_mixed_constraint_ = false;
  visit(node);
  set_group_mappings();
  end();
}

void StringRelationGenerator::start() {
  DVLOG(VLOG_LEVEL) << "String relation extraction starts at root";
  has_string_formula_ = false;
  has_mixed_constraint_ = false;
  visit(root_);
  set_group_mappings();
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
  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;
  current_term_ = and_term;
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

  if (not constraint_information_->is_component(and_term)) {
  current_term_ = nullptr;
    return;
  }
  DVLOG(VLOG_LEVEL) << "post visit start: " << *and_term << "@" << and_term;

  StringRelation_ptr term_relation = nullptr;
  for (auto& term : *(and_term->term_list)) {
    term_relation = get_term_relation(term);
    if(term_relation != nullptr) {
      if(term->type() == Term::Type::QUALIDENTIFIER) {
        delete_term_relation(term);
        continue;
      }
      std::string group_name = get_variable_group_name(current_term_,symbol_table_->get_variable(term_relation->variables[0]));
      term_group_map[term] = group_name;
      VariableTrackMap trackmap = get_group_trackmap(group_name);
      term_relation->set_variable_trackmap(trackmap);
      if(symbol_table_->get_variable_unsafe(group_name) == nullptr) {
        symbol_table_->add_variable(new Variable(group_name,Variable::Type::NONE));
        symbol_table_->set_value(group_name,new Value(MultiTrackAutomaton::makeAnyAutoAligned(trackmap.size())));
      }
      has_string_formula_ = true;
    } else {
      has_mixed_constraint_ = true;
    }
  }

  if(has_string_formula_) {
    constraint_information_->add_string_constraint(and_term);
  }
  if(has_mixed_constraint_) {
    constraint_information_->add_mixed_constraint(and_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *and_term << "@" << and_term;
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
  if ((left_relation == nullptr || right_relation == nullptr)
      || (eq_term->left_term->type() != Term::Type::QUALIDENTIFIER
          && eq_term->right_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(eq_term->left_term);
    delete_term_relation(eq_term->right_term);
    set_term_relation(eq_term, nullptr);
    return;
  } else if (eq_term->left_term->type() == Term::Type::TERMCONSTANT) {
    DVLOG(VLOG_LEVEL) << "--- Left constant => no multitrack";
    delete_term_relation(eq_term->left_term);
    delete_term_relation(eq_term->right_term);
    set_term_relation(eq_term,nullptr);
    return;
  } else if (eq_term->right_term->type() == Term::Type::TERMCONSTANT) {
    DVLOG(VLOG_LEVEL) << "--- Right constant => no multitrack";
    delete_term_relation(eq_term->left_term);
    delete_term_relation(eq_term->right_term);
    set_term_relation(eq_term,nullptr);
    return;
  }

  relation = new StringRelation(StringRelation::Type::EQ,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  if (left_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
    vars.push_back(var->getName());
  } else if(left_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_data());
    vars.push_back(var->getName());
  } else if(right_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }
  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(eq_term->left_term);
  delete_term_relation(eq_term->right_term);
  set_term_relation(eq_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(eq_term);
}

void StringRelationGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(not_eq_term->left_term);
  right_relation = get_term_relation(not_eq_term->right_term);

  if ((left_relation == nullptr || right_relation == nullptr)
      || (not_eq_term->left_term->type() != Term::Type::QUALIDENTIFIER
          && not_eq_term->right_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(not_eq_term->left_term);
    delete_term_relation(not_eq_term->right_term);
    set_term_relation(not_eq_term, nullptr);
    return;
  } else if (not_eq_term->left_term->type() == Term::Type::TERMCONSTANT) {
    DVLOG(VLOG_LEVEL) << "--- Left constant => no multitrack";
    delete_term_relation(not_eq_term->left_term);
    delete_term_relation(not_eq_term->right_term);
    set_term_relation(not_eq_term,nullptr);
    return;
  } else if (not_eq_term->right_term->type() == Term::Type::TERMCONSTANT) {
    DVLOG(VLOG_LEVEL) << "--- Right constant => no multitrack";
    delete_term_relation(not_eq_term->left_term);
    delete_term_relation(not_eq_term->right_term);
    set_term_relation(not_eq_term,nullptr);
    return;
  }

  relation = new StringRelation(StringRelation::Type::NOTEQ,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  if (left_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
    vars.push_back(var->getName());
  } else if(left_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_data());
    vars.push_back(var->getName());
  } else if(right_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }
  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(not_eq_term->left_term);
  delete_term_relation(not_eq_term->right_term);
  set_term_relation(not_eq_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(not_eq_term);
}

void StringRelationGenerator::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(gt_term->left_term);
  right_relation = get_term_relation(gt_term->right_term);
  if ((left_relation == nullptr || right_relation == nullptr)
      || (gt_term->left_term->type() != Term::Type::QUALIDENTIFIER
          && gt_term->right_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(gt_term->left_term);
    delete_term_relation(gt_term->right_term);
    set_term_relation(gt_term, nullptr);
    return;
  }
  relation = new StringRelation(StringRelation::Type::GT,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  if (left_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
    vars.push_back(var->getName());
  } else if(left_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_data());
    vars.push_back(var->getName());
  } else if(right_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }
  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(gt_term->left_term);
  delete_term_relation(gt_term->right_term);
  set_term_relation(gt_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(gt_term);
}

void StringRelationGenerator::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(ge_term->left_term);
  right_relation = get_term_relation(ge_term->right_term);
  if ((left_relation == nullptr || right_relation == nullptr)
      || (ge_term->left_term->type() != Term::Type::QUALIDENTIFIER
          && ge_term->right_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(ge_term->left_term);
    delete_term_relation(ge_term->right_term);
    set_term_relation(ge_term, nullptr);
    return;
  }
  relation = new StringRelation(StringRelation::Type::GE,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  if (left_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
    vars.push_back(var->getName());
  } else if(left_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_data());
    vars.push_back(var->getName());
  } else if(right_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }
  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(ge_term->left_term);
  delete_term_relation(ge_term->right_term);
  set_term_relation(ge_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(ge_term);
}

void StringRelationGenerator::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(lt_term->left_term);
  right_relation = get_term_relation(lt_term->right_term);
  if ((left_relation == nullptr || right_relation == nullptr)
      || (lt_term->left_term->type() != Term::Type::QUALIDENTIFIER
          && lt_term->right_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(lt_term->left_term);
    delete_term_relation(lt_term->right_term);
    set_term_relation(lt_term, nullptr);
    return;
  }
  relation = new StringRelation(StringRelation::Type::LT,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  if (left_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
    vars.push_back(var->getName());
  } else if(left_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_data());
    vars.push_back(var->getName());
  } else if(right_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }
  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(lt_term->left_term);
  delete_term_relation(lt_term->right_term);
  set_term_relation(lt_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(lt_term);
}

void StringRelationGenerator::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(le_term->left_term);
  right_relation = get_term_relation(le_term->right_term);
  if ((left_relation == nullptr || right_relation == nullptr)
      || (le_term->left_term->type() == Term::Type::TERMCONSTANT
          && le_term->right_term->type() == Term::Type::TERMCONSTANT)
      || (le_term->left_term->type() == Term::Type::CONCAT
          && le_term->right_term->type() == Term::Type::CONCAT)) {
    delete_term_relation(le_term->left_term);
    delete_term_relation(le_term->right_term);
    set_term_relation(le_term, nullptr);
    return;
  }
  relation = new StringRelation(StringRelation::Type::LE,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  if (left_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
    vars.push_back(var->getName());
  } else if(left_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(left_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }

  if (right_relation->get_type() == StringRelation::Type::STRING_VAR) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_data());
    vars.push_back(var->getName());
  } else if(right_relation->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
    Variable_ptr var = symbol_table_->get_variable(right_relation->get_left()->get_data());
    vars.push_back(var->getName());
  }
  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(le_term->left_term);
  delete_term_relation(le_term->right_term);
  set_term_relation(le_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(le_term);
}

void StringRelationGenerator::visitConcat(Concat_ptr concat_term) {

  visit_children_of(concat_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *concat_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  if(concat_term->term_list->size() != 2)
    return;

  left_relation = get_term_relation(concat_term->term_list->at(0));
  right_relation = get_term_relation(concat_term->term_list->at(1));
  if ((left_relation == nullptr || right_relation == nullptr)
        || (concat_term->term_list->at(0)->type() != Term::Type::QUALIDENTIFIER
            || concat_term->term_list->at(1)->type() != Term::Type::TERMCONSTANT)) {
    delete_term_relation(concat_term->term_list->at(0));
    delete_term_relation(concat_term->term_list->at(1));
    set_term_relation(concat_term,nullptr);
    return;
  }

  relation = new StringRelation(StringRelation::Type::CONCAT_VAR_CONSTANT,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  delete_term_relation(concat_term->term_list->at(0));
  delete_term_relation(concat_term->term_list->at(1));
  set_term_relation(concat_term, relation);
  has_string_formula_ = true;
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
  has_mixed_constraint_ = true;
  has_string_formula_ = false;
}

void StringRelationGenerator::visitNotContains(NotContains_ptr not_contains_term) {
  has_mixed_constraint_ = true;
  has_string_formula_ = false;
}

void StringRelationGenerator::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *begins_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(begins_term->subject_term);
  right_relation = get_term_relation(begins_term->search_term);
  if ((left_relation == nullptr || right_relation == nullptr)
        || (begins_term->subject_term->type() != Term::Type::QUALIDENTIFIER
            || begins_term->search_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(begins_term->subject_term);
    delete_term_relation(begins_term->search_term);
    set_term_relation(begins_term,nullptr);
    return;
  }
  relation = new StringRelation(StringRelation::Type::BEGINS,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());

  std::vector<std::string> vars;
  Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
  vars.push_back(var->getName());
  var = symbol_table_->get_variable(right_relation->get_data());
  vars.push_back(var->getName());

  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(begins_term->subject_term);
  delete_term_relation(begins_term->search_term);
  set_term_relation(begins_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(begins_term);
}

void StringRelationGenerator::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_begins_term;

  StringRelation_ptr left_relation = nullptr, right_relation = nullptr, relation = nullptr;
  left_relation = get_term_relation(not_begins_term->subject_term);
  right_relation = get_term_relation(not_begins_term->search_term);
  if ((left_relation == nullptr || right_relation == nullptr)
        || (not_begins_term->subject_term->type() != Term::Type::QUALIDENTIFIER
            || not_begins_term->search_term->type() != Term::Type::QUALIDENTIFIER)) {
    delete_term_relation(not_begins_term->subject_term);
    delete_term_relation(not_begins_term->search_term);
    set_term_relation(not_begins_term,nullptr);
    return;
  }
  relation = new StringRelation(StringRelation::Type::NOTBEGINS,
                                left_relation->clone(),
                                right_relation->clone(),
                                "",
                                VariableTrackMap());
  std::vector<std::string> vars;
  Variable_ptr var = symbol_table_->get_variable(left_relation->get_data());
  vars.push_back(var->getName());
  var = symbol_table_->get_variable(right_relation->get_data());
  vars.push_back(var->getName());

  relation->variables = vars;
  add_string_variables(current_term_,vars);

  delete_term_relation(not_begins_term->subject_term);
  delete_term_relation(not_begins_term->search_term);
  set_term_relation(not_begins_term, relation);
  has_string_formula_ = true;
  constraint_information_->add_string_constraint(not_begins_term);
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
  Variable_ptr variable = symbol_table_->get_variable(qi_term->getVarName());
  DVLOG(VLOG_LEVEL) << "-->variable name: " << variable->getName();
  switch(variable->getType()) {
    case Variable::Type::STRING:
      str_rel = new StringRelation(StringRelation::Type::STRING_VAR,
                                  nullptr,
                                  nullptr,
                                  variable->getName(),
                                  VariableTrackMap());
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
  DVLOG(VLOG_LEVEL) << "-->term constant: " << term_constant->getValue();
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

bool StringRelationGenerator::has_string_formula() {
  return has_string_formula_;
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

std::string StringRelationGenerator::get_variable_group_name(Term_ptr term,Variable_ptr variable) {
  std::string var_name = variable->getName();
  if(variable_group_table_[term].find(var_name) == variable_group_table_[term].end()) {
    DVLOG(VLOG_LEVEL) << var_name << " has no group";
    return "";
  }
  return variable_group_table_[term][var_name];
}

std::string StringRelationGenerator::get_term_group_name(SMT::Term_ptr term) {
  if(term_group_map.find(term) == term_group_map.end()) {
    return "";
  }
  return term_group_map[term];
}

void StringRelationGenerator::add_string_variables(Term_ptr term, std::vector<std::string> variables) {
  if (Option::Solver::ENABLE_DEPENDENCY_ANALYSIS) {
    std::string start_group;
    // get a starting group from the variable list
    for (auto &var : variables) {
      if (variable_group_table_[term].find(var) != variable_group_table_[term].end()) {
        start_group = variable_group_table_[term][var];
        break;
      }
    }
    // if no group is found at all, create new one
    if (start_group.empty()) {
      start_group = generate_group_name(term, variables[0]);
    }

    // merge each variable's groups together into start_group
    for (auto &var : variables) {
      if (variable_group_table_[term].find(var) == variable_group_table_[term].end()) {
        variable_group_table_[term][var] = start_group;
        int track = group_variables_map_[start_group].size();
        group_variables_map_[start_group][var] = track;
      } else if (variable_group_table_[term][var] != start_group) {
        // merge the two groups
        std::string var_group = variable_group_table_[term][var];
        for (auto &iter : group_variables_map_[var_group]) {
          variable_group_table_[term][iter.first] = start_group;
          int track = group_variables_map_[start_group].size();
          group_variables_map_[start_group][iter.first] = track;
        }
        group_variables_map_.erase(var_group);
      }
    }
  } else {
    std::string start_group = "BAIL";
    for(auto& var : variables) {
      if(variable_group_table_[term].find(var) == variable_group_table_[term].end()) {
        variable_group_table_[term][var] = start_group;
        int track = group_variables_map_[start_group].size();
        group_variables_map_[start_group][var] = track;
      }
    }
  }
}

std::string StringRelationGenerator::generate_group_name(SMT::Term_ptr term, std::string var_name) {
  std::string group_name = symbol_table_->get_var_name_for_node(term,SMT::Variable::Type::STRING);
  group_name += var_name;
  return group_name;
}

void StringRelationGenerator::set_group_mappings() {
  for (const auto& mel : variable_group_table_) {
    for (const auto& el : mel.second) {
      symbol_table_->add_variable_group_mapping(el.first, el.second);
    }
  }
}

VariableTrackMap StringRelationGenerator::get_group_trackmap(std::string name) {
  if(group_variables_map_.find(name) == group_variables_map_.end()) {
    DVLOG(VLOG_LEVEL) << "no trackmap for group: " << name;
    return VariableTrackMap();
  }
  return group_variables_map_[name];
}

} /* namespace Solver */
} /* namespace Vlab */
