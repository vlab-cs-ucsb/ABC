//
// Created by will on 3/4/16.
//

#include "StringConstraintSolver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringConstraintSolver::VLOG_LEVEL = 13;

StringConstraintSolver::StringConstraintSolver(Script_ptr script, SymbolTable_ptr symb,
                         ConstraintInformation_ptr constraint_information)
  : AstTraverser(script), symbol_table_(symb),
    string_relation_generator_(script, symb, constraint_information),
    constraint_information_(constraint_information) {
  setCallbacks();
}


StringConstraintSolver::~StringConstraintSolver() {
}

void StringConstraintSolver::start() {
  string_relation_generator_.start(root);
  visitScript(root);
  end();
}

void StringConstraintSolver::start(SMT::Visitable_ptr node) {
  string_relation_generator_.start(node);
  this->Visitor::visit(node);
  end();
}

void StringConstraintSolver::end() {
}

void StringConstraintSolver::setCallbacks() {
  auto term_callback = [this](Term_ptr term) -> bool {

      switch (term->type()) {
        case Term::Type::EQ:
        case Term::Type::NOTEQ:
        case Term::Type::GT:
        case Term::Type::GE:
        case Term::Type::LT:
        case Term::Type::LE:
        case Term::Type::BEGINS:
        case Term::Type::NOTBEGINS: {
          DVLOG(VLOG_LEVEL) << "visit: " << *term;

          StringRelation_ptr relation = string_relation_generator_.get_term_relation(term);
          if(relation == nullptr) {
            return false;
          }
          StringRelation_ptr left = relation->get_left();
          StringRelation_ptr right = relation->get_right();
          StringRelation_ptr temp_relation = nullptr;
          MultiTrackAutomaton_ptr multi_auto = nullptr,
                                  temp_auto = nullptr,
                                  result_auto = nullptr;
          /*
           * Xc < Y   =>   Z < Y && Z = Xc
           */
          if(left->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
            DVLOG(VLOG_LEVEL) << "Concat on left side!";
            // Add temp track for temp variable, Z
            std::map<std::string,int> trackmap_handle = relation->get_variable_trackmap();
            std::string name = symbol_table_->get_var_name_for_node(term, Variable::Type::STRING);
            int id = trackmap_handle.size();
            trackmap_handle[name] = id;
            temp_relation = new StringRelation();
            temp_relation->set_type(StringRelation::Type::STRING_VAR);
            temp_relation->set_data(name);


            relation->set_left(temp_relation);
            relation->set_variable_trackmap(trackmap_handle);
            // Z relation_op Y
            temp_auto = MultiTrackAutomaton::makeAuto(relation);
            relation->set_left(left);

            // Z = Xc (temp var Z on last track)
            left->set_variable_trackmap(trackmap_handle);
            multi_auto = MultiTrackAutomaton::makeConcatExtraTrack(left);
            result_auto = temp_auto->intersect(multi_auto);
            delete temp_auto;
            delete multi_auto;
            // project away temp track/variable Z
            multi_auto = result_auto->projectKTrack(id);
            delete result_auto;

            trackmap_handle.erase(name);
            relation->set_variable_trackmap(trackmap_handle);
            multi_auto->setRelation(relation->clone());
            delete temp_relation;
          } else if(right->get_type() == StringRelation::Type::CONCAT_VAR_CONSTANT) {
            DVLOG(VLOG_LEVEL) << "Concat on right side!";
            std::map<std::string, int> trackmap_handle = relation->get_variable_trackmap();
            std::string name = symbol_table_->get_var_name_for_node(term, Variable::Type::STRING);
            int id = trackmap_handle.size();
            trackmap_handle[name] = id;

            temp_relation = new StringRelation();
            temp_relation->set_type(StringRelation::Type::STRING_VAR);
            temp_relation->set_data(name);

            relation->set_right(temp_relation);
            relation->set_variable_trackmap(trackmap_handle);
            temp_auto = MultiTrackAutomaton::makeAuto(relation);
            relation->set_right(right);

            right->set_variable_trackmap(trackmap_handle);
            multi_auto = MultiTrackAutomaton::makeConcatExtraTrack(right);
            result_auto = temp_auto->intersect(multi_auto);
            delete temp_auto;
            delete multi_auto;
            multi_auto = result_auto->projectKTrack(id);
            delete result_auto;

            trackmap_handle.erase(name);
            relation->set_variable_trackmap(trackmap_handle);
            multi_auto->setRelation(relation->clone());
            delete temp_relation;
          } else {
            DVLOG(VLOG_LEVEL) << "No concat!";
            multi_auto = MultiTrackAutomaton::makeAuto(relation);
          }

          Value_ptr val = new Value(multi_auto);
          std::string group_name = string_relation_generator_.get_term_group_name(term);
          symbol_table_->updateValue(group_name,val);
          DVLOG(VLOG_LEVEL) << "Updating group name: " << group_name;
          delete val;
          break;
        }
        default:
          break;
      }
      return false;
  };

  auto command_callback = [](Command_ptr command) -> bool {
      if (Command::Type::ASSERT == command->getType()) {
        return true;
      }
      return false;
  };

  setCommandPreCallback(command_callback);
  setTermPreCallback(term_callback);
}

void StringConstraintSolver::visitScript(Script_ptr script) {
  symbol_table_->push_scope(script);
  visit_children_of(script);
  symbol_table_->pop_scope();
}

void StringConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;
  AstTraverser::visit(assert_command->term);
}

void StringConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
  current_term_ = and_term;

  if (not constraint_information_->is_component(and_term)) {
    visit_children_of(and_term);
    return;
  }

  bool is_satisfiable = true;

  StringRelation_ptr relation = nullptr;
  Value_ptr result = nullptr, param = nullptr, and_value = nullptr;

  for(auto& term : *and_term->term_list) {
    relation = string_relation_generator_.get_term_relation(term);
    if(relation != nullptr) {
      visit(term);
      param = get_term_value(term);
      is_satisfiable = is_satisfiable and param->isSatisfiable();
      string_relation_generator_.delete_term_relation(term);
      if(!is_satisfiable) {
        result = new Value(MultiTrackAutomaton::makePhi(relation->get_num_tracks()));
        break;
      }
    }
  }
}

void StringConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
  current_term_ = or_term;
  for (auto& term : *(or_term->term_list)) {
    symbol_table_->push_scope(term);
    visit(term);
    symbol_table_->pop_scope();
  }
}

void StringConstraintSolver::visitConcat(Concat_ptr concat_term) {
}

void StringConstraintSolver::visitIn(In_ptr in_term) {
}

void StringConstraintSolver::visitNotIn(NotIn_ptr not_in_term) {
}

void StringConstraintSolver::visitLen(Len_ptr len_term) {
}

void StringConstraintSolver::visitContains(Contains_ptr contains_term) {
}

void StringConstraintSolver::visitNotContains(NotContains_ptr not_contains_term) {
}

void StringConstraintSolver::visitEnds(Ends_ptr ends_term) {
}

void StringConstraintSolver::visitNotEnds(NotEnds_ptr not_ends_term) {
}

void StringConstraintSolver::visitIndexOf(IndexOf_ptr index_of_term) {
}

void StringConstraintSolver::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
}

void StringConstraintSolver::visitCharAt(CharAt_ptr char_at_term) {
}

void StringConstraintSolver::visitSubString(SubString_ptr sub_string_term) {
}

void StringConstraintSolver::visitToUpper(ToUpper_ptr to_upper_term) {
}

void StringConstraintSolver::visitToLower(ToLower_ptr to_lower_term) {
}

void StringConstraintSolver::visitTrim(Trim_ptr trim_term) {
}

void StringConstraintSolver::visitReplace(Replace_ptr replace_term) {
}

void StringConstraintSolver::visitCount(Count_ptr count_term) {
}

void StringConstraintSolver::visitIte(Ite_ptr ite_term) {
}

void StringConstraintSolver::visitReConcat(ReConcat_ptr reconcat_term) {
}

void StringConstraintSolver::visitToRegex(ToRegex_ptr to_regex_term) {
}

std::string StringConstraintSolver::get_string_variable_name(Term_ptr term) {
  std::string group_name = string_relation_generator_.get_term_group_name(term);
  return group_name;
}

Value_ptr StringConstraintSolver::get_term_value(Term_ptr term) {
  std::string group_name = string_relation_generator_.get_term_group_name(term);
  if(!group_name.empty()) {
    return symbol_table_->getValue(group_name);
  }
  return nullptr;
}

bool StringConstraintSolver::set_term_value(Term_ptr term, Value_ptr value) {
  std::string group_name = string_relation_generator_.get_term_group_name(term);
  if(!group_name.empty()) {
    symbol_table_->setValue(group_name,value);
    return true;
  }
  return false;
}

Value_ptr StringConstraintSolver::get_variable_value(Variable_ptr variable, bool multi_val) {
  MultiTrackAutomaton_ptr relation_auto = nullptr;
  StringAutomaton_ptr variable_auto = nullptr;
  StringRelation_ptr variable_relation = nullptr;
  Value_ptr relation_value = nullptr;
  std::string group_name = string_relation_generator_.get_variable_group_name(current_term_,variable);
  if(group_name.empty()) {
    return nullptr;
  }
  DVLOG(VLOG_LEVEL) << "VARIABLE: " << variable->str() << " is part of GROUP: " << group_name;
  relation_value = symbol_table_->getValue(group_name);

  if(multi_val) {
    return relation_value->clone();
  }

  relation_auto = relation_value->getMultiTrackAutomaton();
  variable_relation = relation_auto->getRelation();
  variable_auto = relation_auto->getKTrack(variable_relation->get_variable_index(variable->getName()));
  return new Value(variable_auto);
}

bool StringConstraintSolver::update_variable_value(Variable_ptr variable, Value_ptr value) {
  MultiTrackAutomaton_ptr relation_auto = nullptr, variable_multi_auto = nullptr,intersect_auto = nullptr;
  StringAutomaton_ptr variable_auto = nullptr;
  Value_ptr relation_value = nullptr;
  StringRelation_ptr variable_relation = nullptr;
  std::string group_name = string_relation_generator_.get_variable_group_name(current_term_,variable);
  if(group_name.empty()) {
    LOG(FATAL) << "Empty group name!";
  }
  relation_value = symbol_table_->getValue(group_name);
  DVLOG(VLOG_LEVEL) << "VARIABLE: " << variable->str() << " is part of GROUP: " << group_name;
  variable_auto = value->getStringAutomaton();

  relation_auto = relation_value->getMultiTrackAutomaton();
  variable_relation = relation_auto->getRelation();
  // place variable value on multitrack, intersect and update corresonding term value
  variable_multi_auto = new MultiTrackAutomaton(variable_auto->getDFA(),
                                       variable_relation->get_variable_index(variable->getName()),
                                       variable_relation->get_num_tracks());
  variable_multi_auto->setRelation(variable_relation->clone());

  Value_ptr val = new Value(variable_multi_auto);
  symbol_table_->updateValue(group_name,val);
  delete val;
  return true;
}

} /* namespace Solver */
} /* namespace Vlab */