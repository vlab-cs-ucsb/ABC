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
        case Term::Type::LE: {
          DVLOG(VLOG_LEVEL) << "visit: " << *term;
          StringRelation_ptr relation = string_relation_generator_.get_term_relation(term);
          if(relation == nullptr) {
            return false;
          }

          MultiTrackAutomaton_ptr multi_auto = MultiTrackAutomaton::makeAuto(relation);
          Value_ptr val = new Value(multi_auto);
          set_term_value(term,val);
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
  // for temporary variable->term mappings for interplay between
  AstTraverser::visit(assert_command->term);
}

void StringConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;

  if (not constraint_information_->is_component(and_term)) {
    visit_children_of(and_term);
    set_term_value(and_term, nullptr);
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
      if(is_satisfiable) {
        if (result == nullptr) {
          result = param->clone();
        } else {
          and_value = result->intersect(param);
          delete result;
          result = and_value;
        }
      } else {
        result = new Value(MultiTrackAutomaton::makePhi(relation->get_num_tracks()));
        break;
      }
    }
    clear_term_value(term);
  }

  for (auto& term : *(and_term->term_list)) {
    relation = string_relation_generator_.get_term_relation(term);
    if (relation != nullptr) {
      term_value_index_[term] = and_term;
      clear_term_value(term);
    }
  }

  set_term_value(and_term, result);
}

void StringConstraintSolver::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;
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

void StringConstraintSolver::visitBegins(Begins_ptr begins_term) {
}

void StringConstraintSolver::visitNotBegins(NotBegins_ptr not_begins_term) {
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

Value_ptr StringConstraintSolver::get_term_value(Term_ptr term) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  auto it2 = term_values_.find(key);
  if (it2 != term_values_.end()) {
    return it2->second;
  }

  return nullptr;
}

bool StringConstraintSolver::set_term_value(Term_ptr term, Value_ptr value) {
  auto result = term_values_.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL) << "value is already computed for term: " << *term;
  }
  term_value_index_[term] = term;
  return result.second;
}

bool StringConstraintSolver::update_term_value(Term_ptr term, Value_ptr value) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  auto it2 = term_values_.find(key);
  if (it2 != term_values_.end()) {
    it2->second = value;
    return true;
  }

  return false;
}

void StringConstraintSolver::clear_term_value(Term_ptr term) {
  auto it = term_values_.find(term);
  if (it != term_values_.end()) {
    delete it->second;
    term_values_.erase(it);
  }
}

std::map<Term_ptr, Term_ptr> &StringConstraintSolver::get_term_value_index() {
  return term_value_index_;
}

StringConstraintSolver::TermValueMap &StringConstraintSolver::get_term_values() {
  return term_values_;
}

Value_ptr StringConstraintSolver::get_variable_value(Variable_ptr variable) {
  MultiTrackAutomaton_ptr relation_auto = nullptr;
  StringAutomaton_ptr variable_auto = nullptr;
  StringRelation_ptr variable_relation = nullptr;
  Value_ptr relation_value = get_relational_value(variable);
  if(relation_value == nullptr) {
    return nullptr;
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
  Term_ptr term = string_relation_generator_.get_parent_term(variable);
  relation_value = get_relational_value(variable);
  if(relation_value == nullptr) {
    LOG(FATAL) << "Unable to get update relational value for variable: " << variable->getName();
    return false;
  }
  variable_auto = value->getStringAutomaton();
  relation_auto = relation_value->getMultiTrackAutomaton();
  variable_relation = relation_auto->getRelation();

  // place variable value on multitrack, intersect and update corresonding term value
  variable_multi_auto = new MultiTrackAutomaton(variable_auto->getDFA(),
                                       variable_relation->get_variable_index(variable->getName()),
                                       variable_relation->get_num_tracks());
  intersect_auto = relation_auto->intersect(variable_multi_auto);
  relation_value = new Value(intersect_auto);
  clear_term_value(term);
  set_term_value(term, relation_value);
  return true;
}

Value_ptr StringConstraintSolver::get_relational_value(SMT::Variable_ptr variable) {
  Value_ptr relation_value = nullptr;
  StringRelation_ptr variable_relation = nullptr;
  Term_ptr term = string_relation_generator_.get_parent_term(variable);
  if(term == nullptr) {
    return nullptr;
  }
  relation_value = get_term_value(term);
  if(relation_value == nullptr || relation_value->getType() != Value::Type::MULTITRACK_AUTOMATON) {
    return nullptr;
  }
  variable_relation = relation_value->getMultiTrackAutomaton()->getRelation();
  if(variable_relation->get_variable_index(variable->getName()) == -1) {
    LOG(FATAL) << "Variable not part of expected relation";
    return nullptr;
  }
  return relation_value;
}

} /* namespace Solver */
} /* namespace Vlab */
