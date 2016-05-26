//
// Created by will on 3/4/16.
//

#include "StringConstraintSolver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringConstraintSolver::VLOG_LEVEL = 13;

StringConstraintSolver::StringConstraintSolver(Script_ptr script, SymbolTable_ptr symb)
  : AstTraverser(script), symbol_table(symb),
    string_relation_generator(script, symb) {
  setCallbacks();
}


StringConstraintSolver::~StringConstraintSolver() {
}

void StringConstraintSolver::start() {
  string_relation_generator.visit(root);
  visitScript(root);
  end();
}

void StringConstraintSolver::end() {
}

void StringConstraintSolver::setCallbacks() {
  auto term_callback = [this](Term_ptr term) -> bool {
      switch (term->type()) {
        case Term::Type::EQ:
        case Term::Type::NOTEQ: {
          DVLOG(VLOG_LEVEL) << "visit: " << *term;
          StringRelation_ptr relation = string_relation_generator.get_term_relation(term);
          if(relation == nullptr) {
            return false;
          }

          StringRelation::Subrelation subrel = relation->get_subrelation_list()[0];
          std::vector<std::pair<std::string,int>> tracks;
          for(auto& name : subrel.names) {
            tracks.push_back(std::make_pair(name,relation->get_variable_index(name)));
          }
          MultiTrackAutomaton_ptr multi_auto = nullptr;
          if(term->type() == Term::Type::EQ)
            multi_auto = MultiTrackAutomaton::makeEquality(tracks,relation->get_num_tracks());
          else
            multi_auto = MultiTrackAutomaton::makeNotEquality(tracks,relation->get_num_tracks());
          relation->set_value_auto(multi_auto);
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
  symbol_table->push_scope(script);
  visit_children_of(script);
  symbol_table->pop_scope();
}

void StringConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;
  AstTraverser::visit(assert_command->term);
}

void StringConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
  bool is_satisfiable = true;
  Component_ptr current_component = nullptr;
  StringRelation_ptr current_relation = nullptr, term_relation = nullptr, temp_relation;
  Value_ptr term_value = nullptr;
  if (and_term->component!= nullptr) {
    current_component = and_term->component;
  }

  for(auto& term : *and_term->term_list) {
    visit(term);
    term_relation = string_relation_generator.get_term_relation(term);
    if(term_relation != nullptr) {
      if(current_relation == nullptr) {
        current_relation = term_relation;
      } else {
        current_relation = current_relation->combine(term_relation);
        string_relation_generator.delete_term_relation(term);
        term_value = new Value(current_relation->get_value_auto()->clone());
        update_term_value(term,term_value);
      }

    }
  }

  if(current_relation != nullptr) {
    current_component->set_sat(!current_relation->get_value_auto()->isEmptyLanguage());
    symbol_table->set_component_relation(current_component,current_relation);
  }

  set_term_value(and_term,term_value);
}

void StringConstraintSolver::visitOr(Or_ptr or_term) {
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
  auto it1 = term_value_index.find(term);
  if (it1 != term_value_index.end()) {
    key = it1->second;
  }

  auto it2 = term_values.find(key);
  if (it2 != term_values.end()) {
    return it2->second;
  }

  return nullptr;
}

bool StringConstraintSolver::set_term_value(Term_ptr term, Value_ptr value) {
  auto result = term_values.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL) << "value is already computed for term: " << *term;
  }
  term_value_index[term] = term;
  return result.second;
}

bool StringConstraintSolver::update_term_value(Term_ptr term, Value_ptr value) {
  Term_ptr key = term;
  auto it1 = term_value_index.find(term);
  if (it1 != term_value_index.end()) {
    key = it1->second;
  }

  auto it2 = term_values.find(key);
  if (it2 != term_values.end()) {
    it2->second = value;
    return true;
  }

  return false;
}

void StringConstraintSolver::clear_term_value(Term_ptr term) {
  auto it = term_values.find(term);
  if (it != term_values.end()) {
    delete it->second;
    term_values.erase(it);
  }
}

std::map<Term_ptr, Term_ptr> &StringConstraintSolver::get_term_value_index() {
  return term_value_index;
}

StringConstraintSolver::TermValueMap &StringConstraintSolver::get_term_values() {
  return term_values;
}

} /* namespace Solver */
} /* namespace Vlab */