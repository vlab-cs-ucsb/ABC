/*
 * StringConstraintSolver.cpp
 *
 *  Created on: Jan 22, 2017
 *      Author: baki
 */

#include "StringConstraintSolver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringConstraintSolver::VLOG_LEVEL = 13;

StringConstraintSolver::StringConstraintSolver(Script_ptr script, SymbolTable_ptr symbol_table,
                                                       ConstraintInformation_ptr constraint_information)
    : AstTraverser(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      string_formula_generator_(script, symbol_table, constraint_information) {
  setCallbacks();
}

StringConstraintSolver::~StringConstraintSolver() {
}


void StringConstraintSolver::start(Visitable_ptr node) {
  DVLOG(VLOG_LEVEL) << "String constraint solving starts at node: " << node;
  this->Visitor::visit(node);
  end();
}

void StringConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "String constraint solving starts at root";
  visitScript(root_);
  end();
}

void StringConstraintSolver::end() {
  string_formula_generator_.end();
}

void StringConstraintSolver::collect_string_constraint_info() {
  string_formula_generator_.start();
  integer_terms_map_ = string_formula_generator_.get_integer_terms_map();
}

/**
 * TODO move group updating inside AND and OR
 */
void StringConstraintSolver::setCallbacks() {
  auto term_callback = [this] (Term_ptr term) -> bool {
    switch (term->type()) {
      case Term::Type::NOT:
      case Term::Type::EQ:
      case Term::Type::NOTEQ:
      case Term::Type::GT:
      case Term::Type::GE:
      case Term::Type::LT:
      case Term::Type::LE:
      case Term::Type::BEGINS:
      case Term::Type::NOTBEGINS: {
        auto formula = string_formula_generator_.get_term_formula(term);
        if (formula != nullptr) {
          DVLOG(VLOG_LEVEL) << "Relational String Formula: " << *formula << "@" << term;
          auto relational_str_auto = MultiTrackAutomaton::MakeAutomaton(formula->clone());
          auto result = new Value(relational_str_auto);
          set_term_value(term, result);
          // once we solve an atomic string constraint,
          // we delete its formula to avoid solving it again.
          // Atomic string constraints solved precisely,
          // mixed constraints handled without resolving this part
          string_formula_generator_.clear_term_formula(term);
        }
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
  symbol_table_->pop_scope();  // global scope, it is reachable via script pointer all the time
}

void StringConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;
  AstTraverser::visit(assert_command->term);
}

void StringConstraintSolver::visitAnd(And_ptr and_term) {
  if (not constraint_information_->is_component(and_term)) {
    DVLOG(VLOG_LEVEL) << "visit children of non-component start: " << *and_term << "@" << and_term;
    visit_children_of(and_term);
    DVLOG(VLOG_LEVEL) << "visit children of non-component end: " << *and_term << "@" << and_term;
    return;
  }

  if (not constraint_information_->has_string_constraint(and_term)) {
    return;
  }

  DVLOG(VLOG_LEVEL) << "visit children of component start: " << *and_term << "@" << and_term;

  bool is_satisfiable = true;
  bool has_string_formula = false;

  std::string group_name = string_formula_generator_.get_term_group_name(and_term);
  Value_ptr and_value = nullptr;

  for (auto term : *(and_term->term_list)) {
    auto formula = string_formula_generator_.get_term_formula(term);
    if (formula != nullptr) {
      has_string_formula = true;
      visit(term);
      auto param = get_term_value(term);
      is_satisfiable = param->is_satisfiable();
      if (is_satisfiable) {
        if (and_value == nullptr) {
          and_value = param->clone();
        } else {
          auto old_value = and_value;
          and_value = and_value->intersect(param);
          delete old_value;
          is_satisfiable = and_value->is_satisfiable();
        }
      }
      clear_term_value(term);
      if (not is_satisfiable) {
        break;
      }
    }
  }

  DVLOG(VLOG_LEVEL) << "visit children of component end: " << *and_term << "@" << and_term;

  DVLOG(VLOG_LEVEL) << "post visit component start: " << *and_term << "@" << and_term;

  /**
   * TODO Below comment is copied from arithmetic constraint solver, there are different cases
   * If and term does not have string formula, but we end up being here:
   * 1) And term is under a disjunction and other disjunctive terms has string formula.
   *  Here, variables appearing in string term will be unconstrained.
   * 2) We are visited and term second time for some mixed constraints, for this we do an unnecessary
   *  intersection below with any string, we can avoid that with more checks later!!!
   */
  if (and_value == nullptr and (not has_string_formula)) {
    auto group_formula = string_formula_generator_.get_group_formula(group_name);
    and_value = new Value(Theory::BinaryIntAutomaton::MakeAnyInt(group_formula->clone()));
    has_string_formula = true;
    is_satisfiable = true;
  }

  if (has_string_formula) {
    if (is_satisfiable) {
      symbol_table_->IntersectValue(group_name, and_value);  // update value
    } else {
      auto group_formula = string_formula_generator_.get_group_formula(group_name);
      auto value = new Value(Theory::BinaryIntAutomaton::MakePhi(group_formula->clone()));
      symbol_table_->set_value(group_name, value);
    }
    delete and_value;
  }
  DVLOG(VLOG_LEVEL) << "post visit component end: " << *and_term << "@" << and_term;
}

/**
 * 1) Update group value at each scope
 * 2) Update result (union of scopes) after all
 */
void StringConstraintSolver::visitOr(Or_ptr or_term) {
  if (not constraint_information_->is_component(or_term)) {  // a rare case, @deprecated
    DVLOG(VLOG_LEVEL) << "visit children of non-component start: " << *or_term << "@" << or_term;
    visit_children_of(or_term);
    DVLOG(VLOG_LEVEL) << "visit children of non-component end: " << *or_term << "@" << or_term;
    return;
  }

  if (not constraint_information_->has_string_constraint(or_term)) {
    return;
  }

  DVLOG(VLOG_LEVEL) << "visit children of component start: " << *or_term << "@" << or_term;
  bool is_satisfiable = false;
  std::string group_name = string_formula_generator_.get_term_group_name(or_term);
  Value_ptr or_value = nullptr;
  for (auto term : *(or_term->term_list)) {
    auto formula = string_formula_generator_.get_term_formula(term);
    if (formula != nullptr) {
      symbol_table_->push_scope(term);
      visit(term);
      auto param = get_term_value(term);
      is_satisfiable = param->is_satisfiable() or is_satisfiable;
      if (is_satisfiable) {
        if (or_value == nullptr) {
          or_value = param->clone();
        } else {
          auto old_value = or_value;
          or_value = or_value->union_(param);
          delete old_value;
        }
      }
      clear_term_value(term);
      symbol_table_->pop_scope();
    }
  }

  DVLOG(VLOG_LEVEL) << "visit children of component end: " << *or_term << "@" << or_term;

  DVLOG(VLOG_LEVEL) << "post visit component start: " << *or_term << "@" << or_term;

  if (constraint_information_->has_string_constraint(or_term)) {
    if (is_satisfiable) {
      // scope already reads value from upper scope
      // implicit intersection is already done
//      symbol_table_->IntersectValue(group_name, or_value);  // update value for union, this is upper scope
      symbol_table_->set_value(group_name, or_value);
    } else {
      auto group_formula = string_formula_generator_.get_group_formula(group_name);
      auto value = new Value(Theory::BinaryIntAutomaton::MakePhi(group_formula->clone()));
      symbol_table_->set_value(group_name, value);
      delete or_value; // nullptr safe
    }
  }

  DVLOG(VLOG_LEVEL) << "post visit component end: " << *or_term << "@" << or_term;
}

std::string StringConstraintSolver::get_string_variable_name(SMT::Term_ptr term) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  return symbol_table_->get_var_name_for_node(key, Variable::Type::INT);
}

Value_ptr StringConstraintSolver::get_term_value(Term_ptr term) {
  auto it = term_values_.find(term);
  if (it != term_values_.end()) {
    return it->second;
  }
  std::string group_name = string_formula_generator_.get_term_group_name(term);

  if (not group_name.empty()) {
    return symbol_table_->get_value(group_name);
  }

  return nullptr;
}

/**
 * Term values are only stored for atomic constraints
 */
bool StringConstraintSolver::set_term_value(Term_ptr term, Value_ptr value) {
  auto result = term_values_.insert( { term, value });
  if (result.second == false) {
    LOG(FATAL)<< "Term automaton is already computed: " << *term << "@" << term;
  }
//  std::string group_name = arithmetic_formula_generator_.get_term_group_name(term);
//  if(!group_name.empty()) {
//    symbol_table_->set_value(group_name,value);
//    return true;
//  }
  return result.second;
}

bool StringConstraintSolver::set_group_value(Term_ptr term, Value_ptr value) {
  std::string group_name = string_formula_generator_.get_term_group_name(term);
  return symbol_table_->set_value(group_name, value);
}

void StringConstraintSolver::clear_term_values() {
  for (auto& entry : term_values_) {
    delete entry.second;
  }

  term_values_.clear();
}

/**
 * We don't need an atomic term value ones we compute it.
 */
void StringConstraintSolver::clear_term_value(Term_ptr term) {
  auto it = term_values_.find(term);
  if (it != term_values_.end()) {
    delete it->second;
    term_values_.erase(it);
  }
}

bool StringConstraintSolver::has_integer_terms(Term_ptr term) {
  return (integer_terms_map_.find(term) != integer_terms_map_.end());
}

TermList& StringConstraintSolver::get_integer_terms_in(Term_ptr term) {
  return integer_terms_map_[term];
}

std::map<SMT::Term_ptr, SMT::TermList>& StringConstraintSolver::get_integer_terms_map() {
  return integer_terms_map_;
}

} /* namespace Solver */
} /* namespace Vlab */
