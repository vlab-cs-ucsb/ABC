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

int StringConstraintSolver::dfa_misses = 0;
int StringConstraintSolver::dfa_hits = 0;
std::map<std::string,DFA_ptr> StringConstraintSolver::stupid_cache;

const int StringConstraintSolver::VLOG_LEVEL = 13;

StringConstraintSolver::StringConstraintSolver(Script_ptr script, SymbolTable_ptr symbol_table,
                                                       ConstraintInformation_ptr constraint_information)
    : AstTraverser(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      string_formula_generator_(script, symbol_table, constraint_information) {
  setCallbacks();

  auto start = std::chrono::steady_clock::now();
  auto end = std::chrono::steady_clock::now();
  diff = end-start;
  diff2 = end-start;
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

void StringConstraintSolver::collect_string_constraint_info(Visitable_ptr node) {
  string_formula_generator_.start(node);
  integer_terms_map_ = string_formula_generator_.get_integer_terms_map();
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
        if (formula != nullptr && formula->GetType() != Theory::StringFormula::Type::NONRELATIONAL) {
          DVLOG(VLOG_LEVEL) << "Relational String Formula: " << *formula << "@" << term;
//          for(auto it : formula->GetVariableCoefficientMap()) {
//            LOG(INFO) << it.first;
//          }
//          LOG(INFO) << "";

          auto start = std::chrono::steady_clock::now();

          auto relational_str_auto = StringAutomaton::MakeAutomaton(formula->clone());

          auto end = std::chrono::steady_clock::now();
          diff += end - start;


          auto result = new Value(relational_str_auto);
          set_term_value(term, result);
          auto term_group_name = string_formula_generator_.get_term_group_name(term);
          if(term_group_name.empty()) {
            LOG(FATAL) << "Term has no group!";
          }
          // LOG(INFO) << "symbol table intersect";
//
//
//          auto left_auto = symbol_table_->get_value(term_group_name)->getStringAutomaton();
//          auto right_auto = relational_str_auto;
//
//          auto bdd_start = std::chrono::steady_clock::now();
//
//          std::string id1, id2;
//          std::stringstream os1;
//  //        {
//  //          cereal::BinaryOutputArchive ar(os1);
//  //          Util::Serialize::save(ar, left_auto->getDFA());
//  //        }
//          left_auto->toBDD(os1);
//          id1 = os1.str();
//
//          std::stringstream os2;
//  //        {
//  //          cereal::BinaryOutputArchive ar(os1);
//  //          Util::Serialize::save(ar, right_auto->getDFA());
//  //        }
//          right_auto->toBDD(os2);
//          id2 = os2.str();
//
//  //        LOG(INFO) << id1.size();
//
//          auto bdd_end = std::chrono::steady_clock::now();
//          diff2 += bdd_end-bdd_start;
//
//          std::string stupid_key1 = id1 + id2;
//          std::string stupid_key2 = id2 + id1;
//          Theory::DFA_ptr intersect_dfa = nullptr;
//          Theory::StringAutomaton_ptr intersect_auto = nullptr;
//
//          if(stupid_cache.find(stupid_key1) != stupid_cache.end()) {
//            auto cache_start = std::chrono::steady_clock::now();
//
//            intersect_dfa = dfaCopy(stupid_cache[stupid_key1]);
//
//
//            auto new_formula = symbol_table_->get_value(term_group_name)->getStringAutomaton()->GetFormula()->Intersect(result->getStringAutomaton()->GetFormula());
//            intersect_auto = new Theory::StringAutomaton(intersect_dfa,new_formula,false);
//            symbol_table_->set_value(term_group_name,new Value(intersect_auto));
//            dfa_hits++;
//
//
//            auto cache_end = std::chrono::steady_clock::now();
//            diff += cache_end - cache_start;
//
//          } else if (stupid_cache.find(stupid_key2) != stupid_cache.end()) {
//            auto cache_start = std::chrono::steady_clock::now();
//
//            intersect_dfa = dfaCopy(stupid_cache[stupid_key2]);
//
//
//            auto new_formula = symbol_table_->get_value(term_group_name)->getStringAutomaton()->GetFormula()->Intersect(result->getStringAutomaton()->GetFormula());
//            intersect_auto = new Theory::StringAutomaton(intersect_dfa,new_formula,false);
//            symbol_table_->set_value(term_group_name,new Value(intersect_auto));
//            dfa_hits++;
//
//
//            auto cache_end = std::chrono::steady_clock::now();
//            diff += cache_end - cache_start;
//
//          } else {
//
//            symbol_table_->IntersectValue(term_group_name,result);
//            auto cache_start = std::chrono::steady_clock::now();
//            intersect_dfa = symbol_table_->get_value(term_group_name)->getStringAutomaton()->getDFA();
//            stupid_cache[stupid_key1] = dfaCopy(intersect_dfa);
//            auto cache_end = std::chrono::steady_clock::now();
//            diff += cache_end - cache_start;
//            dfa_misses++;
//          }
          while(symbol_table_->values_lock_) std::this_thread::yield();
          symbol_table_->IntersectValue(term_group_name,result);
//          symbol_table_->get_value(term_group_name)->getStringAutomaton()->inspectAuto(false,true);
//          std::cin.get();
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
    // Do not visit child or terms here, handle them in POSTVISIT AND
    if (formula != nullptr and (dynamic_cast<Or_ptr>(term) == nullptr)) {
      has_string_formula = true;
      visit(term);
      auto param = get_term_value(term);
      is_satisfiable = param->is_satisfiable();
      if (is_satisfiable) {
//        if (and_value == nullptr) {
//          and_value = param->clone();
//        } else {
//          auto old_value = and_value;
//          and_value = and_value->intersect(param);
//          delete old_value;
//          is_satisfiable = and_value->is_satisfiable();
//        }
      	auto term_group_name = string_formula_generator_.get_term_group_name(term);
				if(term_group_name.empty()) {
					LOG(FATAL) << "Term has no group!";
				}
				symbol_table_->IntersectValue(term_group_name,param);
				is_satisfiable = symbol_table_->get_value(term_group_name)->is_satisfiable();
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
//  if (and_value == nullptr and (not has_string_formula)) {
//  	auto group_formula = string_formula_generator_.get_group_formula(group_name);
//    and_value = new Value(Theory::StringAutomaton::MakeAnyStringAligned(group_formula->clone()));
//    has_string_formula = true;
//    is_satisfiable = true;
//  }

  //if (has_string_formula) {
//    if (is_satisfiable) {
//      symbol_table_->IntersectValue(group_name, and_value);  // update value
//    } else {
//      auto group_formula = string_formula_generator_.get_group_formula(group_name);
//      auto value = new Value(Theory::StringAutomaton::MakePhi(group_formula->clone()));
//      symbol_table_->set_value(group_name, value);
//    }
//    delete and_value;
  	auto satisfiable_value = new Value(is_satisfiable);
  	symbol_table_->IntersectValue(group_name,satisfiable_value);
  	delete satisfiable_value;
  	//}
  DVLOG(VLOG_LEVEL) << "post visit component end: " << *and_term << "@" << and_term;
}

/**
 * 1) Update group value at each scope
 * 2) Update result (union of scopes) after all
 */
void StringConstraintSolver::visitOr(Or_ptr or_term) {

  if (not constraint_information_->has_string_constraint(or_term)) {
    return;
  }

  DVLOG(VLOG_LEVEL) << "visit children of component start: " << *or_term << "@" << or_term;
  bool is_satisfiable = false;
  bool has_string_formula = false;
  std::string group_name = string_formula_generator_.get_term_group_name(or_term);
  auto group_formula = string_formula_generator_.get_group_formula(group_name);

  // propagate equivalence class values for constants
	for (auto term : *(or_term->term_list)) {
		auto& variable_value_map = symbol_table_->get_values_at_scope(term);
		symbol_table_->push_scope(term);
		for (auto iter = variable_value_map.begin(); iter != variable_value_map.end();) {
			if(Value::Type::STRING_AUTOMATON == iter->second->getType() and iter->second->getStringAutomaton()->GetFormula()->GetNumberOfVariables() == 0) {
				//has_string_formula = true;
				auto variable_group = string_formula_generator_.get_variable_group_name(iter->first);
				auto group_formula = string_formula_generator_.get_group_formula(variable_group);
				if(group_formula == nullptr) {
					iter++;
					continue;
				}
				StringFormula_ptr formula = new StringFormula();
				formula->SetType(StringFormula::Type::VAR);
				formula->AddVariable(iter->first->getName(),1);
				iter->second->getStringAutomaton()->SetFormula(formula);
				symbol_table_->IntersectValue(variable_group,iter->second);
				delete iter->second;iter->second = nullptr;
				iter = variable_value_map.erase(iter);
			} else {
				iter++;
			}
		}
		symbol_table_->pop_scope();
	}


  for (auto term : *(or_term->term_list)) {
    auto formula = string_formula_generator_.get_term_formula(term);
    // Do not visit child and terms here, handle them in POSTVISIT OR
    if (formula != nullptr and (dynamic_cast<And_ptr>(term) == nullptr)) {
			has_string_formula = true;
			symbol_table_->push_scope(term);
			visit(term);
			auto param = get_term_value(term);
			is_satisfiable = param->is_satisfiable() or is_satisfiable;
			if (is_satisfiable) {
				auto term_group_name = string_formula_generator_.get_term_group_name(term);
				if(term_group_name.empty()) {
					LOG(FATAL) << "Term has no group!";
				}
				symbol_table_->IntersectValue(term_group_name,param);
			}
			clear_term_value(term);
			symbol_table_->pop_scope();
		}
  }

  DVLOG(VLOG_LEVEL) << "visit children of component end: " << *or_term << "@" << or_term;

  DVLOG(VLOG_LEVEL) << "post visit component start: " << *or_term << "@" << or_term;

  if (not has_string_formula) {
  	is_satisfiable = true;
  }

  auto satisfiable_value = new Value(is_satisfiable);
	symbol_table_->UnionValue(group_name,satisfiable_value);
	delete satisfiable_value;
	//}

  DVLOG(VLOG_LEVEL) << "post visit component end: " << *or_term << "@" << or_term;
}

void StringConstraintSolver::postVisitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "collect child results start: " << *and_term << "@" << and_term;

  bool is_satisfiable = true;
  bool has_string_formula = false;
  std::string group_name = string_formula_generator_.get_term_group_name(and_term);
  Value_ptr and_value = nullptr;

  for (auto term : *(and_term->term_list)) {
    auto formula = string_formula_generator_.get_term_formula(term);
    /**
     * In previous visit, automata for string constraints are created and
     * formulae for them are deleted.
     * For sub or terms, constraint solver recurses into and here we don't
     * need to visit them, a value is already computed for them,
     * grabs them from symbol table
     */
    if (formula != nullptr) {
    	has_string_formula = true;
    }
  }

  DVLOG(VLOG_LEVEL) << "collect child results end: " << *and_term << "@" << and_term;

  DVLOG(VLOG_LEVEL) << "update result start: " << *and_term << "@" << and_term;


	for(auto group : string_formula_generator_.get_group_subgroups(group_name)) {
		Variable_ptr subgroup_variable = symbol_table_->get_variable(group);
		Value_ptr subgroup_value = symbol_table_->get_value(subgroup_variable);
		is_satisfiable = subgroup_value->is_satisfiable() and is_satisfiable;
	}
	auto satisfiable_value = new Value(is_satisfiable);
	symbol_table_->IntersectValue(group_name,satisfiable_value);
	delete satisfiable_value;
  DVLOG(VLOG_LEVEL) << "update result end: " << *and_term << "@" << and_term;
}

void StringConstraintSolver::postVisitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "collect child results start: " << *or_term << "@" << or_term;

  bool is_satisfiable = false;
  bool has_string_formula = false;

  std::string group_name = string_formula_generator_.get_term_group_name(or_term);
  std::map<std::string,Value_ptr> or_values;

  for (auto term : *(or_term->term_list)) {
    //auto formula = string_formula_generator_.get_term_formula(term);
    /**
     * In previous visit, automata for arithmetic constraints are created and
     * formulae for them are deleted.
     * For sub and terms, constraint solver recurses into and here we don't
     * need to visit them, a value is already computed for them,
     * grabs them from symbol table
     */
  	symbol_table_->push_scope(term);
  	for(auto group : string_formula_generator_.get_group_subgroups(group_name)) {
  		Variable_ptr subgroup_variable = symbol_table_->get_variable(group);
  		Value_ptr subgroup_scope_value = symbol_table_->get_value_at_scope(term,subgroup_variable);
  		if(subgroup_scope_value != nullptr) {
  			has_string_formula = true;
  			if(or_values.find(group) == or_values.end()) {
  				or_values[group] = subgroup_scope_value->clone();
  			} else {
  				auto old_value = or_values[group];
  				or_values[group] = or_values[group]->union_(subgroup_scope_value);
  				delete old_value;
  			}
  			is_satisfiable = or_values[group]->is_satisfiable() or is_satisfiable;
  			symbol_table_->clear_value(subgroup_variable,term);
  		}
  	}
  	symbol_table_->pop_scope();
  }

  DVLOG(VLOG_LEVEL) << "collect child results end: " << *or_term << "@" << or_term;

  DVLOG(VLOG_LEVEL) << "update result start: " << *or_term << "@" << or_term;

  /**
   * If or term does not have string formula, but we end up being here:
   * 1) Or term is under a conjunction and other conjunction terms has string formula.
   *  Here, variables appearing in string term will be unconstrained.
   * 2) We are visited or term second time for some mixed constraints, for this we do an unnecessary
   *  intersection below with any string, we can avoid that with more checks later!!!
   */

  if (has_string_formula) {
  	for(auto& iter : or_values) {
  		symbol_table_->IntersectValue(iter.first,iter.second);
  		is_satisfiable = symbol_table_->get_value(iter.first)->is_satisfiable() and is_satisfiable;
  		if(not is_satisfiable) {
  			break;
  		}
  	}

  	for(auto &iter : or_values) {
  		delete iter.second;
  		iter.second = nullptr;
  	}

  	auto satisfiable_value = new Value(is_satisfiable);
		symbol_table_->IntersectValue(group_name,satisfiable_value);
		delete satisfiable_value;
  }
  DVLOG(VLOG_LEVEL) << "update result end: " << *or_term << "@" << or_term;
}

std::string StringConstraintSolver::get_string_variable_name(SMT::Term_ptr term) {
  Term_ptr key = term;
  auto it1 = term_value_index_.find(term);
  if (it1 != term_value_index_.end()) {
    key = it1->second;
  }

  return symbol_table_->get_var_name_for_node(key, Variable::Type::STRING);
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
