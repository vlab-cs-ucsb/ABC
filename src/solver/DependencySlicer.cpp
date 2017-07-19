#include "DependencySlicer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
const int DependencySlicer::VLOG_LEVEL = 20;

DependencySlicer::DependencySlicer(Script_ptr script, SymbolTable_ptr symbol_table,
                                   ConstraintInformation_ptr constraint_information)
    : AstTraverser(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      current_term_(nullptr) {
  setCallbacks();
}

DependencySlicer::~DependencySlicer() {
}

void DependencySlicer::start() {
  DVLOG(VLOG_LEVEL) << "Starting the Dependency Slicer";

  symbol_table_->push_scope(root_, false);
  visitScript(root_);
  symbol_table_->pop_scope();

  end();
}

void DependencySlicer::end() {
//#ifndef NDEBUG
//  if (VLOG_IS_ON(VLOG_LEVEL)) {
//    for (auto& c : constraint_information_->get_components()){
//      DVLOG(VLOG_LEVEL) << c;
//      DVLOG(VLOG_LEVEL) <<  dynamic_cast<And_ptr>(c)->term_list->size();
//    }
//  }
//#endif
}

void DependencySlicer::setCallbacks() {
  if (Option::Solver::ENABLE_DEPENDENCY_ANALYSIS) {
    auto term_callback = [this] (Term_ptr term) -> bool {
      switch (term->type()) {
        case Term::Type::TERMCONSTANT: {
          return false;
        }
        default:
        return true;
      }
    };
    setTermPreCallback(term_callback);
  } else {
    auto term_callback = [this] (Term_ptr term) -> bool {
      switch (term->type()) {
        case Term::Type::AND: {
          return true;
        }
        case Term::Type::OR: {
          return true;
        }
        default:
        return false;
      }
    };
    setTermPreCallback(term_callback);
  }

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  setCommandPreCallback(command_callback);
}

void DependencySlicer::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void DependencySlicer::visitAnd(And_ptr and_term) {
  for (auto& term : *(and_term->term_list)) {
    current_term_ = term;
    visit(term);
    current_term_ = nullptr;
  }

  constraint_information_->add_component(and_term);

  if (Option::Solver::ENABLE_DEPENDENCY_ANALYSIS and symbol_table_->top_scope() == root_) {
    auto components = GetComponentsFor(and_term->term_list);
    if (components.size() > 1) {  // and term breaks into multiple components
      DVLOG(VLOG_LEVEL) << "Dividing into components: " << *and_term << "@" << and_term;
      and_term->term_list->clear();
      constraint_information_->remove_component(and_term);
      for (auto sub_term_list : components) {
        And_ptr and_component = new And(sub_term_list);
        constraint_information_->add_component(and_component);
        and_term->term_list->push_back(and_component);
      }
    } else if (components.size() == 1) {
      // deallocate term list to avoid memory leak
      components[0]->clear();
      delete components[0];
    }
  }

  /**
   * If and_term is under a disjunction, and_term must be component.
   * We can still do dependency analysis but, we must treat and_term as a component.
   * During automata construction we watch for the case.
   * This enable us to reduce the size of automaton in case one of the sub component is unsat
   */
  if (Option::Solver::ENABLE_DEPENDENCY_ANALYSIS and symbol_table_->top_scope() != root_) {
    constraint_information_->add_component(and_term);
    ReMapTerms(and_term->term_list, and_term);
  } else {
    // reset data
    clear_mappings();
  }
}

/**
 * No dependency analysis for disjunctions
 */
void DependencySlicer::visitOr(Or_ptr or_term) {
  term_variable_map_[or_term];
  auto it = term_variable_map_.find(or_term);
  LOG(INFO) << 1;
  for (auto& term : *(or_term->term_list)) {
    symbol_table_->push_scope(term, false);
    current_term_ = term;
    visit(term);
    current_term_ = nullptr;
    symbol_table_->pop_scope();
  }
  LOG(INFO) << 2;

  constraint_information_->add_component(or_term);
  LOG(INFO) << 3;

  ReMapTerms(or_term->term_list, or_term);
  LOG(INFO) << 4;

}

/**
 * TODO handle local scopes
 */
void DependencySlicer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table_->get_variable(qi_term->getVarName());
  add_variable_current_term_mapping(variable);
}

void DependencySlicer::add_variable_current_term_mapping(Variable_ptr variable) {
  term_variable_map_[current_term_].insert(variable);
  variable_term_map_[variable].insert(current_term_);
}

void DependencySlicer::clear_mappings() {
  term_variable_map_.clear();
  variable_term_map_.clear();
}

void DependencySlicer::ReMapTerms(TermList_ptr term_list, Term_ptr target_term) {
  DVLOG(VLOG_LEVEL)<< "re-mapping child terms to: " << *target_term << "@" << target_term;
  auto& target_variable_set = term_variable_map_[target_term];
  for (const auto term : *term_list) {
    for (const auto variable : term_variable_map_[term]) {
      target_variable_set.insert(variable);
      auto& variable_map = variable_term_map_[variable];
      variable_map.erase(term);
      variable_map.insert(target_term);
    }
    term_variable_map_.erase(term);
  }
}

/**
 * Creates a separate term list for each group of terms that are dependent to each other
 */
std::vector<TermList_ptr> DependencySlicer::GetComponentsFor(TermList_ptr term_list) {
  std::map<Term_ptr, bool> term_processed;
  std::map<Variable_ptr, bool> is_queued;
  std::vector<TermList_ptr> components;
  for (auto term : *term_list) {
    if (not term_processed[term]) {
      term_processed[term] = true;
      std::set<Term_ptr> dependent_terms;
      dependent_terms.insert(term);

      // Get initial work list
      std::queue<Variable_ptr> worklist;
      for (auto variable : term_variable_map_[term]) {
        if (not is_queued[variable]) {
          worklist.push(variable);
          is_queued[variable] = true;
        }
      }

      // Figure out all dependent terms
      while (not worklist.empty()) {
        auto variable = worklist.front();
        worklist.pop();
        for (auto variable_term : variable_term_map_[variable]) {
          if (not term_processed[variable_term]) {
            term_processed[variable_term] = true;
            dependent_terms.insert(variable_term);
            for (auto next_variable : term_variable_map_[variable_term]) {
              if (not is_queued[next_variable]) {
                worklist.push(next_variable);
                is_queued[next_variable] = true;
              }
            }
          }
        }
      }

      TermList_ptr current_component = new TermList();
      current_component->insert(current_component->begin(), dependent_terms.begin(), dependent_terms.end());
      components.push_back(current_component);
    }
  }
  return components;
}

}  //Vlab
}  //Solver
