#include "ImplicationRunner.h"

#include <glog/logging.h>
#include <glog/vlog_is_on.h>
#include <cstdbool>
#include <iostream>
#include <iterator>
#include <string>
#include <utility>

#include "smt/ast.h"
#include "smt/Visitor.h"
#include "utils/List.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
const int ImplicationRunner::VLOG_LEVEL = 20;

ImplicationRunner::ImplicationRunner(Script_ptr script, SymbolTable_ptr symbol_table)
  : AstTraverser(script),
    symbol_table_(symbol_table) {
  setCallbacks();
}

ImplicationRunner::~ImplicationRunner() {
}

void ImplicationRunner::start() {
  DVLOG(VLOG_LEVEL) << "Starting the Implication Runner";

  symbol_table_->push_scope(root, false);
  visitScript(root);
  symbol_table_->pop_scope();

  end();
}

void ImplicationRunner::end() {
}

void ImplicationRunner::setCallbacks() {
  auto term_callback = [this] (Term_ptr term) -> bool {
    switch (term->type()) {
    case Term::Type::TERMCONSTANT: {
      return false;
    }
    default:
      return true;
    }
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

void ImplicationRunner::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void ImplicationRunner::visitAnd(And_ptr and_term) {
  eq_count = 0;
  count = 0;
  int i = 0;
  while(i < and_term->term_list->size()) {
    current_and_ = and_term;
    visit(and_term->term_list->at(i));
    current_and_ = nullptr;
    i++;
  }
}

void ImplicationRunner::visitOr(Or_ptr or_term) {
  for (auto& term : * (or_term->term_list)) {
    symbol_table_->push_scope(term, false);
    visit(term);
    symbol_table_->pop_scope();
  }
}

void ImplicationRunner::visitEq(Eq_ptr eq_term) {
  if (Concat_ptr left_id = dynamic_cast<Concat_ptr>(eq_term->left_term)) {
    if (Concat_ptr right_id = dynamic_cast<Concat_ptr>(eq_term->right_term)) {
//      Term_ptr implication_term = new Eq(get_length(left_id), get_length(right_id));
//      current_and_->term_list->push_back(implication_term);
    } else if (!is_precise(left_id) or !dynamic_cast<QualIdentifier_ptr>(eq_term->right_term)) {
//      Term_ptr implication_term = new Eq(get_length(left_id), get_length(eq_term->right_term));
//      current_and_->term_list->push_back(implication_term);
      if (QualIdentifier_ptr right_variable = dynamic_cast<QualIdentifier_ptr>(eq_term->right_term)) {
        if (Option::Solver::ENABLE_RELATIONAL_STRING_AUTOMATA) {
          Term_ptr implication_term_begins = new Begins(right_variable->clone(), left_id->term_list->front()->clone());
          current_and_->term_list->push_back(implication_term_begins);
        }
      }
    }
  } else if (Concat_ptr right_id = dynamic_cast<Concat_ptr>(eq_term->right_term)) {
    if (!is_precise(right_id) or !dynamic_cast<QualIdentifier_ptr>(eq_term->left_term)) {
      //Term_ptr implication_term = new Eq(get_length(eq_term->left_term), get_length(right_id));
      //current_and_->term_list->push_back(implication_term);
      if (QualIdentifier_ptr left_variable = dynamic_cast<QualIdentifier_ptr>(eq_term->left_term)) {
        if (Option::Solver::ENABLE_RELATIONAL_STRING_AUTOMATA) {
          Term_ptr implication_term_begins = new Begins(left_variable->clone(), right_id->term_list->front()->clone());
          current_and_->term_list->push_back(implication_term_begins);
        }
/*
        if(count < 20) {
          count++;
          Term_ptr implication_term_ends = new Ends(left_variable->clone(), right_id->term_list->back()->clone());
          current_and_->term_list->push_back(implication_term_ends);
        }
*/
      }
    }
  }
}


void ImplicationRunner::visitContains(Contains_ptr contains) {

  if (Option::Solver::LIA_ENGINE_ENABLED) {
    Term_ptr subject_length = get_length(contains->subject_term);
    Term_ptr search_length = get_length(contains->search_term);
    Term_ptr implication_term = new Ge(subject_length, search_length);
    current_and_->term_list->push_back(implication_term);
  }

}



void ImplicationRunner::visitEnds(Ends_ptr ends) {
/*
  if (Option::Solver::LIA_ENGINE_ENABLED) {
    Term_ptr subject_length = get_length(ends->subject_term);
    Term_ptr search_length = get_length(ends->search_term);
    Term_ptr implication_term = new Ge(subject_length, search_length);
    current_and_->term_list->push_back(implication_term);
  }
*/
}



void ImplicationRunner::visitNotContains(NotContains_ptr not_contains) {
  if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(not_contains->subject_term)) {
    if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(not_contains->search_term)) {
      if (Option::Solver::ENABLE_RELATIONAL_STRING_AUTOMATA) {
        NotBegins_ptr implication_term = new NotBegins(not_contains->subject_term->clone(), not_contains->search_term->clone());
        current_and_->term_list->push_back(implication_term);
      }
    }
  }

}

void ImplicationRunner::visitNotEnds(NotEnds_ptr not_ends) {
  if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(not_ends->subject_term)) {
    if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(not_ends->search_term)) {
      if (Option::Solver::ENABLE_RELATIONAL_STRING_AUTOMATA) {
        NotEq_ptr implication_term = new NotEq(not_ends->subject_term->clone(), not_ends->search_term->clone());
        current_and_->term_list->push_back(implication_term);
      }
    }
  }
}

Term_ptr ImplicationRunner::get_length(Term_ptr term) {
  if (TermConstant_ptr constant = dynamic_cast<TermConstant_ptr>(term)) {
    return get_length_constant(constant);
  }
  if (Concat_ptr concat = dynamic_cast<Concat_ptr>(term)) {
    return get_length_concat(concat);
  }
  return new Len(term->clone());
}

TermConstant_ptr ImplicationRunner::get_length_constant(TermConstant_ptr term_constant) {
  int len = term_constant->getValue().length();
  std::string str_len = std::to_string(len);
  return new TermConstant(new Primitive(str_len, Primitive::Type::NUMERAL));

}

Plus_ptr ImplicationRunner::get_length_concat(Concat_ptr concat) {
  TermList_ptr term_list = new TermList();
  for (auto& term_ptr : * (concat->term_list)) {
    //Convert length directly to an integer if the term is a constant.
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term_ptr)) {
      term_list->push_back(get_length(term_constant));
    } else {
      term_list->push_back(new Len(term_ptr->clone()));
    }
  }
  return new Plus(term_list);
}


bool ImplicationRunner::is_precise(Concat_ptr concat) {
  if (TermConstant_ptr right = dynamic_cast<TermConstant_ptr>(concat->term_list->back())) {
    //is of the form x."a" and x."a" = y is aleady precise. 
    return true;
  }
  return false;
}




}  //Vlab
}  //Solver