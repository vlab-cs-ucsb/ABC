/*
 * VariableCollector.cpp
 *
 *  Created on: May 4, 2015
 *      Author: baki
 */

#include "VariableCollector.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int VariableCollector::VLOG_LEVEL = 21;

VariableCollector::VariableCollector(Script_ptr script, SymbolTable_ptr symbol_table)
        : AstTraverser (script), symbol_table (symbol_table) {
  setCallbacks();
}

VariableCollector::~VariableCollector() {
}

void VariableCollector::start() {
  internal = true;
  symbol_table->reset_count();
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
  end();
}

void VariableCollector::end() {
}

void VariableCollector::setCallbacks() {
  auto term_callback = [this] (Term_ptr term) -> bool {
    switch (term->getType()) {
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


void VariableCollector::visitOr(Or_ptr or_term) {
  //Still figuring out how to handle ors. 
  for (auto& term : *(or_term->term_list)) {
    if (internal){
      symbol_table->push_scope(term);
      visit(term);
      symbol_table->pop_scope();
    }
    else {
      visit(term);
    }
  }
}

void VariableCollector::visitAssert(Assert_ptr assert_term){
  visit(assert_term->term);
}

//
void VariableCollector::visitAnd(And_ptr and_term) {
  for (auto& term : *(and_term->term_list)) {
    if (internal) {
      symbol_table->push_scope(term);
      internal = false;
      visit(term);
      internal = true;
      symbol_table->pop_scope();
      }
    else{
      visit(term);
    }
  }
}

void VariableCollector::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  symbol_table->increment_count(symbol_table->getVariable(qi_term->getVarName()));
}

void VariableCollector::visitUnknownTerm(SMT::Unknown_ptr unknown_term) {
  for(auto& term : *unknown_term->term_list) {
    visit(term);
  }
}

} /* namespace Solver */
} /* namespace Vlab */