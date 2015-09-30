/*
 * SyntacticProcessor.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#include "SyntacticProcessor.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int SyntacticProcessor::VLOG_LEVEL = 20;

SyntacticProcessor::SyntacticProcessor(Script_ptr script) : AstTraverser (script) {
  setCallbacks();
}

SyntacticProcessor::~SyntacticProcessor() {
}

void SyntacticProcessor::start() {
  convertAssertsToAnd();
  visitScript(root);
}

void SyntacticProcessor::end() {
}

void SyntacticProcessor::setCallbacks() {
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

void SyntacticProcessor::convertAssertsToAnd() {
  CommandList_ptr commands = root->command_list;
  Assert_ptr current_assert = nullptr;
  And_ptr and_term = nullptr;
  TermList_ptr term_list = nullptr;

  if (commands->size() > 1) {
    term_list = new TermList();
    for (auto command : *commands) {
      current_assert = dynamic_cast<Assert_ptr>(command);
      if (current_assert) {
        term_list->push_back(current_assert->term);
        current_assert->term = nullptr;
        delete current_assert;
      }
    }
    commands->clear();
    and_term = new And(term_list);
    current_assert = new Assert(and_term);
    commands->push_back(current_assert);
  }
}

/**
 * Applies De Morgan's Law and push negations down
 */
void SyntacticProcessor::visitNot(Not_ptr not_term) {
  switch (not_term->term->getType()) {
  case Term::Type::AND: {
    DVLOG(VLOG_LEVEL) << "push negation '(not (" << *not_term->term << " ... ))'";
    Term_ptr* reference_term = term_stack.top();
    And_ptr and_term = dynamic_cast<And_ptr>(not_term->term);

    for (auto& sub_term : *and_term->term_list) {
      Not_ptr sub_not_term = new Not(sub_term);
      sub_term = sub_not_term;
    }

    Or_ptr or_term = new Or(and_term->term_list);
    and_term->term_list = nullptr;
    delete not_term;

    *reference_term = or_term;
    visitOr(or_term);
    break;
  }
  case Term::Type::OR: {
    DVLOG(VLOG_LEVEL) << "pushNegations '(not (" << *not_term->term << " ... ))'";
    Term_ptr* reference_term = term_stack.top();
    Or_ptr or_term = dynamic_cast<Or_ptr>(not_term->term);

    for (auto& sub_term : *or_term->term_list) {
      Not_ptr sub_not_term = new Not(sub_term);
      sub_term = sub_not_term;
    }

    And_ptr and_term = new And(or_term->term_list);
    or_term->term_list = nullptr;
    delete not_term;

    *reference_term = and_term;
    visitAnd(and_term);
    break;
  }
  case Term::Type::NOT: {
    DVLOG(VLOG_LEVEL) << "pushNegations '(not (" << *not_term->term << " ... ))'";
    Term_ptr* reference_term = term_stack.top();
    Not_ptr sub_not_term = dynamic_cast<Not_ptr>(not_term->term);

    *reference_term = sub_not_term->term;
    sub_not_term->term = nullptr;
    delete not_term;
    visit(*reference_term);
    break;
  }
  default:
    visit(not_term->term);
    break;
  }
}

} /* namespace Solver */
} /* namespace Vlab */
