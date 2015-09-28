/*
 * SyntaxFixer.cpp
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#include "SyntaxFixer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int SyntaxFixer::VLOG_LEVEL = 20;

SyntaxFixer::SyntaxFixer(Script_ptr script) : root (script) {
}

SyntaxFixer::~SyntaxFixer() {
}

void SyntaxFixer::start() {
  convertAssertsToAnd();
}

void SyntaxFixer::end() {
}

void SyntaxFixer::convertAssertsToAnd() {
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

void SyntaxFixer::applyDeMorgansLaw() {

}

void SyntaxFixer::convertToDNF() {
}

} /* namespace Solver */
} /* namespace Vlab */
