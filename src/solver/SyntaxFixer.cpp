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
  preProcessNegations();
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

/**
 * Applies De Morgan's Law and push negations down
 * Handles negations syntacticly if possible
 */
void SyntaxFixer::preProcessNegations() {
  PreOrderTraversal preorder_traversal(root);
  auto term_callback = [&preorder_traversal] (Term_ptr term) -> bool {
    if (Term::Type::NOT == term->getType()) {
      Not_ptr not_term = dynamic_cast<Not_ptr>(term);
      DVLOG(VLOG_LEVEL) << "preProcessNegations '(not (" << *not_term->term << " ... ))'";
      switch (not_term->term->getType()) {
      case Term::Type::AND: {
        Term_ptr* reference_term = preorder_traversal.top();
        And_ptr and_term = dynamic_cast<And_ptr>(not_term->term);

        for (auto& sub_term : *and_term->term_list) {
          Not_ptr sub_not_term = new Not(sub_term);
          sub_term = sub_not_term;
        }

        Or_ptr or_term = new Or(and_term->term_list);
        and_term->term_list = nullptr;
        delete not_term;

        *reference_term = or_term;
        preorder_traversal.visitOr(or_term);
        return false;
      }
      case Term::Type::OR: {
        Term_ptr* reference_term = preorder_traversal.top();
        Or_ptr or_term = dynamic_cast<Or_ptr>(not_term->term);

        for (auto& sub_term : *or_term->term_list) {
          Not_ptr sub_not_term = new Not(sub_term);
          sub_term = sub_not_term;
        }

        And_ptr and_term = new And(or_term->term_list);
        or_term->term_list = nullptr;
        delete not_term;

        *reference_term = and_term;
        preorder_traversal.visitAnd(and_term);
        return false;
      }
      case Term::Type::NOT: {
        Term_ptr* reference_term = preorder_traversal.top();
        Not_ptr sub_not_term = dynamic_cast<Not_ptr>(not_term->term);

        *reference_term = sub_not_term->term;
        sub_not_term->term = nullptr;
        delete not_term;
        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::EQ: {
        Term_ptr* reference_term = preorder_traversal.top();
        Eq_ptr eq_term = dynamic_cast<Eq_ptr>(not_term->term);
        NotEq_ptr not_eq_term = new NotEq(eq_term->left_term, eq_term->right_term);
        eq_term->left_term = nullptr; eq_term->right_term = nullptr;

        *reference_term = not_eq_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::NOTEQ: {
        Term_ptr* reference_term = preorder_traversal.top();
        NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>(not_term->term);
        Eq_ptr eq_term = new Eq(not_eq_term->left_term, not_eq_term->right_term);
        not_eq_term->left_term = nullptr; not_eq_term->right_term = nullptr;

        *reference_term = eq_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::GT: {
        Term_ptr* reference_term = preorder_traversal.top();
        Gt_ptr gt_term = dynamic_cast<Gt_ptr>(not_term->term);
        Le_ptr le_term = new Le(gt_term->left_term, gt_term->right_term);
        gt_term->left_term = nullptr; gt_term->right_term = nullptr;

        *reference_term = le_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::GE: {
        Term_ptr* reference_term = preorder_traversal.top();
        Ge_ptr ge_term = dynamic_cast<Ge_ptr>(not_term->term);
        Lt_ptr lt_term = new Lt(ge_term->left_term, ge_term->right_term);
        ge_term->left_term = nullptr; ge_term->right_term = nullptr;

        *reference_term = lt_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::LT: {
        Term_ptr* reference_term = preorder_traversal.top();
        Lt_ptr lt_term = dynamic_cast<Lt_ptr>(not_term->term);
        Ge_ptr ge_term = new Ge(lt_term->left_term, lt_term->right_term);
        lt_term->left_term = nullptr; lt_term->right_term = nullptr;

        *reference_term = ge_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::LE: {
        Term_ptr* reference_term = preorder_traversal.top();
        Le_ptr le_term = dynamic_cast<Le_ptr>(not_term->term);
        Gt_ptr gt_term = new Gt(le_term->left_term, le_term->right_term);
        le_term->left_term = nullptr; le_term->right_term = nullptr;

        *reference_term = gt_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::IN: {
        Term_ptr* reference_term = preorder_traversal.top();
        In_ptr in_term = dynamic_cast<In_ptr>(not_term->term);
        NotIn_ptr not_in_term = new NotIn(in_term->left_term, in_term->right_term);
        in_term->left_term = nullptr; in_term->right_term = nullptr;

        *reference_term = not_in_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::NOTIN: {
        Term_ptr* reference_term = preorder_traversal.top();
        NotIn_ptr not_in_term = dynamic_cast<NotIn_ptr>(not_term->term);
        In_ptr in_term = new In(not_in_term->left_term, not_in_term->right_term);
        not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;

        *reference_term = in_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::CONTAINS: {
        Term_ptr* reference_term = preorder_traversal.top();
        Contains_ptr contains_term = dynamic_cast<Contains_ptr>(not_term->term);
        NotContains_ptr not_contains_term = new NotContains(contains_term->subject_term, contains_term->search_term);
        contains_term->subject_term = nullptr; contains_term->search_term = nullptr;

        *reference_term = not_contains_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::NOTCONTAINS: {
        Term_ptr* reference_term = preorder_traversal.top();
        NotContains_ptr not_contains_term = dynamic_cast<NotContains_ptr>(not_term->term);
        Contains_ptr contains_term = new Contains(not_contains_term->subject_term, not_contains_term->search_term);
        not_contains_term->subject_term = nullptr; not_contains_term->search_term = nullptr;

        *reference_term = contains_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::BEGINS: {
        Term_ptr* reference_term = preorder_traversal.top();
        Begins_ptr begins_term = dynamic_cast<Begins_ptr>(not_term->term);
        NotBegins_ptr not_begins_term = new NotBegins(begins_term->subject_term, begins_term->search_term);
        begins_term->subject_term = nullptr; begins_term->search_term = nullptr;

        *reference_term = not_begins_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::NOTBEGINS: {
        Term_ptr* reference_term = preorder_traversal.top();
        NotBegins_ptr not_begins_term = dynamic_cast<NotBegins_ptr>(not_term->term);
        Begins_ptr begins_term = new Begins(not_begins_term->subject_term, not_begins_term->search_term);
        not_begins_term->subject_term = nullptr; not_begins_term->search_term = nullptr;

        *reference_term = begins_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::ENDS: {
        Term_ptr* reference_term = preorder_traversal.top();
        Ends_ptr ends_term = dynamic_cast<Ends_ptr>(not_term->term);
        NotEnds_ptr not_ends_term = new NotEnds(ends_term->subject_term, ends_term->search_term);
        ends_term->subject_term = nullptr; ends_term->search_term = nullptr;

        *reference_term = not_ends_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      case Term::Type::NOTENDS: {
        Term_ptr* reference_term = preorder_traversal.top();
        NotEnds_ptr not_ends_term = dynamic_cast<NotEnds_ptr>(not_term->term);
        Ends_ptr ends_term = new Ends(not_ends_term->subject_term, not_ends_term->search_term);
        not_ends_term->subject_term = nullptr; not_ends_term->search_term = nullptr;

        *reference_term = ends_term;
        delete not_term;

        preorder_traversal.visit(*reference_term);
        return false;
      }
      default:
        return true;
      }
    }
    return true;
  };

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  preorder_traversal.setCommandCallback(command_callback);
  preorder_traversal.setTermCallback(term_callback);
  preorder_traversal.start();
}

void SyntaxFixer::convertToDNF() {
}

} /* namespace Solver */
} /* namespace Vlab */
