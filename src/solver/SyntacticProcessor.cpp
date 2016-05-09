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
 * TODO pull not processing in SyntacticOptimizer into here
 */
void SyntacticProcessor::visitNot(Not_ptr not_term) {
  Term_ptr* reference_term = top();

  if (And_ptr and_term = dynamic_cast<And_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "pushNegations '(not (" << *not_term->term << " ... ))'";

    for (auto& sub_term : *and_term->term_list) {
      Not_ptr sub_not_term = new Not(sub_term);
      sub_term = sub_not_term;
    }

    Or_ptr or_term = new Or(and_term->term_list);
    and_term->term_list = nullptr;
    delete not_term;

    *reference_term = or_term;
    visitOr(or_term);
  } else if (Or_ptr or_term = dynamic_cast<Or_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "pushNegations '(not (" << *not_term->term << " ... ))'";

    for (auto& sub_term : *or_term->term_list) {
      Not_ptr sub_not_term = new Not(sub_term);
      sub_term = sub_not_term;
    }

    And_ptr and_term = new And(or_term->term_list);
    or_term->term_list = nullptr;
    delete not_term;

    *reference_term = and_term;
    visitAnd(and_term);
  } else if (Not_ptr sub_not_term = dynamic_cast<Not_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (not a) to a";

    *reference_term = sub_not_term->term;
    sub_not_term->term = nullptr;
    delete not_term;
    visit(*reference_term);
  } else if (Eq_ptr eq_term = dynamic_cast<Eq_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (= ...)) to (!= ...)";

    NotEq_ptr not_eq_term = new NotEq(eq_term->left_term, eq_term->right_term);
    eq_term->left_term = nullptr; eq_term->right_term = nullptr;
    delete not_term;

    *reference_term = not_eq_term;
    visitNotEq(not_eq_term);
  } else if (NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (!= ...)) to (= ...)";

    Eq_ptr eq_term = new Eq(not_eq_term->left_term, not_eq_term->right_term);
    not_eq_term->left_term = nullptr; not_eq_term->right_term = nullptr;
    delete not_term;

    *reference_term = eq_term;
    visitEq(eq_term);
  } else if (Gt_ptr gt_term = dynamic_cast<Gt_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (> ...)) to (<= ...)";

    Le_ptr le_term = new Le(gt_term->left_term, gt_term->right_term);
    gt_term->left_term = nullptr; gt_term->right_term = nullptr;
    delete not_term;

    *reference_term = le_term;
    visitLe(le_term);
  } else if (Ge_ptr ge_term = dynamic_cast<Ge_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (>= ...)) to (< ...)";

    Lt_ptr lt_term = new Lt(ge_term->left_term, ge_term->right_term);
    ge_term->left_term = nullptr; ge_term->right_term = nullptr;
    delete not_term;

    *reference_term = lt_term;
    visitLt(lt_term);
  } else if (Lt_ptr lt_term = dynamic_cast<Lt_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (< ...)) to (>= ...)";
    Ge_ptr ge_term = new Ge(lt_term->left_term, lt_term->right_term);
    lt_term->left_term = nullptr; lt_term->right_term = nullptr;
    delete not_term;

    *reference_term = ge_term;
    visitGe(ge_term);
  } else if (Le_ptr le_term = dynamic_cast<Le_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (<= ...)) to (> ...)";
    Gt_ptr gt_term = new Gt(le_term->left_term, le_term->right_term);
    le_term->left_term = nullptr; le_term->right_term = nullptr;
    delete not_term;

    *reference_term = gt_term;
    visitGt(gt_term);
  } else if (In_ptr in_term = dynamic_cast<In_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (in ...)) to (notIn ...)";

    NotIn_ptr not_in_term = new NotIn(in_term->left_term, in_term->right_term);
    in_term->left_term = nullptr; in_term->right_term = nullptr;
    delete not_term;

    *reference_term = not_in_term;
    visitNotIn(not_in_term);
  } else if (NotIn_ptr not_in_term = dynamic_cast<NotIn_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (notIn ...)) to (in ...)";

    In_ptr in_term = new In(not_in_term->left_term, not_in_term->right_term);
    not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;
    delete not_term;

    *reference_term = in_term;
    visitIn(in_term);
  } else if (Contains_ptr contains_term = dynamic_cast<Contains_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (contains ...)) to (notContains ...)";

    NotContains_ptr not_contains_term = new NotContains(contains_term->subject_term, contains_term->search_term);
    contains_term->subject_term = nullptr; contains_term->search_term = nullptr;
    delete not_term;

    *reference_term = not_contains_term;
    visitNotContains(not_contains_term);
  } else if (NotContains_ptr not_contains_term = dynamic_cast<NotContains_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (notContains ...)) to (contains ...)";

    Contains_ptr contains_term = new Contains(not_contains_term->subject_term, not_contains_term->search_term);
    not_contains_term->subject_term = nullptr; not_contains_term->search_term = nullptr;
    delete not_term;

    *reference_term = contains_term;
    visitContains(contains_term);
  } else if (Begins_ptr begins_term = dynamic_cast<Begins_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (begins ...)) to (notBegins ...)";

    NotBegins_ptr not_begins_term = new NotBegins(begins_term->subject_term, begins_term->search_term);
    begins_term->subject_term = nullptr; begins_term->search_term = nullptr;
    delete not_term;

    *reference_term = not_begins_term;
    visitNotBegins(not_begins_term);
  } else if (NotBegins_ptr not_begins_term = dynamic_cast<NotBegins_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (notBegins ...)) to (begins ...)";

    Begins_ptr begins_term = new Begins(not_begins_term->subject_term, not_begins_term->search_term);
    not_begins_term->subject_term = nullptr; not_begins_term->search_term = nullptr;
    delete not_term;

    *reference_term = begins_term;
    visitBegins(begins_term);
  } else if (Ends_ptr ends_term = dynamic_cast<Ends_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (ends ...)) to (notEnds ...)";

    NotEnds_ptr not_ends_term = new NotEnds(ends_term->subject_term, ends_term->search_term);
    ends_term->subject_term = nullptr; ends_term->search_term = nullptr;
    delete not_term;

    *reference_term = not_ends_term;
    visitNotEnds(not_ends_term);
  } else if (NotEnds_ptr not_ends_term = dynamic_cast<NotEnds_ptr>(not_term->term)) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (notEnds ...)) to (ends ...)";

    Ends_ptr ends_term = new Ends(not_ends_term->subject_term, not_ends_term->search_term);
    not_ends_term->subject_term = nullptr; not_ends_term->search_term = nullptr;
    delete not_term;

    *reference_term = ends_term;
    visitEnds(ends_term);
  } else {
    visit(not_term->term);
  }
}

/**
 * Check if second parameter is a decimal representation of an ASCII char and convert it into string
 * TODO that should be supported during automaton construction
 */
void SyntacticProcessor::visitIndexOf(IndexOf_ptr index_of_term) {
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(index_of_term->search_term)) {
    check_and_convert_numeral_to_char(term_constant);
  }
  visit(index_of_term->subject_term);
  if (IndexOf::Mode::FROMFIRSTOF == index_of_term->getMode() or
          IndexOf::Mode::FROMLASTOF == index_of_term->getMode()) {
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(index_of_term->from_index)) {
      check_and_convert_numeral_to_char(term_constant);
    }
    visit(index_of_term->from_index);
  }
}

void SyntacticProcessor::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(last_index_of_term->search_term)) {
    check_and_convert_numeral_to_char(term_constant);
  }
  visit(last_index_of_term->subject_term);
  if (LastIndexOf::Mode::FROMFIRSTOF == last_index_of_term->getMode() or
          LastIndexOf::Mode::FROMLASTOF == last_index_of_term->getMode()) {
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(last_index_of_term->from_index)) {
      check_and_convert_numeral_to_char(term_constant);
    }
    visit(last_index_of_term->from_index);
  }
}

void SyntacticProcessor::check_and_convert_numeral_to_char(TermConstant_ptr term_constant) {
  switch (term_constant->getValueType()) {
    case Primitive::Type::BINARY:
      LOG(FATAL)<< "Implement me";
      break;
    case Primitive::Type::HEXADECIMAL:
      LOG(FATAL)<< "Implement me";
      break;
    case Primitive::Type::NUMERAL: {
      int value = std::stoi(term_constant->getValue());
      std::stringstream ss;
      ss << (unsigned char)value;
      term_constant->primitive->setData(ss.str());
      term_constant->primitive->setType(Primitive::Type::STRING);
      break;
    }
    default:
      break;
  }
}


} /* namespace Solver */
} /* namespace Vlab */
