/*
 * SyntacticOptimizer.cpp
 *
 *  Created on: Apr 28, 2015
 *      Author: baki
 */

#include "SyntacticOptimizer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int SyntacticOptimizer::VLOG_LEVEL = 18;

SyntacticOptimizer::SyntacticOptimizer(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table), current_assert(nullptr) {
}

SyntacticOptimizer::~SyntacticOptimizer() {
}

void SyntacticOptimizer::start() {
  visit(root);
  end();
}

void SyntacticOptimizer::end() {
}

void SyntacticOptimizer::visitScript(Script_ptr script) {
  CommandList_ptr commands = script->command_list;
  for (auto iter = commands->begin(); iter != commands->end();) {
    current_assert = nullptr;
    visit(*iter);
    CHECK_NOTNULL(current_assert);
    if (check_bool_constant_value(current_assert->term, "true")) {
      delete (*iter);
      iter = commands->erase(iter);
      DVLOG(VLOG_LEVEL) << "remove: 'true' assert command";
    } else {
      iter++;
    }
  }

  if (script->command_list->empty()) {
    script->command_list->push_back(new Assert(generate_dummy_term()));
  }
}

void SyntacticOptimizer::visitCommand(Command_ptr command) {
}

void SyntacticOptimizer::visitAssert(Assert_ptr assert_command) {
  current_assert = assert_command;
  visit_and_callback(current_assert->term);
}

void SyntacticOptimizer::visitTerm(Term_ptr term) {
}

void SyntacticOptimizer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void SyntacticOptimizer::visitExists(Exists_ptr exists_term) {
}

void SyntacticOptimizer::visitForAll(ForAll_ptr for_all_term) {
}

void SyntacticOptimizer::visitLet(Let_ptr let_term) {
}

void SyntacticOptimizer::visitAnd(And_ptr and_term) {
  bool has_false_term = false;
  std::vector<TermList> or_term_lists;
  for (auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
    visit_and_callback(*iter);
    if (check_bool_constant_value(*iter, "true")) {
      DVLOG(VLOG_LEVEL) << "remove: 'true' constant from 'and'";
      delete (*iter);
      iter = and_term->term_list->erase(iter);
    } else if (check_bool_constant_value(*iter, "false")) {
      has_false_term = true;
      break;
    } else if (Term::Type::OR == (*iter)->getType()) {
      Or_ptr or_term = dynamic_cast<Or_ptr>(*iter);
      or_term_lists.push_back(*or_term->term_list);
      or_term->term_list->clear();
      delete or_term;
      iter = and_term->term_list->erase(iter);
    } else {
      iter++;
    }
  }

  if (has_false_term) {
    add_callback_to_replace_with_bool(and_term, "false");
  } else if (not ( or_term_lists.empty() )) { // convert to DNF
    std::vector<TermList> cartesian = {{}};
    for (auto& term_list_1 : or_term_lists) {
      std::vector<TermList> sub_product;
        for (auto& term_list_2 : cartesian) {
            for (auto& term_1 : term_list_1) {
                TermList term_list_2_clone;
                for (auto& term_2 : term_list_2) {
                  term_list_2_clone.push_back(term_2->clone());
                }
                sub_product.push_back(term_list_2_clone);
                sub_product.back().push_back(term_1->clone());
            }
        }
        // do not allow memory leak
        for (auto& term_list : cartesian) {
          for (auto term : term_list) {
            delete term;
          }
        }
        for (auto& term : term_list_1) {
          delete term; term = nullptr;
        }
        cartesian.clear();
        cartesian.swap(sub_product);
    }

    TermList_ptr or_term_list = new TermList();
    for (auto& term_list : cartesian) {
      for (auto term : *and_term->term_list) {
        term_list.push_back(term->clone());
      }

      TermList_ptr and_term_list = new TermList();
      for (auto term : term_list) { // Associativity
        if (And_ptr sub_and_term = dynamic_cast<And_ptr>(term)) {
          and_term_list->insert(and_term_list->end(), sub_and_term->term_list->begin(), sub_and_term->term_list->end());
        } else {
          and_term_list->push_back(term);
        }
      }

      or_term_list->push_back(new And(and_term_list));
    }

    Or_ptr or_term = new Or(or_term_list);
    callback = [or_term, and_term](Term_ptr& term) mutable {
      term = or_term;
      delete and_term;
    };

  } else if (and_term->term_list->empty()) {
    add_callback_to_replace_with_bool(and_term, "true");
  } else if (and_term->term_list->size() == 1) {
    callback = [and_term](Term_ptr& term) mutable {
      Term_ptr child_term = and_term->term_list->front();
      and_term->term_list->clear();
      delete and_term;
      term = child_term;
    };
  } else {
    DVLOG(VLOG_LEVEL) << "Optimize operation: '" << *and_term;
    TermConstant_ptr initial_term_constant = nullptr;
    int pos = 0;
    for (auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
      if (Term::Type::AND == (*iter)->getType()) { // Associativity
        And_ptr sub_and_term = dynamic_cast<And_ptr>(*iter);
        and_term->term_list->erase(iter);
        and_term->term_list->insert(iter, sub_and_term->term_list->begin(), sub_and_term->term_list->end());
        sub_and_term->term_list->clear();
        delete sub_and_term;
        iter = and_term->term_list->begin() + pos; // insertion invalidates iter, reset it
        continue;
      }
      iter++; pos++;
    }
  }
}

void SyntacticOptimizer::visitOr(Or_ptr or_term) {
  for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
    visit_and_callback(*iter);
    if (check_bool_constant_value(*iter, "false")) {
      DVLOG(VLOG_LEVEL) << "remove: 'false' constant from 'or'";
      delete (*iter);
      iter = or_term->term_list->erase(iter);
    } else {
      iter++;
    }
  }

  if (or_term->term_list->empty()) {
    add_callback_to_replace_with_bool(or_term, "false");
  } else if (or_term->term_list->size() == 1) {
    callback = [or_term](Term_ptr& term) mutable {
      Term_ptr child_term = or_term->term_list->front();
      or_term->term_list->clear();
      delete or_term;
      term = child_term;
    };
  } else {
    DVLOG(VLOG_LEVEL) << "Optimize operation: '" << *or_term;
    TermConstant_ptr initial_term_constant = nullptr;
    int pos = 0;
    for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
      if (Term::Type::OR == (*iter)->getType()) { // Associativity
        Or_ptr sub_or_term = dynamic_cast<Or_ptr>(*iter);
        or_term->term_list->erase(iter);
        or_term->term_list->insert(iter, sub_or_term->term_list->begin(), sub_or_term->term_list->end());
        sub_or_term->term_list->clear();
        delete sub_or_term;
        iter = or_term->term_list->begin() + pos; // insertion invalidates iter, reset it
        continue;
      }
      iter++; pos++;
    }
  }
}

void SyntacticOptimizer::visitNot(Not_ptr not_term) {
  visit_and_callback(not_term->term);

  switch (not_term->term->getType()) {
  case Term::Type::NOT: {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (not a) to a";
    callback = [not_term](Term_ptr& term) mutable {
      Not_ptr child_not = dynamic_cast<Not_ptr>(not_term->term);
      term = child_not->term;
      child_not->term = nullptr;
      delete not_term;
    };
    break;
  }
  case Term::Type::EQ: {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (= ...)) to (!= ...)";
    callback = [not_term](Term_ptr& term) mutable {
      Eq_ptr eq_term = dynamic_cast<Eq_ptr>(not_term->term);
      NotEq_ptr not_eq_term = new NotEq(eq_term->left_term, eq_term->right_term);
      eq_term->left_term = nullptr; eq_term->right_term = nullptr;
      term = not_eq_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::NOTEQ: {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (!= ...)) to (= ...)";
    callback = [not_term](Term_ptr& term) mutable {
    NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>(not_term->term);
    Eq_ptr eq_term = new Eq(not_eq_term->left_term, not_eq_term->right_term);
    not_eq_term->left_term = nullptr; not_eq_term->right_term = nullptr;
    term = eq_term;
    delete not_term;
    };
    break;
  }
  case Term::Type::GT: {
    callback = [not_term](Term_ptr& term) mutable {
      Gt_ptr gt_term = dynamic_cast<Gt_ptr>(not_term->term);
      Le_ptr le_term = new Le(gt_term->left_term, gt_term->right_term);
      gt_term->left_term = nullptr; gt_term->right_term = nullptr;
      term = le_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::GE: {
    callback = [not_term](Term_ptr& term) mutable {
      Ge_ptr ge_term = dynamic_cast<Ge_ptr>(not_term->term);
      Lt_ptr lt_term = new Lt(ge_term->left_term, ge_term->right_term);
      ge_term->left_term = nullptr; ge_term->right_term = nullptr;
      term = lt_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::LT: {
    callback = [not_term](Term_ptr& term) mutable {
      Lt_ptr lt_term = dynamic_cast<Lt_ptr>(not_term->term);
      Ge_ptr ge_term = new Ge(lt_term->left_term, lt_term->right_term);
      lt_term->left_term = nullptr; lt_term->right_term = nullptr;
      term = ge_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::LE: {
    callback = [not_term](Term_ptr& term) mutable {
      Le_ptr le_term = dynamic_cast<Le_ptr>(not_term->term);
      Gt_ptr gt_term = new Gt(le_term->left_term, le_term->right_term);
      le_term->left_term = nullptr; le_term->right_term = nullptr;
      term = gt_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::IN: {
    callback = [not_term](Term_ptr& term) mutable {
      In_ptr in_term = dynamic_cast<In_ptr>(not_term->term);
      NotIn_ptr not_in_term = new NotIn(in_term->left_term, in_term->right_term);
      in_term->left_term = nullptr; in_term->right_term = nullptr;
      term = not_in_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::NOTIN: {
    callback = [not_term](Term_ptr& term) mutable {
      NotIn_ptr not_in_term = dynamic_cast<NotIn_ptr>(not_term->term);
      In_ptr in_term = new In(not_in_term->left_term, not_in_term->right_term);
      not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;
      term = in_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::CONTAINS: {
    callback = [not_term](Term_ptr& term) mutable {
      Contains_ptr contains_term = dynamic_cast<Contains_ptr>(not_term->term);
      NotContains_ptr not_contains_term = new NotContains(contains_term->subject_term, contains_term->search_term);
      contains_term->subject_term = nullptr; contains_term->search_term = nullptr;
      term = not_contains_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::NOTCONTAINS: {
    callback = [not_term](Term_ptr& term) mutable {
      NotContains_ptr not_contains_term = dynamic_cast<NotContains_ptr>(not_term->term);
      Contains_ptr contains_term = new Contains(not_contains_term->subject_term, not_contains_term->search_term);
      not_contains_term->subject_term = nullptr; not_contains_term->search_term = nullptr;
      term = contains_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::BEGINS: {
    callback = [not_term](Term_ptr& term) mutable {
      Begins_ptr begins_term = dynamic_cast<Begins_ptr>(not_term->term);
      NotBegins_ptr not_begins_term = new NotBegins(begins_term->subject_term, begins_term->search_term);
      begins_term->subject_term = nullptr; begins_term->search_term = nullptr;
      term = not_begins_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::NOTBEGINS: {
    callback = [not_term](Term_ptr& term) mutable {
      NotBegins_ptr not_begins_term = dynamic_cast<NotBegins_ptr>(not_term->term);
      Begins_ptr begins_term = new Begins(not_begins_term->subject_term, not_begins_term->search_term);
      not_begins_term->subject_term = nullptr; not_begins_term->search_term = nullptr;
      term = begins_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::ENDS: {
    callback = [not_term](Term_ptr& term) mutable {
      Ends_ptr ends_term = dynamic_cast<Ends_ptr>(not_term->term);
      NotEnds_ptr not_ends_term = new NotEnds(ends_term->subject_term, ends_term->search_term);
      ends_term->subject_term = nullptr; ends_term->search_term = nullptr;
      term = not_ends_term;
      delete not_term;
    };
    break;
  }
  case Term::Type::NOTENDS: {
    callback = [not_term](Term_ptr& term) mutable {
      NotEnds_ptr not_ends_term = dynamic_cast<NotEnds_ptr>(not_term->term);
      Ends_ptr ends_term = new Ends(not_ends_term->subject_term, not_ends_term->search_term);
      not_ends_term->subject_term = nullptr; not_ends_term->search_term = nullptr;
      term = ends_term;
      delete not_term;
    };
    break;
  }
  default:
    break;
  }
}

void SyntacticOptimizer::visitUMinus(UMinus_ptr u_minus_term) {
  visit_and_callback(u_minus_term->term);

  if (Term::Type::UMINUS == u_minus_term->term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- (- a) to a";
    callback = [u_minus_term](Term_ptr& term) mutable {
      UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(u_minus_term->term);
      term = child_u_minus->term;
      child_u_minus->term = nullptr;
      delete u_minus_term;
    };
  }
}

void SyntacticOptimizer::visitMinus(Minus_ptr minus_term) {
  visit_and_callback(minus_term->left_term);
  visit_and_callback(minus_term->right_term);

  if (Term::Type::TERMCONSTANT == minus_term->left_term->getType()
          and Term::Type::TERMCONSTANT == minus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- lc rc) to lc-rc";
    callback = [this, minus_term](Term_ptr& term) mutable {
      TermConstant_ptr left_constant = dynamic_cast<TermConstant_ptr>(minus_term->left_term);
      TermConstant_ptr right_constant = dynamic_cast<TermConstant_ptr>(minus_term->right_term);

      int left_value = std::stoi(left_constant->getValue());
      int right_value = std::stoi(right_constant->getValue());

      int result = left_value - right_value;
      if (result >= 0) {
        term = this->generate_term_constant(std::to_string(result),Primitive::Type::NUMERAL);
      } else {
        term = new UMinus(this->generate_term_constant(std::to_string(-result),Primitive::Type::NUMERAL));
      }
      delete minus_term;
    };
  } else if (Term::Type::TERMCONSTANT == minus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- l 0) to l";
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
    if (term_constant->getValue() == "0") {
      callback = [minus_term](Term_ptr& term) mutable {
        term = minus_term->left_term;
        minus_term->left_term = nullptr;
        delete minus_term;
      };
    }
  } else if (Term::Type::UMINUS == minus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- l (- r) to (+ l r)";
    callback = [minus_term](Term_ptr& term) mutable {
      UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(minus_term->right_term);
      TermList_ptr term_list = new TermList();
      term_list->push_back(minus_term->left_term);
      term_list->push_back(child_u_minus->term);
      term = new Plus(term_list);
      minus_term->left_term = nullptr;
      child_u_minus->term = nullptr;
      delete minus_term;
    };
  }
}

void SyntacticOptimizer::visitPlus(Plus_ptr plus_term) {
  for (auto& term_ptr : *(plus_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "Optimize operation: '" << *plus_term << "'";

  int constant_value = 0;
  int pos = 0;
  for (auto iter = plus_term->term_list->begin(); iter != plus_term->term_list->end();) {
    if (Term::Type::PLUS == (*iter)->getType()) {
      Plus_ptr sub_plus_term = dynamic_cast<Plus_ptr>(*iter);
      plus_term->term_list->erase(iter);
      plus_term->term_list->insert(iter, sub_plus_term->term_list->begin(), sub_plus_term->term_list->end());
      sub_plus_term->term_list->clear();
      delete sub_plus_term;
      iter = plus_term->term_list->begin() + pos; // insertion invalidates iter, reset it
      continue;
    } else if(Term::Type::TERMCONSTANT == (*iter)->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      std::string value = term_constant->getValue();
      constant_value += std::stoi(value);
      delete term_constant; // deallocate
      plus_term->term_list->erase(iter);
      continue;
    } else if (Term::Type::UMINUS == (*iter)->getType()) {
      UMinus_ptr u_minus = dynamic_cast<UMinus_ptr>(*iter);
      if (Term::Type::TERMCONSTANT == u_minus->term->getType()) {
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(u_minus->term);
        std::string value = term_constant->getValue();
        constant_value -= std::stoi(value);
        delete u_minus; // deallocate
        plus_term->term_list->erase(iter);
        continue;
      }
    }
    iter++; pos++;
  }
  if (constant_value != 0) {
    if (constant_value > 0) {
      plus_term->term_list->insert(plus_term->term_list->begin(), generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
    } else {
      UMinus_ptr u_minus = new UMinus(generate_term_constant(std::to_string(-constant_value), Primitive::Type::NUMERAL));
      plus_term->term_list->insert(plus_term->term_list->begin(), u_minus);
    }
  } else if (plus_term->term_list->size() == 0) { // constant is the only term, add it to result
    plus_term->term_list->push_back(generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
  } // else constant value is zero, do not need to add it

  if (plus_term->term_list->size() == 1) {
    callback = [plus_term] (Term_ptr& term) mutable {
      term = plus_term->term_list->front();
      plus_term->term_list->clear();
      delete plus_term;
    };
  }
}

void SyntacticOptimizer::visitTimes(Times_ptr times_term) {
  for (auto& term_ptr : *(times_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "Optimize operation: '" << *times_term << "'";

  int constant_value = 1;
  int pos = 0;
  for (auto iter = times_term->term_list->begin(); iter != times_term->term_list->end();) {
    if (Term::Type::TIMES == (*iter)->getType()) {
      Plus_ptr sub_plus_term = dynamic_cast<Plus_ptr>(*iter);
      times_term->term_list->erase(iter);
      times_term->term_list->insert(iter, sub_plus_term->term_list->begin(), sub_plus_term->term_list->end());
      sub_plus_term->term_list->clear();
      delete sub_plus_term;
      iter = times_term->term_list->begin() + pos; // insertion invalidates iter, reset it
      continue;
    } else if(Term::Type::TERMCONSTANT == (*iter)->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      std::string value = term_constant->getValue();
      constant_value *= std::stoi(value);
      delete term_constant; // deallocate
      times_term->term_list->erase(iter);
      continue;
    } else if (Term::Type::UMINUS == (*iter)->getType()) {
      UMinus_ptr u_minus = dynamic_cast<UMinus_ptr>(*iter);
      if (Term::Type::TERMCONSTANT == u_minus->term->getType()) {
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(u_minus->term);
        std::string value = term_constant->getValue();
        constant_value *= -std::stoi(value);
        delete u_minus; // deallocate
        times_term->term_list->erase(iter);
        continue;
      }
    }
    iter++; pos++;
    if (constant_value == 0) {
      break;
    }
  }


  if (constant_value != 1 and constant_value != 0) {
    if (constant_value > 0) {
      times_term->term_list->insert(times_term->term_list->begin(), generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
    } else {
      UMinus_ptr u_minus = new UMinus(generate_term_constant(std::to_string(-constant_value), Primitive::Type::NUMERAL));
      times_term->term_list->insert(times_term->term_list->begin(), u_minus);
    }
  } else if (times_term->term_list->size() == 0) { // constant is the only term, add it to result
    times_term->term_list->push_back(generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
  } else if (constant_value == 0) { // make it zero
    times_term->term_list->clear();
    times_term->term_list->push_back(generate_term_constant("0", Primitive::Type::NUMERAL));
  } // else constant value is 1, do not need to add it

  if (times_term->term_list->size() == 1) {
    callback = [times_term] (Term_ptr& term) mutable {
      term = times_term->term_list->front();
      times_term->term_list->clear();
      delete times_term;
    };
  }
}

void SyntacticOptimizer::visitEq(Eq_ptr eq_term) {
  visit_and_callback(eq_term->left_term);
  visit_and_callback(eq_term->right_term);

  if (Ast2Dot::isEquivalent(eq_term->left_term, eq_term->right_term)) {
    add_callback_to_replace_with_bool(eq_term, "true");
  } else if (check_and_process_len_transformation(eq_term, eq_term->left_term, eq_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *eq_term << "'";
    if (Ast2Dot::isEquivalent(eq_term->left_term, eq_term->right_term)) {
      add_callback_to_replace_with_bool(eq_term, "true");
    }
  } else if (check_and_process_for_notContains_transformation(eq_term->left_term, eq_term->right_term, -1) or
          check_and_process_for_notContains_transformation(eq_term->right_term, eq_term->left_term, -1)) {
    DVLOG(VLOG_LEVEL) << "Applying notContains transformation: '" << *eq_term << "'";
    callback = [eq_term](Term_ptr& term) mutable {
      term = new NotContains(eq_term->left_term, eq_term->right_term);
      eq_term->left_term = nullptr;
      eq_term->right_term = nullptr;
      delete eq_term;
    };
  }
}

void SyntacticOptimizer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_and_callback(not_eq_term->left_term);
  visit_and_callback(not_eq_term->right_term);

  if (Ast2Dot::isEquivalent(not_eq_term->left_term, not_eq_term->right_term)) {
    add_callback_to_replace_with_bool(not_eq_term, "false");
  } else if (check_and_process_len_transformation(not_eq_term, not_eq_term->left_term, not_eq_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *not_eq_term << "'";
    if (Ast2Dot::isEquivalent(not_eq_term->left_term, not_eq_term->right_term)) {
      add_callback_to_replace_with_bool(not_eq_term, "false");
    }
  }
}

void SyntacticOptimizer::visitGt(Gt_ptr gt_term) {
  visit_and_callback(gt_term->left_term);
  visit_and_callback(gt_term->right_term);

  if (Ast2Dot::isEquivalent(gt_term->left_term, gt_term->right_term)) {
    add_callback_to_replace_with_bool(gt_term, "false");
  } else if (check_and_process_len_transformation(gt_term, gt_term->left_term, gt_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *gt_term << "'";
    if (Ast2Dot::isEquivalent(gt_term->left_term, gt_term->right_term)) {
      add_callback_to_replace_with_bool(gt_term, "false");
    } else {
      callback = [gt_term](Term_ptr& term) mutable {
        term = new Eq(gt_term->left_term, gt_term->right_term);
        gt_term->left_term = nullptr;
        gt_term->right_term = nullptr;
        delete gt_term;
      };
    }
  }
}

void SyntacticOptimizer::visitGe(Ge_ptr ge_term) {
  visit_and_callback(ge_term->left_term);
  visit_and_callback(ge_term->right_term);

  if (Ast2Dot::isEquivalent(ge_term->left_term, ge_term->right_term)) {
    add_callback_to_replace_with_bool(ge_term, "true");
  } else if (check_and_process_len_transformation(ge_term, ge_term->left_term, ge_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *ge_term << "'";
    if (Ast2Dot::isEquivalent(ge_term->left_term, ge_term->right_term)) {
      add_callback_to_replace_with_bool(ge_term, "true");
    } else {
      callback = [ge_term](Term_ptr& term) mutable {
        term = new Eq(ge_term->left_term, ge_term->right_term);
        ge_term->left_term = nullptr;
        ge_term->right_term = nullptr;
        delete ge_term;
      };
    }
  }
}

void SyntacticOptimizer::visitLt(Lt_ptr lt_term) {
  visit_and_callback(lt_term->left_term);
  visit_and_callback(lt_term->right_term);

  if (Ast2Dot::isEquivalent(lt_term->left_term, lt_term->right_term)) {
    add_callback_to_replace_with_bool(lt_term, "false");
  } else if (check_and_process_len_transformation(lt_term, lt_term->left_term, lt_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *lt_term << "'";
    if (Ast2Dot::isEquivalent(lt_term->left_term, lt_term->right_term)) {
      add_callback_to_replace_with_bool(lt_term, "false");
    } else {
      callback = [lt_term](Term_ptr& term) mutable {
        term = new Eq(lt_term->left_term, lt_term->right_term);
        lt_term->left_term = nullptr;
        lt_term->right_term = nullptr;
        delete lt_term;
      };
    }
  } else if (check_and_process_for_notContains_transformation(lt_term->left_term, lt_term->right_term, 0) or
          check_and_process_for_notContains_transformation(lt_term->right_term, lt_term->left_term, 0)) {
    DVLOG(VLOG_LEVEL) << "Applying notContains transformation: '" << *lt_term << "'";
    callback = [lt_term](Term_ptr& term) mutable {
      term = new NotContains(lt_term->left_term, lt_term->right_term);
      lt_term->left_term = nullptr;
      lt_term->right_term = nullptr;
      delete lt_term;
    };
  }
}

void SyntacticOptimizer::visitLe(Le_ptr le_term) {
  visit_and_callback(le_term->left_term);
  visit_and_callback(le_term->right_term);

  if (Ast2Dot::isEquivalent(le_term->left_term, le_term->right_term)) {
    add_callback_to_replace_with_bool(le_term, "true");
  } else if (check_and_process_len_transformation(le_term, le_term->left_term, le_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *le_term << "'";
    if (Ast2Dot::isEquivalent(le_term->left_term, le_term->right_term)) {
      add_callback_to_replace_with_bool(le_term, "true");
    } else {
      callback = [le_term](Term_ptr& term) mutable {
        term = new Eq(le_term->left_term, le_term->right_term);
        le_term->left_term = nullptr;
        le_term->right_term = nullptr;
        delete le_term;
      };
    }
  } else if (check_and_process_for_notContains_transformation(le_term->left_term, le_term->right_term, -1) or
          check_and_process_for_notContains_transformation(le_term->right_term, le_term->left_term, -1)) {
    DVLOG(VLOG_LEVEL) << "Applying notContains transformation: '" << *le_term << "'";
    callback = [le_term](Term_ptr& term) mutable {
      term = new NotContains(le_term->left_term, le_term->right_term);
      le_term->left_term = nullptr;
      le_term->right_term = nullptr;
      delete le_term;
    };
  }
}

void SyntacticOptimizer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : *(concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "Optimize operation: '" << *concat_term << "'";
  TermConstant_ptr initial_term_constant = nullptr;
  int pos = 0;
  for (auto iter = concat_term->term_list->begin(); iter != concat_term->term_list->end();) {
    if (Term::Type::CONCAT == (*iter)->getType()) {
      Concat_ptr sub_concat_term = dynamic_cast<Concat_ptr>(*iter);
      concat_term->term_list->erase(iter);
      concat_term->term_list->insert(iter, sub_concat_term->term_list->begin(), sub_concat_term->term_list->end());
      sub_concat_term->term_list->clear();
      delete sub_concat_term;
      iter = concat_term->term_list->begin() + pos; // insertion invalidates iter, reset it
      continue;
    } else if(Term::Type::TERMCONSTANT == (*iter)->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      if (initial_term_constant == nullptr) {
        initial_term_constant = term_constant;
      } else {
        append_constant(initial_term_constant, term_constant);
        delete term_constant; // deallocate
        concat_term->term_list->erase(iter);
        continue;
      }
    } else {
      initial_term_constant = nullptr;
    }
    iter++; pos++;
  }

  if (concat_term->term_list->size() == 1) {
    callback = [concat_term] (Term_ptr& term) mutable {
      term = concat_term->term_list->front();
      concat_term->term_list->clear();
      delete concat_term;
    };
  }
}

void SyntacticOptimizer::visitIn(In_ptr in_term) {
  visit_and_callback(in_term->left_term);
  visit_and_callback(in_term->right_term);

  if (Ast2Dot::isEquivalent(in_term->left_term, in_term->right_term)) {
    callback = [in_term](Term_ptr& term) mutable {
      term = in_term->left_term;
      in_term->left_term = nullptr;
      delete in_term;
    };
  }
}

void SyntacticOptimizer::visitNotIn(NotIn_ptr not_in_term) {
  visit_and_callback(not_in_term->left_term);
  visit_and_callback(not_in_term->right_term);

  if (Ast2Dot::isEquivalent(not_in_term->left_term, not_in_term->right_term)) {
    callback = [this, not_in_term](Term_ptr& term) mutable {
      term = generate_term_constant("/#/", Primitive::Type::REGEX);
      delete not_in_term;
    };
  }
}

void SyntacticOptimizer::visitLen(Len_ptr len_term) {
  visit_and_callback(len_term->term);
}

void SyntacticOptimizer::visitContains(Contains_ptr contains_term) {
  visit_and_callback(contains_term->subject_term);
  visit_and_callback(contains_term->search_term);

  if (Ast2Dot::isEquivalent(contains_term->subject_term, contains_term->search_term)) {
    callback = [contains_term](Term_ptr& term) mutable {
      term = contains_term->subject_term;
      contains_term->subject_term = nullptr;
      delete contains_term;
    };
  }
}

void SyntacticOptimizer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_and_callback(not_contains_term->subject_term);
  visit_and_callback(not_contains_term->search_term);

  if (Ast2Dot::isEquivalent(not_contains_term->subject_term, not_contains_term->search_term)) {
    callback = [this, not_contains_term](Term_ptr& term) mutable {
      term = generate_term_constant("/#/", Primitive::Type::REGEX);
      delete not_contains_term;
    };
  }
}

void SyntacticOptimizer::visitBegins(Begins_ptr begins_term) {
  visit_and_callback(begins_term->subject_term);
  visit_and_callback(begins_term->search_term);

  if (Ast2Dot::isEquivalent(begins_term->subject_term, begins_term->search_term)) {
    callback = [begins_term](Term_ptr& term) mutable {
      term = begins_term->subject_term;
      begins_term->subject_term = nullptr;
      delete begins_term;
    };
  }
}

void SyntacticOptimizer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_and_callback(not_begins_term->subject_term);
  visit_and_callback(not_begins_term->search_term);

  if (Ast2Dot::isEquivalent(not_begins_term->subject_term, not_begins_term->search_term)) {
    callback = [this, not_begins_term](Term_ptr& term) mutable {
      term = generate_term_constant("/#/", Primitive::Type::REGEX);
      delete not_begins_term;
    };
  }
}

void SyntacticOptimizer::visitEnds(Ends_ptr ends_term) {
  visit_and_callback(ends_term->subject_term);
  visit_and_callback(ends_term->search_term);

  if (Ast2Dot::isEquivalent(ends_term->subject_term, ends_term->search_term)) {
    callback = [ends_term](Term_ptr& term) mutable {
      term = ends_term->subject_term;
      ends_term->subject_term = nullptr;
      delete ends_term;
    };
  }
}

void SyntacticOptimizer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_and_callback(not_ends_term->subject_term);
  visit_and_callback(not_ends_term->search_term);

  if (Ast2Dot::isEquivalent(not_ends_term->subject_term, not_ends_term->search_term)) {
    callback = [this, not_ends_term](Term_ptr& term) mutable {
      term = generate_term_constant("/#/", Primitive::Type::REGEX);
      delete not_ends_term;
    };
  }
}

void SyntacticOptimizer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_and_callback(index_of_term->subject_term);
  visit_and_callback(index_of_term->search_term);
}

void SyntacticOptimizer::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visit_and_callback(last_index_of_term->subject_term);
  visit_and_callback(last_index_of_term->search_term);
}

void SyntacticOptimizer::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visit_and_callback(char_at_term->subject_term);
  visit_and_callback(char_at_term->index_term);
}

void SyntacticOptimizer::visitSubString(SMT::SubString_ptr sub_string_term) {
  visit_and_callback(sub_string_term->subject_term);
  visit_and_callback(sub_string_term->start_index_term);
  if (sub_string_term->end_index_term) {
    visit_and_callback(sub_string_term->end_index_term);
  }

  Term::Type result = check_and_process_subString(sub_string_term->subject_term, sub_string_term->start_index_term);
  if (Term::Type::INDEXOF == result or Term::Type::LASTINDEXOF == result) {
    callback = [result, sub_string_term](Term_ptr& term) mutable {
      switch (result) {
        case Term::Type::INDEXOF:
          term = new SubStringFirstOf(sub_string_term->subject_term, sub_string_term->start_index_term);
          break;
        case Term::Type::LASTINDEXOF:
          term = new SubStringLastOf(sub_string_term->subject_term, sub_string_term->start_index_term);
          break;
        default:
          break;
      }
      sub_string_term->subject_term = nullptr;
      sub_string_term->start_index_term = nullptr;
      delete sub_string_term; sub_string_term = nullptr;
    };
  }

  if (sub_string_term->end_index_term) {
    LOG(WARNING)<< "optimization check skipped, please contact us";
    LOG(FATAL)<< "handle substring optimization case";
  }
}

void SyntacticOptimizer::visitSubStringFirstOf(SMT::SubStringFirstOf_ptr sub_string_first_of_term) {
  visit_and_callback(sub_string_first_of_term->subject_term);
  visit_and_callback(sub_string_first_of_term->start_index_term);
}

void SyntacticOptimizer::visitSubStringLastOf(SMT::SubStringLastOf_ptr sub_string_last_of_term) {
  visit_and_callback(sub_string_last_of_term->subject_term);
  visit_and_callback(sub_string_last_of_term->start_index_term);
}

void SyntacticOptimizer::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visit_and_callback(to_upper_term->subject_term);
}

void SyntacticOptimizer::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visit_and_callback(to_lower_term->subject_term);
}

void SyntacticOptimizer::visitTrim(SMT::Trim_ptr trim_term) {
  visit_and_callback(trim_term->subject_term);
}

void SyntacticOptimizer::visitReplace(Replace_ptr replace_term) {
  visit_and_callback(replace_term->subject_term);
  visit_and_callback(replace_term->search_term);
  visit_and_callback(replace_term->replace_term);

  if (Ast2Dot::isEquivalent(replace_term->search_term, replace_term->replace_term)) {
    callback = [replace_term](Term_ptr& term) mutable {
      term = replace_term->subject_term;
      replace_term->subject_term = nullptr;
      delete replace_term;
    };
  }
}

void SyntacticOptimizer::visitCount(Count_ptr count_term) {
  visit_and_callback(count_term->subject_term);
  visit_and_callback(count_term->bound_term);
}

void SyntacticOptimizer::visitIte(Ite_ptr ite_term) {
  callback = [ite_term] (Term_ptr& term) mutable {
    DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *ite_term << "' into 'or'";
    And_ptr then_branch = dynamic_cast<And_ptr>(ite_term->then_branch);
    And_ptr else_branch = dynamic_cast<And_ptr>(ite_term->else_branch);
    then_branch->term_list->insert(then_branch->term_list->begin(), ite_term->cond->clone());
    if (Not_ptr not_term = dynamic_cast<Not_ptr>(ite_term->cond)) {
      else_branch->term_list->insert(else_branch->term_list->begin(), not_term->term->clone());
    } else {
      not_term = new Not(ite_term->cond);
      else_branch->term_list->insert(else_branch->term_list->begin(), not_term->clone());
    }

    TermList_ptr term_list = new TermList();
    term_list->push_back(then_branch);
    term_list->push_back(else_branch);
    term = new Or(term_list);
    ite_term->then_branch = nullptr;
    ite_term->else_branch = nullptr;
    delete ite_term;
  };
}

void SyntacticOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
  for (auto& term_ptr : *(re_concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *re_concat_term << "' into 'concat'";
  TermConstant_ptr initial_term_constant = nullptr;
  int pos = 0;
  for (auto iter = re_concat_term->term_list->begin(); iter != re_concat_term->term_list->end();) {
    if (Term::Type::CONCAT == (*iter)->getType()) {
      Concat_ptr sub_concat_term = dynamic_cast<Concat_ptr>(*iter);
      re_concat_term->term_list->erase(iter);
      re_concat_term->term_list->insert(iter, sub_concat_term->term_list->begin(), sub_concat_term->term_list->end());
      sub_concat_term->term_list->clear();
      delete sub_concat_term;
      iter = re_concat_term->term_list->begin() + pos; // insertion invalidates iter, reset it
      continue;
    } else if (Term::Type::TERMCONSTANT == (*iter)->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      if (initial_term_constant == nullptr) {
        initial_term_constant = term_constant;
      } else {
        append_constant(initial_term_constant, term_constant);
        delete term_constant; // deallocate
        re_concat_term->term_list->erase(iter);
        continue;
      }
    } else {
      initial_term_constant = nullptr;
    }
    iter++; pos++;
  }

  callback = [re_concat_term] (Term_ptr& term) mutable {
    if (re_concat_term->term_list->size() == 1) {
      term = re_concat_term->term_list->front();
      re_concat_term->term_list->clear();
    } else {
      term = new Concat(re_concat_term->term_list);
      re_concat_term->term_list = nullptr;
    }
    delete re_concat_term;
  };
}

void SyntacticOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
  if (Term::Type::TERMCONSTANT == to_regex_term->term->getType()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_regex_term->term);
    if (Primitive::Type::STRING == term_constant->getValueType()) {
      DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *to_regex_term << "'";
      std::string regex_template = "%s";
      std::string escaped_regex = escape_regex(term_constant->getValue());
      regex_template.replace(regex_template.find_first_of("%s"), 2, escaped_regex);
      Primitive_ptr regex_primitive = new Primitive(regex_template, Primitive::Type::REGEX);
      delete term_constant->primitive;
      term_constant->primitive = regex_primitive;

      callback = [to_regex_term] (Term_ptr& term) mutable {
        term = to_regex_term->term;
        to_regex_term->term = nullptr;
        delete to_regex_term;
      };
    }
  }
}

void SyntacticOptimizer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void SyntacticOptimizer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void SyntacticOptimizer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void SyntacticOptimizer::visitTermConstant(TermConstant_ptr term_constant) {
}

void SyntacticOptimizer::visitIdentifier(Identifier_ptr identifier) {
}

void SyntacticOptimizer::visitPrimitive(Primitive_ptr primitive) {
}

void SyntacticOptimizer::visitTVariable(TVariable_ptr t_variable) {
}

void SyntacticOptimizer::visitTBool(TBool_ptr t_bool) {
}

void SyntacticOptimizer::visitTInt(TInt_ptr t_int) {
}

void SyntacticOptimizer::visitTString(TString_ptr t_string) {
}

void SyntacticOptimizer::visitVariable(Variable_ptr variable) {
}

void SyntacticOptimizer::visitSort(Sort_ptr sort) {
}

void SyntacticOptimizer::visitAttribute(Attribute_ptr attribute) {
}

void SyntacticOptimizer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void SyntacticOptimizer::visitVarBinding(VarBinding_ptr var_binding) {
}

void SyntacticOptimizer::visit_and_callback(Term_ptr& term) {
  visit(term);
  if (callback) {
    callback(term);
    callback = nullptr;
  }
}

std::string SyntacticOptimizer::escape_regex(std::string regex) {
  std::stringstream ss;
  for (auto ch : regex) {
    std::string escaper = "";
    // put escaping rules here, nothing for now.
    ss << escaper << ch;
  }
  return ss.str();
}

std::string SyntacticOptimizer::regex_to_str(std::string regex) {
  std::string::size_type last = regex.substr(1).find_last_of("/");
  return regex.substr(1, last);
}

void SyntacticOptimizer::append_constant(TermConstant_ptr left_constant, TermConstant_ptr right_constant) {
  std::stringstream ss;
  if (Primitive::Type::REGEX == left_constant->getValueType()
          and Primitive::Type::REGEX == right_constant->getValueType()) {
    std::string left_data = regex_to_str(left_constant->getValue());
    std::string right_data = regex_to_str(right_constant->getValue());
    ss << "/" << left_data << right_data << "/";
    left_constant->primitive->setType(Primitive::Type::REGEX);
    left_constant->primitive->setData(ss.str());
  } else if (Primitive::Type::STRING == left_constant->getValueType()
          and Primitive::Type::STRING == right_constant->getValueType()) {
    std::string left_data = left_constant->getValue();
    std::string right_data = right_constant->getValue();
    ss << left_data << right_data ;
    left_constant->primitive->setType(Primitive::Type::STRING);
    left_constant->primitive->setData(ss.str());

  } else if (Primitive::Type::REGEX == left_constant->getValueType()
          or Primitive::Type::REGEX == right_constant->getValueType()) {
    std::string left_data =
            (Primitive::Type::REGEX == left_constant->getValueType()) ?
                    regex_to_str(left_constant->getValue()) : left_constant->getValue();
    std::string right_data =
            (Primitive::Type::REGEX == right_constant->getValueType()) ?
                    regex_to_str(right_constant->getValue()) : right_constant->getValue();
    ss << "/" << left_data << right_data << "/";
    left_constant->primitive->setType(Primitive::Type::REGEX);
    left_constant->primitive->setData(ss.str());
  }

}

bool SyntacticOptimizer::check_and_process_len_transformation(Term_ptr operation, Term_ptr& left_term,
        Term_ptr& right_term) {
  return __check_and_process_len_transformation(operation->getType(), left_term, right_term)
          || __check_and_process_len_transformation(syntactic_reverse_relation(operation->getType()), right_term, left_term);
}

bool SyntacticOptimizer::__check_and_process_len_transformation(Term::Type operation, Term_ptr& left_term,
        Term_ptr& right_term) {
  if (Term::Type::LEN == left_term->getType()) {
    Len_ptr len_ptr = dynamic_cast<Len_ptr>(left_term);
    if (Term::Type::TERMCONSTANT == right_term->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(right_term);
      if (term_constant->getValueType() == Primitive::Type::NUMERAL) {
        int value = std::stoi(term_constant->getValue());
        std::string regex_template = ".{%s,%s}";
        std::string l_value = "";
        std::string r_value = "";
        switch (operation) {
        case Term::Type::EQ: {
          l_value = std::to_string(value);
          r_value = std::to_string(value);
          break;
        }
        case Term::Type::NOTEQ: {
          l_value = std::to_string(value);
          r_value = std::to_string(value);
          break;
        }
        case Term::Type::LT: {
          l_value = "0";
          r_value = std::to_string(value - 1);
          break;
        }
        case Term::Type::LE: {
          l_value = "0";
          r_value = std::to_string(value);
          break;
        }
        case Term::Type::GT: {
          l_value = std::to_string(value + 1);
          break;
        }
        case Term::Type::GE: {
          l_value = std::to_string(value);
          break;
        }
        default:
          return false;
        }
        regex_template.replace(regex_template.find_first_of("%s"), 2, l_value); // replace l
        regex_template.replace(regex_template.find_first_of("%s"), 2, r_value); // replace r
        term_constant->primitive->setData(regex_template);
        term_constant->primitive->setType(Primitive::Type::REGEX);
        left_term = len_ptr->term;
        len_ptr->term = nullptr;
        delete len_ptr;
        return true;
      }
    }
  }
  return false;
}

SMT::Term::Type SyntacticOptimizer::syntactic_reverse_relation(SMT::Term::Type operation) {
  switch (operation) {
    case Term::Type::LT:
      return Term::Type::GT;
    case Term::Type::LE:
      return Term::Type::GE;
    case Term::Type::GT:
      return Term::Type::LT;
    case Term::Type::GE:
      return Term::Type::LE;
    default:
      return operation;
  }
}

/**
 * Checks if we can convert indexOf and lastIndexOf operations to contains operation
 * when they are used to check if a string does not contain other one
 */
bool SyntacticOptimizer::check_and_process_for_notContains_transformation(SMT::Term_ptr& left_term, SMT::Term_ptr& right_term, int compare_value) {
  TermConstant_ptr expected_constant_term = nullptr;
  if (compare_value < 0 and Term::Type::UMINUS == right_term->getType()) {
    UMinus_ptr u_minus_term = dynamic_cast<UMinus_ptr>(right_term);
    if (Term::Type::TERMCONSTANT == u_minus_term->term->getType()) {
      expected_constant_term = dynamic_cast<TermConstant_ptr>(u_minus_term->term);
      compare_value = -compare_value;
    }
  } else if (Term::Type::TERMCONSTANT == right_term->getType()) {
    expected_constant_term = dynamic_cast<TermConstant_ptr>(right_term);
  }

  if (expected_constant_term == nullptr or
          Primitive::Type::NUMERAL != expected_constant_term->getValueType()) {
    return false;
  } else if (compare_value != std::stoi(expected_constant_term->getValue())) {
    return false;
  }

  if (IndexOf_ptr index_of_term = dynamic_cast<IndexOf_ptr>(left_term)) {
    Term_ptr tmp_term = right_term;
    right_term = index_of_term->search_term;
    left_term = index_of_term->subject_term;
    index_of_term->subject_term = nullptr;
    index_of_term->search_term = nullptr;
    delete index_of_term;
    delete tmp_term;
    return true;
  } else if (LastIndexOf_ptr last_index_of_term = dynamic_cast<LastIndexOf_ptr>(left_term)) {
    Term_ptr tmp_term = right_term;
    right_term = last_index_of_term->search_term;
    left_term = last_index_of_term->subject_term;
    last_index_of_term->subject_term = nullptr;
    last_index_of_term->search_term = nullptr;
    delete last_index_of_term;
    delete tmp_term;
    return true;
  }

  return false;
}

Term::Type SyntacticOptimizer::check_and_process_subString(Term_ptr subject_term, Term_ptr &index_term) {
  switch (index_term->getType()) {
    case Term::Type::INDEXOF: {
      IndexOf_ptr index_of_term = dynamic_cast<IndexOf_ptr>(index_term);
      if (Ast2Dot::isEquivalent(subject_term, index_of_term->subject_term)) {
        index_term = index_of_term->search_term;
        index_of_term->search_term = nullptr;
        delete index_of_term;
        return Term::Type::INDEXOF;
      }
      break;
    }
    case Term::Type::LASTINDEXOF: {
      LastIndexOf_ptr last_index_of_term = dynamic_cast<LastIndexOf_ptr>(index_term);
      if (Ast2Dot::isEquivalent(subject_term, last_index_of_term->subject_term)) {
        index_term = last_index_of_term->search_term;
        last_index_of_term->search_term = nullptr;
        delete last_index_of_term;
        return Term::Type::LASTINDEXOF;
      }
      break;
    }
    default:
      break;
  }
  return Term::Type::NONE;
}

Term_ptr SyntacticOptimizer::generate_term_constant(std::string data, Primitive::Type type) {
  return new TermConstant(new Primitive(data, type));
}

Term_ptr SyntacticOptimizer::generate_dummy_term() {
  std::string var_name;

  for (auto& variable_pair : symbol_table->getVariables()) {
    var_name = variable_pair.first;
    if (variable_pair.second->isSymbolic())
      break;
  }

  if (var_name.empty()) {
    return generate_term_constant("true", Primitive::Type::BOOL);
  } else {
    Primitive_ptr primitive = new Primitive(var_name, Primitive::Type::SYMBOL);
    Identifier_ptr identifier = new Identifier(primitive);
    QualIdentifier_ptr var_ptr = new QualIdentifier(identifier);
    return var_ptr;
  }
}

void SyntacticOptimizer::add_callback_to_replace_with_bool(Term_ptr term, std::string value) {
  DVLOG(VLOG_LEVEL) << "Replacing with '" << value << "': '" << *term << "'";
  callback = [this, term, value](Term_ptr& ref_term) mutable {
    ref_term = generate_term_constant(value, Primitive::Type::BOOL);
    delete term;
  };
}

bool SyntacticOptimizer::check_bool_constant_value(Term_ptr term, std::string value) {
  if (Term::Type::TERMCONSTANT == term->getType()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term);
    if (Primitive::Type::BOOL == term_constant->getValueType() and value == term_constant->getValue()) {
      return true;
    }
  }

  return false;
}

} /* namespace Solver */
} /* namespace Vlab */

