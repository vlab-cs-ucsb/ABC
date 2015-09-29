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
    } else if (Term::Type::AND == current_assert->term->getType()) {
      iter = commands->erase(iter);
      And_ptr and_term = dynamic_cast<And_ptr>(current_assert->term);
      for (auto riter = and_term->term_list->rbegin(); riter != and_term->term_list->rend(); riter++) {
        iter = commands->insert(iter, new Assert(*riter));
        *riter = nullptr;
      }
      delete current_assert;
    } else {
      iter++;
    }
  }

  if (script->command_list->empty()) {
    script->command_list->push_back(new Assert(generate_dummy_term()));
  }
}

void SyntacticOptimizer::visitCommand(Command_ptr command) {

  switch (command->getType()) {
  case Command::Type::ASSERT: {
    current_assert = dynamic_cast<Assert_ptr>(command);
    visit_and_callback(current_assert->term);

//			std::string assert_string = to_string(current_assert->term);
//			if (assert_equivalance.find(assert_string) != assert_equivalance.end()) {
//				to_be_removed.insert(command);
//			} else {
//				assert_equivalance.insert(assert_string);
//			}
    break;
  }
  default:
    LOG(FATAL)<< "'" << *command<< "' is not expected.";
    break;
  }
}

void SyntacticOptimizer::visitAssert(Assert_ptr assert_command) {

  current_assert = assert_command;
  visit_and_callback(current_assert->term);

//  std::string assert_string = to_string(current_assert->term);
//  if (assert_equivalance.find(assert_string) != assert_equivalance.end()) {
//    to_be_removed.insert(assert_command);
//  } else {
//    assert_equivalance.insert(assert_string);
//  }
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
  for (auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
    visit_and_callback(*iter);
    if (check_bool_constant_value(*iter, "true")) {
      DVLOG(VLOG_LEVEL) << "remove: 'true' constant from 'and'";
      delete (*iter);
      iter = and_term->term_list->erase(iter);
    } else if (check_bool_constant_value(*iter, "false")) {
      has_false_term = true;
      break;
    } else {
      iter++;
    }
  }

  if (has_false_term) {
    DVLOG(VLOG_LEVEL) << "replace: 'and' with constant 'false'";
    auto callback = [this, and_term](Term_ptr& term) mutable {
      term = generate_term_constant("false", Primitive::Type::BOOL);
      delete and_term;
    };
  } else if (and_term->term_list->empty()) {
    add_callback_to_replace_with_bool(and_term, "true");
  } else if (and_term->term_list->size() == 1) {
    auto callback = [and_term](Term_ptr& term) mutable {
      Term_ptr child_term = and_term->term_list->front();
      and_term->term_list->clear();
      delete and_term;
      term = child_term;
    };
    callbacks.push(callback);
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
    auto callback = [or_term](Term_ptr& term) mutable {
      Term_ptr child_term = or_term->term_list->front();
      or_term->term_list->clear();
      delete or_term;
      term = child_term;
    };
    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitNot(Not_ptr not_term) {
  visit_and_callback(not_term->term);

  switch (not_term->term->getType()) {
  case Term::Type::NOT: {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (not (not a) to a";
    auto callback = [not_term](Term_ptr& term) mutable {
      Not_ptr child_not = dynamic_cast<Not_ptr>(not_term->term);
      term = child_not->term;
      child_not->term = nullptr;
      delete not_term;
    };
    callbacks.push(callback);
    break;
  }
  case Term::Type::IN: {
    In_ptr in_ptr = dynamic_cast<In_ptr>(not_term->term);
    if (check_and_process_in_transformation(in_ptr->right_term, true)) {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (not (in l r) to (in l r')";
      auto callback = [not_term](Term_ptr& term) mutable {
        term = not_term->term;
        not_term->term = nullptr;
        delete not_term;
      };

      callbacks.push(callback);
    }
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
    auto callback = [u_minus_term](Term_ptr& term) mutable {
      UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(u_minus_term->term);
      term = child_u_minus->term;
      child_u_minus->term = nullptr;
      delete u_minus_term;
    };
    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitMinus(Minus_ptr minus_term) {
  visit_and_callback(minus_term->left_term);
  visit_and_callback(minus_term->right_term);

  if (Term::Type::TERMCONSTANT == minus_term->left_term->getType()
          and Term::Type::TERMCONSTANT == minus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- lc rc) to lc-rc";
    auto callback = [this, minus_term](Term_ptr& term) mutable {
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
    callbacks.push(callback);
  } else if (Term::Type::TERMCONSTANT == minus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- l 0) to l";
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
    if (term_constant->getValue() == "0") {
      auto callback = [minus_term](Term_ptr& term) mutable {
        term = minus_term->left_term;
        minus_term->left_term = nullptr;
        delete minus_term;
      };
      callbacks.push(callback);
    }
  } else if (Term::Type::UMINUS == minus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- l (- r) to (+ l r)";
    auto callback = [minus_term](Term_ptr& term) mutable {
      UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(minus_term->right_term);
      term = new Plus(minus_term->left_term, child_u_minus->term);
      minus_term->left_term = nullptr;
      child_u_minus->term = nullptr;
      delete minus_term;
    };
    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitPlus(Plus_ptr plus_term) {
  visit_and_callback(plus_term->left_term);
  visit_and_callback(plus_term->right_term);

  if (Term::Type::TERMCONSTANT == plus_term->left_term->getType()
          and Term::Type::TERMCONSTANT == plus_term->right_term->getType()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (+ lc rc) to lc+rc";
    auto callback = [this, plus_term](Term_ptr& term) mutable {
      TermConstant_ptr left_constant = dynamic_cast<TermConstant_ptr>(plus_term->left_term);
      TermConstant_ptr right_constant = dynamic_cast<TermConstant_ptr>(plus_term->right_term);
      int left_value = std::stoi(left_constant->getValue());
      int right_value = std::stoi(right_constant->getValue());
      int result = left_value + right_value;
      term = this->generate_term_constant(std::to_string(result),Primitive::Type::NUMERAL);
      delete plus_term;
    };
    callbacks.push(callback);
  } else if (Term::Type::TERMCONSTANT == plus_term->right_term->getType()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(plus_term->right_term);
    if (term_constant->getValue() == "0") {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (+ l 0) to l";
      auto callback = [plus_term](Term_ptr& term) mutable {
        term = plus_term->left_term;
        plus_term->left_term = nullptr;
        delete plus_term;
      };
      callbacks.push(callback);
    }
  } else if (Term::Type::TERMCONSTANT == plus_term->left_term->getType()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(plus_term->left_term);
    if (term_constant->getValue() == "0") {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (+ 0 r) to r";
      auto callback = [plus_term](Term_ptr& term) mutable {
        term = plus_term->right_term;
        plus_term->right_term = nullptr;
        delete plus_term;
      };
      callbacks.push(callback);
    }
  }
}

void SyntacticOptimizer::visitEq(Eq_ptr eq_term) {
  visit_and_callback(eq_term->left_term);
  visit_and_callback(eq_term->right_term);

  if (check_and_process_len_transformation(eq_term, eq_term->left_term, eq_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *eq_term << "'";
  }

  if (is_equivalent(eq_term->left_term, eq_term->right_term)) {
    add_callback_to_replace_with_bool(eq_term, "true");
  }
}

void SyntacticOptimizer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_and_callback(not_eq_term->left_term);
  visit_and_callback(not_eq_term->right_term);

  LOG(FATAL) << "implement me";
}

void SyntacticOptimizer::visitGt(Gt_ptr gt_term) {
  visit_and_callback(gt_term->left_term);
  visit_and_callback(gt_term->right_term);

  if (check_and_process_len_transformation(gt_term, gt_term->left_term, gt_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *gt_term << "'";
    auto callback = [gt_term](Term_ptr& term) mutable {
      term = new Eq(gt_term->left_term, gt_term->right_term);
      gt_term->left_term = nullptr;
      gt_term->right_term = nullptr;
      delete gt_term;
    };
    callbacks.push(callback);
  }

  if (is_equivalent(gt_term->left_term, gt_term->right_term)) {
    add_callback_to_replace_with_bool(gt_term, "false");
  }
}

void SyntacticOptimizer::visitGe(Ge_ptr ge_term) {
  visit_and_callback(ge_term->left_term);
  visit_and_callback(ge_term->right_term);

  if (check_and_process_len_transformation(ge_term, ge_term->left_term, ge_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *ge_term << "'";
    auto callback = [ge_term](Term_ptr& term) mutable {
      term = new Eq(ge_term->left_term, ge_term->right_term);
      ge_term->left_term = nullptr;
      ge_term->right_term = nullptr;
      delete ge_term;
    };
    callbacks.push(callback);
  }

  if (is_equivalent(ge_term->left_term, ge_term->right_term)) {
    add_callback_to_replace_with_bool(ge_term, "true");
  }
}

void SyntacticOptimizer::visitLt(Lt_ptr lt_term) {
  visit_and_callback(lt_term->left_term);
  visit_and_callback(lt_term->right_term);

  if (check_and_process_len_transformation(lt_term, lt_term->left_term, lt_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *lt_term << "'";
    auto callback = [lt_term](Term_ptr& term) mutable {
      term = new Eq(lt_term->left_term, lt_term->right_term);
      lt_term->left_term = nullptr;
      lt_term->right_term = nullptr;
      delete lt_term;
    };
    callbacks.push(callback);
  }

  if (is_equivalent(lt_term->left_term, lt_term->right_term)) {
    add_callback_to_replace_with_bool(lt_term, "false");
  }
}

void SyntacticOptimizer::visitLe(Le_ptr le_term) {
  visit_and_callback(le_term->left_term);
  visit_and_callback(le_term->right_term);

  if (check_and_process_len_transformation(le_term, le_term->left_term, le_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *le_term << "'";
    auto callback = [le_term](Term_ptr& term) mutable {
      term = new Eq(le_term->left_term, le_term->right_term);
      le_term->left_term = nullptr;
      le_term->right_term = nullptr;
      delete le_term;
    };
    callbacks.push(callback);
  }

  if (is_equivalent(le_term->left_term, le_term->right_term)) {
    add_callback_to_replace_with_bool(le_term, "true");
  }
}

//TODO Optimize concat based on concat test case,
// reduce nested concats into one level
// test case test_syntactic_optimization_concat_01.smt2
void SyntacticOptimizer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : *(concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }
}

void SyntacticOptimizer::visitIn(In_ptr in_term) {
  visit_and_callback(in_term->left_term);
  visit_and_callback(in_term->right_term);

  if (is_equivalent(in_term->left_term, in_term->right_term)) {
    auto callback = [in_term](Term_ptr& term) mutable {
      term = in_term->left_term;
      in_term->left_term = nullptr;
      delete in_term;
    };

    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitNotIn(NotIn_ptr not_in_term) {
  visit_and_callback(not_in_term->left_term);
  visit_and_callback(not_in_term->right_term);

  LOG(FATAL) << "implement me";
}

void SyntacticOptimizer::visitLen(Len_ptr len_term) {
  visit_and_callback(len_term->term);
}

void SyntacticOptimizer::visitContains(Contains_ptr contains_term) {
  visit_and_callback(contains_term->subject_term);
  visit_and_callback(contains_term->search_term);

  if (is_equivalent(contains_term->subject_term, contains_term->search_term)) {
    auto callback = [contains_term](Term_ptr& term) mutable {
      term = contains_term->subject_term;
      contains_term->subject_term = nullptr;
      delete contains_term;
    };

    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_and_callback(not_contains_term->subject_term);
  visit_and_callback(not_contains_term->search_term);

  LOG(FATAL) << "implement me";
}

void SyntacticOptimizer::visitBegins(Begins_ptr begins_term) {
  visit_and_callback(begins_term->subject_term);
  visit_and_callback(begins_term->search_term);

  if (is_equivalent(begins_term->subject_term, begins_term->search_term)) {
    auto callback = [begins_term](Term_ptr& term) mutable {
      term = begins_term->subject_term;
      begins_term->subject_term = nullptr;
      delete begins_term;
    };

    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_and_callback(not_begins_term->subject_term);
  visit_and_callback(not_begins_term->search_term);
  LOG(FATAL) << "implement me";
}

void SyntacticOptimizer::visitEnds(Ends_ptr ends_term) {
  visit_and_callback(ends_term->subject_term);
  visit_and_callback(ends_term->search_term);

  if (is_equivalent(ends_term->subject_term, ends_term->search_term)) {
    auto callback = [ends_term](Term_ptr& term) mutable {
      term = ends_term->subject_term;
      ends_term->subject_term = nullptr;
      delete ends_term;
    };

    callbacks.push(callback);
  }
}

void SyntacticOptimizer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_and_callback(not_ends_term->subject_term);
  visit_and_callback(not_ends_term->search_term);

  LOG(FATAL) << "implement me";
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
}

void SyntacticOptimizer::visitCount(Count_ptr count_term) {
  visit_and_callback(count_term->subject_term);
  visit_and_callback(count_term->bound_term);
}

void SyntacticOptimizer::visitIte(Ite_ptr ite_term) {
  visit_and_callback(ite_term->cond);
  visit_and_callback(ite_term->then_branch);
  visit_and_callback(ite_term->else_branch);

  DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *ite_term << "' into 'or'";
  auto callback = [ite_term](Term_ptr& term) mutable {
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
  callbacks.push(callback);
}

void SyntacticOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
  for (auto& term_ptr : *(re_concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *re_concat_term << "' into 'concat'";
  TermConstant_ptr initial_term_constant = nullptr;
  for (auto iter = re_concat_term->term_list->begin(); iter != re_concat_term->term_list->end();) {
    if (Term::Type::TERMCONSTANT == (*iter)->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      if (initial_term_constant == nullptr) {
        initial_term_constant = term_constant;
      } else {
        pre_concat_constants(initial_term_constant, term_constant);
        delete term_constant; // deallocate
        re_concat_term->term_list->erase(iter);
        continue;
      }
    } else {
      initial_term_constant = nullptr;
    }
    iter++;
  }

  auto callback = [re_concat_term](Term_ptr& term) mutable {
    if (re_concat_term->term_list->size() == 1) {
      term = re_concat_term->term_list->front();
      re_concat_term->term_list->clear();
    } else {
      term = new Concat(re_concat_term->term_list);
      re_concat_term->term_list = nullptr;
    }
    delete re_concat_term;
  };
  callbacks.push(callback);
}

void SyntacticOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
  if (Term::Type::TERMCONSTANT == to_regex_term->term->getType()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_regex_term->term);
    if (Primitive::Type::STRING == term_constant->getValueType()) {
      DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *to_regex_term << "'";
      std::string regex_template = "/%s/";
      std::string escaped_regex = escape_regex(term_constant->getValue());
      regex_template.replace(regex_template.find_first_of("%s"), 2, escaped_regex);
      Primitive_ptr regex_primitive = new Primitive(regex_template, Primitive::Type::REGEX);
      delete term_constant->primitive;
      term_constant->primitive = regex_primitive;

      auto callback = [to_regex_term](Term_ptr& term) mutable {
        term = to_regex_term->term;
        to_regex_term->term = nullptr;
        delete to_regex_term;
      };

      callbacks.push(callback);
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
  while (not callbacks.empty()) {
    callbacks.front()(term);
    callbacks.pop();
  }
}

bool SyntacticOptimizer::is_equivalent(Term_ptr x, Term_ptr y) {
  if (x == y) {
    return true;
  }
  return (to_string(x) == to_string(y));
}

std::string SyntacticOptimizer::to_string(Visitable_ptr visitable) {
  std::stringstream ss;
  Ast2Dot ast2dot(&ss);
  ast2dot.start(visitable);
  return ss.str();
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

void SyntacticOptimizer::pre_concat_constants(TermConstant_ptr left_constant, TermConstant_ptr right_constant) {
  std::stringstream ss;
  if (Primitive::Type::REGEX == left_constant->getValueType()
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

bool SyntacticOptimizer::check_and_process_in_transformation(Term_ptr term, bool isComplement) {
  if (Term::Type::TERMCONSTANT == term->getType()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term);
    if (Primitive::Type::REGEX == term_constant->getValueType() and isComplement) {
      std::string data = regex_to_str(term_constant->getValue());
      if (data.find_first_of("~(") == 0 and data.back() == ')') {
        data.replace(0, 2, "");
        data.pop_back();
      } else {
        std::string regex_template = "/~(%s)/";
        regex_template.replace(regex_template.find_first_of("%s"), 2, data);
        data = regex_template;
      }
      term_constant->primitive->setData(data);
      return true;
    } else if (Primitive::Type::STRING == term_constant->getValueType() and isComplement) {
      std::string regex_template = "/~(%s)/";
      regex_template.replace(regex_template.find_first_of("%s"), 2, escape_regex(term_constant->getValue()));
      term_constant->primitive->setData(regex_template);
      term_constant->primitive->setType(Primitive::Type::REGEX);
      return true;
    }
  }

  return false;
}

bool SyntacticOptimizer::check_and_process_len_transformation(Term_ptr operation, Term_ptr& left_term,
        Term_ptr& right_term) {
  return __check_and_process_len_transformation(operation->str(), left_term, right_term)
          || __check_and_process_len_transformation(syntactic_reverse_relation(operation->str()), right_term, left_term);
}

bool SyntacticOptimizer::__check_and_process_len_transformation(std::string operation, Term_ptr& left_term,
        Term_ptr& right_term) {
  if (Term::Type::LEN == left_term->getType()) {
    Len_ptr len_ptr = dynamic_cast<Len_ptr>(left_term);
    if (Term::Type::TERMCONSTANT == right_term->getType()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(right_term);
      if (term_constant->getValueType() == Primitive::Type::NUMERAL) {
        int value = std::stoi(term_constant->getValue());
        std::string regex_template = "/.{%s,%s}/";
        std::string l_value = "";
        std::string r_value = "";
        if (operation == "=") {
          l_value = std::to_string(value);
          r_value = std::to_string(value);
        } else if (operation == "<") {
          l_value = "0";
          r_value = std::to_string(value - 1);
        } else if (operation == "<=") {
          l_value = "0";
          r_value = std::to_string(value);
        } else if (operation == ">") {
          l_value = std::to_string(value + 1);
        } else if (operation == ">=") {
          l_value = std::to_string(value);
        } else {
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

std::string SyntacticOptimizer::syntactic_reverse_relation(std::string operation) {
  if (operation == "<") {
    return ">";
  } else if (operation == "<=") {
    return ">=";
  } else if (operation == ">") {
    return "<";
  } else if (operation == ">=") {
    return "<=";
  } else {
    return operation;
  }
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
  auto callback = [this, term, value](Term_ptr& ref_term) mutable {
    ref_term = generate_term_constant(value, Primitive::Type::BOOL);
    delete term;
  };
  callbacks.push(callback);
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

