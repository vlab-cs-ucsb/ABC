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

SyntacticProcessor::SyntacticProcessor(Script_ptr script) : root (script) {
}

SyntacticProcessor::~SyntacticProcessor() {
}

void SyntacticProcessor::start() {
  convertAssertsToAnd();
  preProcessNegations();
}

void SyntacticProcessor::end() {
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

void SyntacticProcessor::fixOperationSyntax() {
  AstTraverser postorder_traverser(root);
  auto term_post_callback = [this, &postorder_traverser] (Term_ptr term) mutable -> bool {
    switch (term->getType()) {
    case Term::Type::ITE: {
      Ite_ptr ite_term = dynamic_cast<Ite_ptr>(term);
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
      Term_ptr* reference_term = postorder_traverser.top();
      *reference_term = new Or(term_list);
      ite_term->then_branch = nullptr;
      ite_term->else_branch = nullptr;
      delete ite_term;
      break;
    }
    case Term::Type::RECONCAT: {
      ReConcat_ptr re_concat_term = dynamic_cast<ReConcat_ptr>(term);
      DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *re_concat_term << "' into 'concat'";
      TermConstant_ptr initial_term_constant = nullptr;
      for (auto iter = re_concat_term->term_list->begin(); iter != re_concat_term->term_list->end();) {
        if (Term::Type::TERMCONSTANT == (*iter)->getType()) {
          TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
          if (initial_term_constant == nullptr) {
            initial_term_constant = term_constant;
          } else {
            concat_to_left(initial_term_constant, term_constant);
            delete term_constant; // deallocate
            re_concat_term->term_list->erase(iter);
            continue;
          }
        } else {
          initial_term_constant = nullptr;
        }
        iter++;
      }

      Term_ptr* reference_term = postorder_traverser.top();
      if (re_concat_term->term_list->size() == 1) {
        *reference_term = re_concat_term->term_list->front();
        re_concat_term->term_list->clear();
      } else {
        *reference_term = new Concat(re_concat_term->term_list);
        re_concat_term->term_list = nullptr;
      }
      delete re_concat_term;
      break;
    }
    case Term::Type::TOREGEX: {
      ToRegex_ptr to_regex_term = dynamic_cast<ToRegex_ptr>(term);
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

          Term_ptr* reference_term = postorder_traverser.top();
          *reference_term = to_regex_term->term;
          to_regex_term->term = nullptr;
          delete to_regex_term;
        }
      }
      break;
    }
    default:
      break;
    }

    return true;
  };

  postorder_traverser.setTermPostCallback(term_post_callback);
  postorder_traverser.start();
}

/**
 * Applies De Morgan's Law and push negations down
 * Handles negations syntacticly if possible
 */
void SyntacticProcessor::preProcessNegations() {
  AstTraverser preorder_traverser(root);
  auto term_pre_callback = [&preorder_traverser] (Term_ptr term) -> bool {
    if (Term::Type::NOT == term->getType()) {
      Not_ptr not_term = dynamic_cast<Not_ptr>(term);
      DVLOG(VLOG_LEVEL) << "preProcessNegations '(not (" << *not_term->term << " ... ))'";
      switch (not_term->term->getType()) {
      case Term::Type::AND: {
        Term_ptr* reference_term = preorder_traverser.top();
        And_ptr and_term = dynamic_cast<And_ptr>(not_term->term);

        for (auto& sub_term : *and_term->term_list) {
          Not_ptr sub_not_term = new Not(sub_term);
          sub_term = sub_not_term;
        }

        Or_ptr or_term = new Or(and_term->term_list);
        and_term->term_list = nullptr;
        delete not_term;

        *reference_term = or_term;
        preorder_traverser.visitOr(or_term);
        return false;
      }
      case Term::Type::OR: {
        Term_ptr* reference_term = preorder_traverser.top();
        Or_ptr or_term = dynamic_cast<Or_ptr>(not_term->term);

        for (auto& sub_term : *or_term->term_list) {
          Not_ptr sub_not_term = new Not(sub_term);
          sub_term = sub_not_term;
        }

        And_ptr and_term = new And(or_term->term_list);
        or_term->term_list = nullptr;
        delete not_term;

        *reference_term = and_term;
        preorder_traverser.visitAnd(and_term);
        return false;
      }
      case Term::Type::NOT: {
        Term_ptr* reference_term = preorder_traverser.top();
        Not_ptr sub_not_term = dynamic_cast<Not_ptr>(not_term->term);

        *reference_term = sub_not_term->term;
        sub_not_term->term = nullptr;
        delete not_term;
        preorder_traverser.Visitor::visit(*reference_term);
        return false;
      }
      case Term::Type::EQ: {
        Term_ptr* reference_term = preorder_traverser.top();
        Eq_ptr eq_term = dynamic_cast<Eq_ptr>(not_term->term);
        NotEq_ptr not_eq_term = new NotEq(eq_term->left_term, eq_term->right_term);
        eq_term->left_term = nullptr; eq_term->right_term = nullptr;

        *reference_term = not_eq_term;
        delete not_term;

        preorder_traverser.visitNotEq(not_eq_term);
        return false;
      }
      case Term::Type::NOTEQ: {
        Term_ptr* reference_term = preorder_traverser.top();
        NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>(not_term->term);
        Eq_ptr eq_term = new Eq(not_eq_term->left_term, not_eq_term->right_term);
        not_eq_term->left_term = nullptr; not_eq_term->right_term = nullptr;

        *reference_term = eq_term;
        delete not_term;

        preorder_traverser.visitEq(eq_term);
        return false;
      }
      case Term::Type::GT: {
        Term_ptr* reference_term = preorder_traverser.top();
        Gt_ptr gt_term = dynamic_cast<Gt_ptr>(not_term->term);
        Le_ptr le_term = new Le(gt_term->left_term, gt_term->right_term);
        gt_term->left_term = nullptr; gt_term->right_term = nullptr;

        *reference_term = le_term;
        delete not_term;

        preorder_traverser.visitLe(le_term);
        return false;
      }
      case Term::Type::GE: {
        Term_ptr* reference_term = preorder_traverser.top();
        Ge_ptr ge_term = dynamic_cast<Ge_ptr>(not_term->term);
        Lt_ptr lt_term = new Lt(ge_term->left_term, ge_term->right_term);
        ge_term->left_term = nullptr; ge_term->right_term = nullptr;

        *reference_term = lt_term;
        delete not_term;

        preorder_traverser.visitLt(lt_term);
        return false;
      }
      case Term::Type::LT: {
        Term_ptr* reference_term = preorder_traverser.top();
        Lt_ptr lt_term = dynamic_cast<Lt_ptr>(not_term->term);
        Ge_ptr ge_term = new Ge(lt_term->left_term, lt_term->right_term);
        lt_term->left_term = nullptr; lt_term->right_term = nullptr;

        *reference_term = ge_term;
        delete not_term;

        preorder_traverser.visitGe(ge_term);
        return false;
      }
      case Term::Type::LE: {
        Term_ptr* reference_term = preorder_traverser.top();
        Le_ptr le_term = dynamic_cast<Le_ptr>(not_term->term);
        Gt_ptr gt_term = new Gt(le_term->left_term, le_term->right_term);
        le_term->left_term = nullptr; le_term->right_term = nullptr;

        *reference_term = gt_term;
        delete not_term;

        preorder_traverser.visitGt(gt_term);
        return false;
      }
      case Term::Type::IN: {
        Term_ptr* reference_term = preorder_traverser.top();
        In_ptr in_term = dynamic_cast<In_ptr>(not_term->term);
        NotIn_ptr not_in_term = new NotIn(in_term->left_term, in_term->right_term);
        in_term->left_term = nullptr; in_term->right_term = nullptr;

        *reference_term = not_in_term;
        delete not_term;

        preorder_traverser.visitNotIn(not_in_term);
        return false;
      }
      case Term::Type::NOTIN: {
        Term_ptr* reference_term = preorder_traverser.top();
        NotIn_ptr not_in_term = dynamic_cast<NotIn_ptr>(not_term->term);
        In_ptr in_term = new In(not_in_term->left_term, not_in_term->right_term);
        not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;

        *reference_term = in_term;
        delete not_term;

        preorder_traverser.visitIn(in_term);
        return false;
      }
      case Term::Type::CONTAINS: {
        Term_ptr* reference_term = preorder_traverser.top();
        Contains_ptr contains_term = dynamic_cast<Contains_ptr>(not_term->term);
        NotContains_ptr not_contains_term = new NotContains(contains_term->subject_term, contains_term->search_term);
        contains_term->subject_term = nullptr; contains_term->search_term = nullptr;

        *reference_term = not_contains_term;
        delete not_term;

        preorder_traverser.visitNotContains(not_contains_term);
        return false;
      }
      case Term::Type::NOTCONTAINS: {
        Term_ptr* reference_term = preorder_traverser.top();
        NotContains_ptr not_contains_term = dynamic_cast<NotContains_ptr>(not_term->term);
        Contains_ptr contains_term = new Contains(not_contains_term->subject_term, not_contains_term->search_term);
        not_contains_term->subject_term = nullptr; not_contains_term->search_term = nullptr;

        *reference_term = contains_term;
        delete not_term;

        preorder_traverser.visitContains(contains_term);
        return false;
      }
      case Term::Type::BEGINS: {
        Term_ptr* reference_term = preorder_traverser.top();
        Begins_ptr begins_term = dynamic_cast<Begins_ptr>(not_term->term);
        NotBegins_ptr not_begins_term = new NotBegins(begins_term->subject_term, begins_term->search_term);
        begins_term->subject_term = nullptr; begins_term->search_term = nullptr;

        *reference_term = not_begins_term;
        delete not_term;

        preorder_traverser.visitNotBegins(not_begins_term);
        return false;
      }
      case Term::Type::NOTBEGINS: {
        Term_ptr* reference_term = preorder_traverser.top();
        NotBegins_ptr not_begins_term = dynamic_cast<NotBegins_ptr>(not_term->term);
        Begins_ptr begins_term = new Begins(not_begins_term->subject_term, not_begins_term->search_term);
        not_begins_term->subject_term = nullptr; not_begins_term->search_term = nullptr;

        *reference_term = begins_term;
        delete not_term;

        preorder_traverser.visitBegins(begins_term);
        return false;
      }
      case Term::Type::ENDS: {
        Term_ptr* reference_term = preorder_traverser.top();
        Ends_ptr ends_term = dynamic_cast<Ends_ptr>(not_term->term);
        NotEnds_ptr not_ends_term = new NotEnds(ends_term->subject_term, ends_term->search_term);
        ends_term->subject_term = nullptr; ends_term->search_term = nullptr;

        *reference_term = not_ends_term;
        delete not_term;

        preorder_traverser.visitNotEnds(not_ends_term);
        return false;
      }
      case Term::Type::NOTENDS: {
        Term_ptr* reference_term = preorder_traverser.top();
        NotEnds_ptr not_ends_term = dynamic_cast<NotEnds_ptr>(not_term->term);
        Ends_ptr ends_term = new Ends(not_ends_term->subject_term, not_ends_term->search_term);
        not_ends_term->subject_term = nullptr; not_ends_term->search_term = nullptr;

        *reference_term = ends_term;
        delete not_term;

        preorder_traverser.visitEnds(ends_term);
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

  preorder_traverser.setCommandPreCallback(command_callback);
  preorder_traverser.setTermPreCallback(term_pre_callback);
  preorder_traverser.start();
}

void SyntacticProcessor::convertToDNF() {
}

std::string SyntacticProcessor::escape_regex(std::string regex) {
  std::stringstream ss;
  for (auto ch : regex) {
    std::string escaper = "";
    // put escaping rules here, nothing for now.
    ss << escaper << ch;
  }
  return ss.str();
}

std::string SyntacticProcessor::regex_to_str(std::string regex) {
  std::string::size_type last = regex.substr(1).find_last_of("/");
  return regex.substr(1, last);
}

void SyntacticProcessor::concat_to_left(TermConstant_ptr left_constant, TermConstant_ptr right_constant) {
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

} /* namespace Solver */
} /* namespace Vlab */
