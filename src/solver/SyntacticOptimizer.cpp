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

unsigned SyntacticOptimizer::name_counter = 0;
const int SyntacticOptimizer::VLOG_LEVEL = 18;

SyntacticOptimizer::SyntacticOptimizer(Script_ptr script, SymbolTable_ptr symbol_table, bool transform_ite)
    : root_(script),
      symbol_table_(symbol_table),
      transform_ite_(transform_ite) {
}

SyntacticOptimizer::~SyntacticOptimizer() {
}

void SyntacticOptimizer::start() {
  symbol_table_->reset_variable_usage();
  symbol_table_->reset_variable_concat();

  DVLOG(VLOG_LEVEL) << "Start SyntacticOptimizer";
  symbol_table_->push_scope(root_,false);
  visit(root_);
  symbol_table_->pop_scope();
  end();
}

void SyntacticOptimizer::end() {
  DVLOG(VLOG_LEVEL) << "SyntacticOptimizer is finished!";

}

void SyntacticOptimizer::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void SyntacticOptimizer::visitCommand(Command_ptr command) {
}

void SyntacticOptimizer::visitAssert(Assert_ptr assert_command) {
  visit_and_callback(assert_command->term);
}

void SyntacticOptimizer::visitTerm(Term_ptr term) {
}

void SyntacticOptimizer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void SyntacticOptimizer::visitExists(Exists_ptr exists_term) {
  visit_and_callback(exists_term->term);
}

void SyntacticOptimizer::visitForAll(ForAll_ptr for_all_term) {
}

void SyntacticOptimizer::visitLet(Let_ptr let_term) {
  // Variable_ptr variable = new Variable(primitive, sort->var_type->getType());
  //   symbol_table_->add_variable(variable);
  for(auto var_binding_term : *(let_term->var_binding_list)) {
    // switch(var_binding_term->term->type()) {
    //   case Term::Type::PLUS:
    //   case Term::Type::MINUS:
    //   case Term::Type::TIMES:
    //   case Term::Type::DIV:
    //   case Term::Type::UMINUS: {
    //     Variable_ptr variable = new Variable(var_binding_term->symbol->clone(),SMT::TVariable::Type::INT);
    //     symbol_table_->add_variable(variable);
    //     break;
    //   }
    //   default: {
    //     Variable_ptr variable = new Variable(var_binding_term->symbol->clone(),SMT::TVariable::Type::BOOL);
    //     symbol_table_->add_variable(variable);
    //     break;
    //   }
    // }
    visit(var_binding_term);
  }

  visit_and_callback(let_term->term);

  // callback_ = [let_term](Term_ptr & term) mutable {
  //   TermList_ptr term_list = new TermList();
  //   for(auto var_binding_term : *(let_term->var_binding_list)) {
  //     term_list->push_back(new Eq(new QualIdentifier(new Identifier(var_binding_term->symbol->clone())),var_binding_term->term->clone()));
  //   }
  //   term_list->push_back(let_term->term);
  //   let_term->term = nullptr;
  //   term = new And(term_list);
  //   delete let_term;
  // };

  callback_ = [let_term](Term_ptr & term) mutable {
    term = let_term->term;
    let_term->term = nullptr;
    delete let_term;
  };
}

void SyntacticOptimizer::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;
  bool has_false_term = false;
  std::vector<TermList> or_term_lists;
  int pos = 0;
  for (auto iter = and_term->term_list->begin(); iter != and_term->term_list->end();) {
  	
    if(Ite_ptr ite_term = dynamic_cast<Ite_ptr>(*iter)) {
      if(transform_ite_) {
        Term_ptr true_condition = ite_term->cond->clone();
        visit_and_callback(true_condition);
        Term_ptr false_condition = new Not(true_condition->clone());
        visit_and_callback(false_condition); // push down the negation
        
        for(auto it : *and_term->term_list) {
          // LOG(INFO) << it->str();
          bool first = check_condition_against_term(true_condition,it);
          bool second = check_condition_against_term(false_condition,it);
          
          Term_ptr t = new Not(it->clone());
          visit_and_callback(t);

          bool first2 = check_condition_against_term(true_condition,t);
          bool second2 = check_condition_against_term(false_condition,t);
          
          if(first and second) {
            break;
          } else if(first and not second) {
            *iter = ite_term->then_branch;
            ite_term->then_branch = nullptr;
            delete ite_term; ite_term = nullptr;
            break;
          } else if(not first and second) {
            *iter = ite_term->else_branch;
            ite_term->else_branch = nullptr;
            delete ite_term; ite_term = nullptr;
            break;
          }

          if(first2 and not second2) {
            *iter = ite_term->else_branch;
            ite_term->else_branch = nullptr;
            delete ite_term; ite_term = nullptr;
            break;
          } else if(not first2 and second2) {
            *iter = ite_term->then_branch;
            ite_term->then_branch = nullptr;
            delete ite_term; ite_term = nullptr;
            break;
          }
          
        }
        delete true_condition;
        delete false_condition;
      }
    }
    
    visit_and_callback(*iter);
  	if (!ite_terms_.empty()) {
  	  if(dynamic_cast<Or_ptr>(*iter) != nullptr) {
        LOG(FATAL) << "ite_terms should be empty if child is or_term!";
      }

      and_term->term_list->insert(and_term->term_list->end(),ite_terms_.begin(),ite_terms_.end());
      iter = and_term->term_list->begin() + pos;
      ite_terms_.clear();
  	}

  	if (check_bool_constant_value(*iter, "true") and and_term->term_list->size() > 1) {
      DVLOG(VLOG_LEVEL) << "remove: 'true' constant from 'and'";
      // just in case
      symbol_table_->merge_scopes(symbol_table_->top_scope(),*iter);
      delete (*iter); *iter = nullptr;
      iter = and_term->term_list->erase(iter);
    } else if (And_ptr sub_and_term = dynamic_cast<And_ptr>(*iter)) { // Associativity
      and_term->term_list->erase(iter);
      and_term->term_list->insert(iter, sub_and_term->term_list->begin(), sub_and_term->term_list->end());
      sub_and_term->term_list->clear();
      delete sub_and_term;
      iter = and_term->term_list->begin() + pos; // insertion invalidates iter, reset it
    } else if (check_bool_constant_value(*iter, "false")) {
      DVLOG(VLOG_LEVEL) << "has 'false' constant, UNSAT 'and'";
      has_false_term = true;
      break;
    } else {
      iter++;
      pos++;
    }
  }

  if (has_false_term) {
    add_callback_to_replace_with_bool(and_term, false);
  } else if (and_term->term_list->empty()) {
    add_callback_to_replace_with_bool(and_term, true);
  } else if (and_term->term_list->size() == 1) {
    auto child_term = and_term->term_list->front();
    // simplify, but always make sure there is at least one AND at top scope
    if (dynamic_cast<And_ptr>(child_term) or (dynamic_cast<Or_ptr>(child_term) && symbol_table_->top_scope() != root_)) {
      callback_ = [and_term, child_term](Term_ptr & term) mutable {
        and_term->term_list->clear();
        delete and_term;
        term = child_term;
      };
    }
  }

  if(!ss_terms.empty()) {
    and_term->term_list->insert(and_term->term_list->end(),ss_terms.begin(),ss_terms.end());
    ss_terms.clear();
  }

  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;
}

void SyntacticOptimizer::visitOr(Or_ptr or_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;

  int pos = 0;
  for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
    auto before_scope = *iter;
  	symbol_table_->push_scope(*iter,false);
    visit_and_callback(*iter);
    auto after_scope = *iter;

    // if there are ite_terms, take care of them
    if(!ite_terms_.empty()) {
      if(dynamic_cast<And_ptr>(*iter) != nullptr) {
        LOG(FATAL) << "ite_terms should be empty if child is and_term!";
      }

      TermList_ptr sub_terms = new TermList();
      sub_terms->push_back(*iter);
      sub_terms->insert(sub_terms->end(),ite_terms_.begin(),ite_terms_.end());
      
      ite_terms_.clear();
      or_term->term_list->erase(iter);
      or_term->term_list->insert(iter,new And(sub_terms));
      iter = or_term->term_list->begin() + pos;
    }
    if (check_bool_constant_value(*iter, "false")) {
      DVLOG(VLOG_LEVEL) << "remove: 'false' constant from 'or'";
      delete (*iter);
      iter = or_term->term_list->erase(iter);
    } else {
      // // term for scope may have changed, refactor equivalence & variable classes
    	// if(Ast2Dot::toString(before_scope) != Ast2Dot::toString(after_scope)) {
      if(before_scope != after_scope) {
    		DVLOG(VLOG_LEVEL) << "scope term changed after visiting, refactoring...";
				symbol_table_->refactor_scope(before_scope,after_scope);
      }
      pos++;
      iter++;
    }
		symbol_table_->pop_scope();
  }

  if (or_term->term_list->empty()) {
    add_callback_to_replace_with_bool(or_term, false);
  } else if (or_term->term_list->size() == 1) {
    auto child_term = or_term->term_list->front();
    if (dynamic_cast<And_ptr>(child_term) or dynamic_cast<Or_ptr>(child_term)) {
      // if child term an AND term, merge upper scope with child scope
    	symbol_table_->merge_scopes(symbol_table_->top_scope(),child_term);
      callback_ = [or_term, child_term](Term_ptr & term) mutable {
        or_term->term_list->clear();
        delete or_term;
        term = child_term;
      };
    }
  }

  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;
}

void SyntacticOptimizer::visitNot(Not_ptr not_term) {
  visit_and_callback(not_term->term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_term << "@" << not_term;
  switch (not_term->term->type()) {
    case Term::Type::NOT: {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (not (not a) to a";
      callback_ = [not_term](Term_ptr & term) mutable {
        Not_ptr child_not = dynamic_cast<Not_ptr>(not_term->term);
        term = child_not->term;
        child_not->term = nullptr;
        delete not_term;
      };
      break;
    }
    case Term::Type::EQ: {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (not (= ...)) to (!= ...)";
      callback_ = [not_term](Term_ptr & term) mutable {
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
      callback_ = [not_term](Term_ptr & term) mutable {
        NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>(not_term->term);
        Eq_ptr eq_term = new Eq(not_eq_term->left_term, not_eq_term->right_term);
        not_eq_term->left_term = nullptr; not_eq_term->right_term = nullptr;
        term = eq_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::GT: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Gt_ptr gt_term = dynamic_cast<Gt_ptr>(not_term->term);
        Le_ptr le_term = new Le(gt_term->left_term, gt_term->right_term);
        gt_term->left_term = nullptr; gt_term->right_term = nullptr;
        term = le_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::GE: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Ge_ptr ge_term = dynamic_cast<Ge_ptr>(not_term->term);
        Lt_ptr lt_term = new Lt(ge_term->left_term, ge_term->right_term);
        ge_term->left_term = nullptr; ge_term->right_term = nullptr;
        term = lt_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::LT: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Lt_ptr lt_term = dynamic_cast<Lt_ptr>(not_term->term);
        Ge_ptr ge_term = new Ge(lt_term->left_term, lt_term->right_term);
        lt_term->left_term = nullptr; lt_term->right_term = nullptr;
        term = ge_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::LE: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Le_ptr le_term = dynamic_cast<Le_ptr>(not_term->term);
        Gt_ptr gt_term = new Gt(le_term->left_term, le_term->right_term);
        le_term->left_term = nullptr; le_term->right_term = nullptr;
        term = gt_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::IN: {
      callback_ = [not_term](Term_ptr & term) mutable {
        In_ptr in_term = dynamic_cast<In_ptr>(not_term->term);
        NotIn_ptr not_in_term = new NotIn(in_term->left_term, in_term->right_term);
        in_term->left_term = nullptr; in_term->right_term = nullptr;
        term = not_in_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::NOTIN: {
      callback_ = [not_term](Term_ptr & term) mutable {
        NotIn_ptr not_in_term = dynamic_cast<NotIn_ptr>(not_term->term);
        In_ptr in_term = new In(not_in_term->left_term, not_in_term->right_term);
        not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;
        term = in_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::CONTAINS: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Contains_ptr contains_term = dynamic_cast<Contains_ptr>(not_term->term);
        NotContains_ptr not_contains_term = new NotContains(contains_term->subject_term, contains_term->search_term);
        contains_term->subject_term = nullptr; contains_term->search_term = nullptr;
        term = not_contains_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::NOTCONTAINS: {
      callback_ = [not_term](Term_ptr & term) mutable {
        NotContains_ptr not_contains_term = dynamic_cast<NotContains_ptr>(not_term->term);
        Contains_ptr contains_term = new Contains(not_contains_term->subject_term, not_contains_term->search_term);
        not_contains_term->subject_term = nullptr; not_contains_term->search_term = nullptr;
        term = contains_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::BEGINS: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Begins_ptr begins_term = dynamic_cast<Begins_ptr>(not_term->term);
        NotBegins_ptr not_begins_term = new NotBegins(begins_term->subject_term, begins_term->search_term);
        begins_term->subject_term = nullptr; begins_term->search_term = nullptr;
        term = not_begins_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::NOTBEGINS: {
      callback_ = [not_term](Term_ptr & term) mutable {
        NotBegins_ptr not_begins_term = dynamic_cast<NotBegins_ptr>(not_term->term);
        Begins_ptr begins_term = new Begins(not_begins_term->subject_term, not_begins_term->search_term);
        not_begins_term->subject_term = nullptr; not_begins_term->search_term = nullptr;
        term = begins_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::ENDS: {
      callback_ = [not_term](Term_ptr & term) mutable {
        Ends_ptr ends_term = dynamic_cast<Ends_ptr>(not_term->term);
        NotEnds_ptr not_ends_term = new NotEnds(ends_term->subject_term, ends_term->search_term);
        ends_term->subject_term = nullptr; ends_term->search_term = nullptr;
        term = not_ends_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::NOTENDS: {
      callback_ = [not_term](Term_ptr & term) mutable {
        NotEnds_ptr not_ends_term = dynamic_cast<NotEnds_ptr>(not_term->term);
        Ends_ptr ends_term = new Ends(not_ends_term->subject_term, not_ends_term->search_term);
        not_ends_term->subject_term = nullptr; not_ends_term->search_term = nullptr;
        term = ends_term;
        delete not_term;
      };
      break;
    }
    case Term::Type::TERMCONSTANT: {
			callback_ = [not_term](Term_ptr & term) mutable {
				TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(not_term->term);
				if(Primitive::Type::BOOL == term_constant->getValueType() and "true" == term_constant->getValue()) {
					term_constant->primitive->setData("false");
					not_term->term = nullptr;
					term = term_constant;
					delete not_term;
				} else if(Primitive::Type::BOOL == term_constant->getValueType() and "false" == term_constant->getValue()) {
					term_constant->primitive->setData("true");
					not_term->term = nullptr;
					term = term_constant;
					delete not_term;
				} else {
					LOG(FATAL) << "non-boolean term constant cannot be negated: " << *term_constant;
				}
			};
			break;
		}
    default:
      break;
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_term << "@" << not_term;
}

void SyntacticOptimizer::visitUMinus(UMinus_ptr u_minus_term) {
  visit_and_callback(u_minus_term->term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *u_minus_term << "@" << u_minus_term;
  if (Term::Type::UMINUS == u_minus_term->term->type()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- (- a) to a";
    callback_ = [u_minus_term](Term_ptr & term) mutable {
      UMinus_ptr child_u_minus = dynamic_cast<UMinus_ptr>(u_minus_term->term);
      term = child_u_minus->term;
      child_u_minus->term = nullptr;
      delete u_minus_term;
    };
  } else if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(u_minus_term->term)) {
    if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (- c) to -c";
      std::string data = term_constant->getValue();
      if (data.find("-") == 0) {
        term_constant->primitive->setData(data.substr(1));
      } else {
        term_constant->primitive->setData("-" + data);
      }
      callback_ = [u_minus_term](Term_ptr & term) mutable {
        term = u_minus_term->term;
        u_minus_term->term = nullptr;
        delete u_minus_term;
      };
    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *u_minus_term << "@" << u_minus_term;
}

void SyntacticOptimizer::visitMinus(Minus_ptr minus_term) {
  visit_and_callback(minus_term->left_term);
  visit_and_callback(minus_term->right_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *minus_term << "@" << minus_term;
  if (Term::Type::TERMCONSTANT == minus_term->left_term->type()
      	and Term::Type::TERMCONSTANT == minus_term->right_term->type()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- lc rc) to lc-rc";
    callback_ = [this, minus_term](Term_ptr & term) mutable {
      TermConstant_ptr left_constant = dynamic_cast<TermConstant_ptr>(minus_term->left_term);
      TermConstant_ptr right_constant = dynamic_cast<TermConstant_ptr>(minus_term->right_term);

      int left_value = std::stoi(left_constant->getValue());
      int right_value = std::stoi(right_constant->getValue());

      int result = left_value - right_value;
      if (result >= 0) {
        term = this->generate_term_constant(std::to_string(result), Primitive::Type::NUMERAL);
      } else {
        term = new UMinus(this->generate_term_constant(std::to_string(-result), Primitive::Type::NUMERAL));
      }
      delete minus_term;
    };
  } else if (Term::Type::TERMCONSTANT == minus_term->right_term->type()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
    if (term_constant->getValue() == "0") {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (- l 0) to l";
      callback_ = [minus_term](Term_ptr & term) mutable {
        term = minus_term->left_term;
        minus_term->left_term = nullptr;
        delete minus_term;
      };
    } else if(Term::Type::MINUS == minus_term->left_term->type()) {
      Minus_ptr child_minus = dynamic_cast<Minus_ptr>(minus_term->left_term);
      if (Term::Type::TERMCONSTANT == minus_term->right_term->type() &&
          Term::Type::TERMCONSTANT == child_minus->right_term->type()) {

        DVLOG(VLOG_LEVEL) << "Transforming operation: (- (- l c1) c2) to (- l (c1 + c2))";
        callback_ = [minus_term, this](Term_ptr &term) mutable {
          Minus_ptr child_minus = dynamic_cast<Minus_ptr>(minus_term->left_term);
          TermConstant_ptr c1_ptr = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
          TermConstant_ptr c2_ptr = dynamic_cast<TermConstant_ptr>(child_minus->right_term);
          int c1 = std::stoi(c1_ptr->getValue());
          int c2 = std::stoi(c2_ptr->getValue());
          Term_ptr c3_ptr = generate_term_constant(std::to_string(c2 + c1), Primitive::Type::NUMERAL);
          delete child_minus->right_term;
          child_minus->right_term = c3_ptr;
          minus_term->left_term = nullptr;
          delete minus_term;
          term = child_minus;
        };
      }
    }
  } else if (Term::Type::TERMCONSTANT == minus_term->left_term->type()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(minus_term->left_term);
    if (term_constant->getValue() == "0") {
      DVLOG(VLOG_LEVEL) << "Transforming operation: (- 0 l) to (- l)";
      callback_ = [minus_term](Term_ptr & term) mutable {
        term = new UMinus(minus_term->right_term);
        minus_term->right_term = nullptr;
        delete minus_term;
      };
    }
  } else if (Term::Type::UMINUS == minus_term->right_term->type()) {
    DVLOG(VLOG_LEVEL) << "Transforming operation: (- l (- r) to (+ l r)";
    callback_ = [minus_term](Term_ptr & term) mutable {
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
  DVLOG(VLOG_LEVEL) << "post visit end: " << *minus_term << "@" << minus_term;
}

void SyntacticOptimizer::visitPlus(Plus_ptr plus_term) {
  for (auto& term_ptr : *(plus_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *plus_term << "@" << plus_term;

  int constant_value = 0;
  int pos = 0;

  TermList_ptr div_terms = new TermList();

  for (auto iter = plus_term->term_list->begin(); iter != plus_term->term_list->end();) {
    if (Term::Type::PLUS == (*iter)->type()) {
      Plus_ptr sub_plus_term = dynamic_cast<Plus_ptr>(*iter);
      plus_term->term_list->erase(iter);
      plus_term->term_list->insert(iter, sub_plus_term->term_list->begin(), sub_plus_term->term_list->end());
      sub_plus_term->term_list->clear();
      delete sub_plus_term;
      iter = plus_term->term_list->begin() + pos;  // insertion invalidates iter, reset it
      continue;
    } else if (Term::Type::DIV == (*iter)->type()) {
      div_terms->push_back(*iter);
      plus_term->term_list->erase(iter);
      iter = plus_term->term_list->begin() + pos;
      continue;
    } else if (Term::Type::TERMCONSTANT == (*iter)->type()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      std::string value = term_constant->getValue();
      constant_value += std::stoi(value);
      delete term_constant;  // deallocate
      plus_term->term_list->erase(iter);
      continue;
    } else if (Term::Type::UMINUS == (*iter)->type()) {
      UMinus_ptr u_minus = dynamic_cast<UMinus_ptr>(*iter);
      if (Term::Type::TERMCONSTANT == u_minus->term->type()) {
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(u_minus->term);
        std::string value = term_constant->getValue();
        constant_value -= std::stoi(value);
        delete u_minus;  // deallocate
        plus_term->term_list->erase(iter);
        continue;
      }
    }
    iter++;
    pos++;
  }

  if (constant_value != 0) {
    if (constant_value > 0) {
      plus_term->term_list->insert(plus_term->term_list->begin(),
                                   generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
    } else {
      UMinus_ptr u_minus = new UMinus(
          generate_term_constant(std::to_string(-constant_value), Primitive::Type::NUMERAL));
      plus_term->term_list->insert(plus_term->term_list->begin(), u_minus);
    }
  } else if (plus_term->term_list->size() == 0) {  // constant is the only term, add it to result
    plus_term->term_list->push_back(generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
  }  // else initial constant value is zero, do not need to add it

  if(div_terms->size() > 0) {
    callback_ = [plus_term, div_terms] (Term_ptr & term) mutable {
      TermList_ptr div_times_termlist = new TermList();
      
      std::map<Term_ptr, Times_ptr> mult_map;
      for(auto it : *div_terms) {
        Div_ptr div_term = dynamic_cast<Div_ptr>(it);
        mult_map[it] = new Times(new TermList());
        mult_map[it]->term_list->push_back(div_term->term_list->at(0)->clone());
      }

      for(auto it : *div_terms) {
        Div_ptr div_term = dynamic_cast<Div_ptr>(it);
        for(auto map_it : mult_map) {
          if(Ast2Dot::toString(div_term) != Ast2Dot::toString(map_it.first)) {
            map_it.second->term_list->push_back(div_term->term_list->at(1)->clone());
          }
        }
      }
      
      for(auto &iter : *div_terms) {
        Div_ptr div_term = dynamic_cast<Div_ptr>(iter);
        div_times_termlist->push_back(div_term->term_list->at(1)->clone());  

        for(auto iter = plus_term->term_list->begin(); iter != plus_term->term_list->end(); iter++) {
          TermList_ptr times_termlist = new TermList();
          times_termlist->push_back(*iter);
          times_termlist->push_back(div_term->term_list->at(1)->clone());

          Times_ptr times_term = new Times(times_termlist);
          *iter = times_term;
        }
      }
      
      for(auto &map_it : mult_map) {
        plus_term->term_list->push_back(map_it.second->clone());
        delete map_it.second;
        map_it.second = nullptr;
      }


      Times_ptr div_times_term = new Times(div_times_termlist);
      TermList_ptr div_termlist = new TermList();
      div_termlist->push_back(plus_term);
      div_termlist->push_back(div_times_term);
      Div_ptr div_term = new Div(div_termlist);

      term = div_term;
    };
  } else if (plus_term->term_list->size() == 1) {
    callback_ = [plus_term] (Term_ptr & term) mutable {
      term = plus_term->term_list->front();
      plus_term->term_list->clear();
      delete plus_term;
    };
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *plus_term << "@" << plus_term;
}

void SyntacticOptimizer::visitTimes(Times_ptr times_term) {
  for (auto& term_ptr : *(times_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *times_term << "@" << times_term;

  int constant_value = 1;
  int pos = 0;

  TermList_ptr div_terms = new TermList();
  for (auto iter = times_term->term_list->begin(); iter != times_term->term_list->end();) {
    if (Term::Type::TIMES == (*iter)->type()) {
      Times_ptr sub_times_term = dynamic_cast<Times_ptr>(*iter);
      times_term->term_list->erase(iter);
      times_term->term_list->insert(iter, sub_times_term->term_list->begin(), sub_times_term->term_list->end());
      sub_times_term->term_list->clear();
      delete sub_times_term;
      iter = times_term->term_list->begin() + pos;  // insertion invalidates iter, reset it
      continue;
    } else if (Term::Type::DIV == (*iter)->type()) {
      div_terms->push_back(*iter);
      times_term->term_list->erase(iter);
      iter = times_term->term_list->begin() + pos;
      continue;
    } else if (Term::Type::TERMCONSTANT == (*iter)->type()) {
      TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter);
      std::string value = term_constant->getValue();
      constant_value *= std::stoi(value);
      delete term_constant;  // deallocate
      times_term->term_list->erase(iter);
      continue;
    } else if (Term::Type::UMINUS == (*iter)->type()) {
      UMinus_ptr u_minus = dynamic_cast<UMinus_ptr>(*iter);
      if (Term::Type::TERMCONSTANT == u_minus->term->type()) {
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(u_minus->term);
        std::string value = term_constant->getValue();
        constant_value *= -std::stoi(value);
        delete u_minus;  // deallocate
        times_term->term_list->erase(iter);
        continue;
      }
    }
    iter++;
    pos++;
    if (constant_value == 0) {
      break;
    }
  }

  if (constant_value != 1 and constant_value != 0) {
    if (constant_value > 0) {
      times_term->term_list->insert(times_term->term_list->begin(),
                                    generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
    } else {
      UMinus_ptr u_minus = new UMinus(
          generate_term_constant(std::to_string(-constant_value), Primitive::Type::NUMERAL));
      times_term->term_list->insert(times_term->term_list->begin(), u_minus);
    }
  } else if (times_term->term_list->size() == 0) {  // constant is the only term, add it to result
    times_term->term_list->push_back(generate_term_constant(std::to_string(constant_value), Primitive::Type::NUMERAL));
  } else if (constant_value == 0) {  // make it zero
    times_term->term_list->clear();
    times_term->term_list->push_back(generate_term_constant("0", Primitive::Type::NUMERAL));
  }  // else initial constant value is 1, do not need to add it

  if(div_terms->size() > 0) {
    callback_ = [times_term, div_terms] (Term_ptr & term) mutable {
      TermList_ptr div_times_termlist = new TermList();
      for(auto &iter : *div_terms) {
        Div_ptr div_term = dynamic_cast<Div_ptr>(iter);
        times_term->term_list->push_back(div_term->term_list->at(0)->clone());
        div_times_termlist->push_back(div_term->term_list->at(1)->clone());  
        delete iter;
      }
      div_terms->clear();
      delete div_terms;

      Times_ptr div_times_term = new Times(div_times_termlist);
      TermList_ptr div_termlist = new TermList();
      div_termlist->push_back(times_term);
      div_termlist->push_back(div_times_term);
      Div_ptr div_term = new Div(div_termlist);

      term = div_term;
    };
  } else if (times_term->term_list->size() == 1) {
    callback_ = [times_term] (Term_ptr & term) mutable {
      term = times_term->term_list->front();
      times_term->term_list->clear();
      delete times_term;
    };
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *times_term << "@" << times_term;
}

void SyntacticOptimizer::visitDiv(Div_ptr div_term) {
  for (auto& term_ptr : *(div_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *div_term << "@" << div_term;
  
  if(div_term->term_list->size() != 2) {
    LOG(FATAL) << "div term must have two args";
  }

  if(Term::Type::DIV == div_term->term_list->at(0)->type()) {
    callback_ = [div_term](Term_ptr & term) mutable {
      Div_ptr sub_div_term = dynamic_cast<Div_ptr>(div_term->term_list->at(0));
      Times_ptr times_term = new Times(new TermList());
      times_term->term_list->push_back(div_term->term_list->at(1));
      times_term->term_list->push_back(sub_div_term->term_list->at(1));
      
      sub_div_term->term_list->at(1) = times_term;
      div_term->term_list->clear();
      delete div_term;
      term = sub_div_term;
    };
  }
  
  DVLOG(VLOG_LEVEL) << "post visit end: " << *div_term << "@" << div_term;
}

void SyntacticOptimizer::visitEq(Eq_ptr eq_term) {

  if(Ite_ptr ite_term = dynamic_cast<Ite_ptr>(eq_term->left_term)) {
    if(Ast2Dot::isEquivalent(ite_term->then_branch,eq_term->right_term)) {
      callback_ = [eq_term, ite_term](Term_ptr & term) mutable {
//        Ast2Dot::inspectAST(term);
        term = ite_term->cond;
        ite_term->cond = nullptr;
//        Ast2Dot::inspectAST(term);
//        std::cin.get();
        delete eq_term;
      };
      return;
    } else if(Ast2Dot::isEquivalent(ite_term->else_branch,eq_term->right_term)) {
      callback_ = [eq_term, ite_term](Term_ptr & term) mutable {
//        Ast2Dot::inspectAST(term);
        term = new Not(ite_term->cond);
        ite_term->cond = nullptr;
        delete eq_term;
//        Ast2Dot::inspectAST(term);
//        std::cin.get();
      };
      return;
    }
  } else if(symbol_table_->ss_term_vars.find(Ast2Dot::toString(eq_term->left_term)) != symbol_table_->ss_term_vars.end()) {
    ss_flag = true;
  } else if(symbol_table_->ss_term_vars.find(Ast2Dot::toString(eq_term->right_term)) != symbol_table_->ss_term_vars.end()) {
    ss_flag = true;
  }

  visit_and_callback(eq_term->left_term);
  visit_and_callback(eq_term->right_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *eq_term << "@" << eq_term;

  bool match_p = match_prefix(eq_term->left_term, eq_term->right_term);
  if (!match_p) {
    add_callback_to_replace_with_bool(eq_term, false);
    return;
  }
  bool match_s = match_suffix(eq_term->left_term, eq_term->right_term);
  if (!match_s) {
    add_callback_to_replace_with_bool(eq_term, false);
    return;
  }
  //Might need to update.
  visit_and_callback(eq_term->left_term);
  visit_and_callback(eq_term->right_term);

  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;

  constant_term_checker_left.start(eq_term->left_term, Optimization::ConstantTermChecker::Mode::FULL);
  constant_term_checker_right.start(eq_term->right_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker_left.is_constant() and constant_term_checker_right.is_constant()) {
    bool result = (constant_term_checker_left.get_constant_as_string() == constant_term_checker_right.get_constant_as_string());
    add_callback_to_replace_with_bool(eq_term, result);
    return;
  }
//  else if(constant_term_checker_left.is_constant()) {
//  	if(constant_term_checker_left.get_constant_as_string() == "false") {
//  		callback_ = [eq_term](Term_ptr & term) mutable {
//  			term = new Not(eq_term->right_term);
//  			eq_term->right_term = nullptr;
//  			delete eq_term;
//  		};
//  	} else if(constant_term_checker_left.get_constant_as_string() == "true") {
//  		callback_ = [eq_term](Term_ptr & term) mutable {
//  			term = eq_term->right_term;
//  			eq_term->right_term = nullptr;
//  		}
//  	}
//  }

  if(Term::Type::QUALIDENTIFIER == eq_term->right_term->type() && Term::Type::QUALIDENTIFIER != eq_term->left_term->type()) {
    auto temp = eq_term->left_term;
    eq_term->left_term = eq_term->right_term;
    eq_term->right_term = temp;
  }

  // if EQ is of the form X = Y / C, where C is constant, transform to X * C = Y
  // if(Term::Type::QUALIDENTIFIER == eq_term->left_term->type() && Term::Type::DIV == eq_term->right_term->type()) {
  //   Div_ptr div_term = dynamic_cast<Div_ptr>(eq_term->right_term);
  //   if(div_term->term_list->size() == 2) {
  //     if(Term::Type::QUALIDENTIFIER == div_term->term_list->at(0)->type() 
  //           && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
  //       callback_ = [eq_term](Term_ptr & term) mutable {
  //         Div_ptr div_term = dynamic_cast<Div_ptr>(eq_term->right_term);
  //         TermList_ptr times_list = new TermList();
  //         times_list->push_back(div_term->term_list->at(1)->clone());
  //         times_list->push_back(eq_term->left_term->clone());
  //         Times_ptr times_term = new Times(times_list);
  //         QualIdentifier_ptr right_var = dynamic_cast<QualIdentifier_ptr>(div_term->term_list->at(0)->clone());
  //         delete eq_term;
  //         term = new Eq(right_var,times_term);
  //       };
  //       return;
  //     }
  //   }
  //   LOG(FATAL) << "Operation not supported";
  // }

  // Y / C1 = X / C2
  if(eq_term->left_term->type() == Term::Type::DIV and eq_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr left_div_term = dynamic_cast<Div_ptr>(eq_term->left_term);
    Div_ptr right_div_term = dynamic_cast<Div_ptr>(eq_term->left_term);
    if(left_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == left_div_term->term_list->at(1)->type()
          and right_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == right_div_term->term_list->at(1)->type()) {
      callback_ = [eq_term](Term_ptr & term) mutable {
        Div_ptr left_div_term = dynamic_cast<Div_ptr>(eq_term->left_term);
        Div_ptr right_div_term = dynamic_cast<Div_ptr>(eq_term->right_term);

        TermList_ptr left_times_list = new TermList();
        left_times_list->push_back(right_div_term->term_list->at(1)->clone());
        left_times_list->push_back(left_div_term->term_list->at(0)->clone());
        
        TermList_ptr right_times_list = new TermList();
        right_times_list->push_back(left_div_term->term_list->at(1)->clone());
        right_times_list->push_back(right_div_term->term_list->at(0)->clone());

        term = new Eq(new Times(left_times_list), new Times(right_times_list));
        delete eq_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(eq_term->left_term->type() == Term::Type::DIV) {  //    y/z = x
    Div_ptr div_term = dynamic_cast<Div_ptr>(eq_term->left_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [eq_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(eq_term->left_term);

        TermList_ptr times_list = new TermList();
        times_list->push_back(new UMinus(div_term->term_list->at(1)->clone()));
        times_list->push_back(eq_term->right_term->clone());
        Times_ptr times_term = new Times(times_list);

        TermList_ptr plus_list = new TermList();
        plus_list->push_back(div_term->term_list->at(0)->clone());
        plus_list->push_back(times_term);
        Plus_ptr plus_term = new Plus(plus_list);

        TermConstant_ptr zero_constant = new TermConstant(new Primitive("0",SMT::Primitive::Type::NUMERAL));
        UMinus_ptr neg_denominator_term = new UMinus(div_term->term_list->at(1)->clone());
        
        // split on whether numerator is positive or negative
        Ge_ptr numerator_ge_zero_term = new Ge(div_term->term_list->at(0)->clone(),zero_constant->clone());
        Ge_ptr remainder_ge_zero_term = new Ge(plus_term->clone(),zero_constant->clone());
        Lt_ptr remainder_lt_denominator_term = new Lt(plus_term->clone(),div_term->term_list->at(1)->clone());

        Lt_ptr numerator_lt_zero_term = new Lt(div_term->term_list->at(0)->clone(),zero_constant->clone());
        Gt_ptr remainder_gt_neg_denominator_term = new Gt(plus_term->clone(),neg_denominator_term);
        Le_ptr remainder_le_zero_term = new Le(plus_term,zero_constant);

        // result is OR of the AND of each case
        TermList_ptr pos_and_termlist = new TermList();
        pos_and_termlist->push_back(numerator_ge_zero_term);
        pos_and_termlist->push_back(remainder_ge_zero_term);
        pos_and_termlist->push_back(remainder_lt_denominator_term);
        And_ptr pos_and_term = new And(pos_and_termlist);

        TermList_ptr neg_and_termlist = new TermList();
        neg_and_termlist->push_back(numerator_lt_zero_term);
        neg_and_termlist->push_back(remainder_gt_neg_denominator_term);
        neg_and_termlist->push_back(remainder_le_zero_term);
        And_ptr neg_and_term = new And(neg_and_termlist);

        TermList_ptr or_termlist = new TermList();
        or_termlist->push_back(pos_and_term);
        or_termlist->push_back(neg_and_term);
        Or_ptr or_term = new Or(or_termlist);

        term = or_term;
        delete eq_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(eq_term->right_term->type() == Term::Type::DIV) { //   x = y/z
    Div_ptr div_term = dynamic_cast<Div_ptr>(eq_term->right_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      // can't just multiply both sides by the constant, need boundary constraints
      // for x = y/z, create two constraints:
      // y - zx >= 0
      // y - zx < z
      callback_ = [eq_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(eq_term->right_term);

        TermList_ptr times_list = new TermList();
        times_list->push_back(new UMinus(div_term->term_list->at(1)->clone()));
        times_list->push_back(eq_term->left_term->clone());
        Times_ptr times_term = new Times(times_list);

        TermList_ptr plus_list = new TermList();
        plus_list->push_back(div_term->term_list->at(0)->clone());
        plus_list->push_back(times_term);
        Plus_ptr plus_term = new Plus(plus_list);
        
        TermConstant_ptr zero_constant = new TermConstant(new Primitive("0",SMT::Primitive::Type::NUMERAL));
        UMinus_ptr neg_denominator_term = new UMinus(div_term->term_list->at(1)->clone());
        
        // split on whether numerator is positive or negative
        Ge_ptr numerator_ge_zero_term = new Ge(div_term->term_list->at(0)->clone(),zero_constant->clone());
        Ge_ptr remainder_ge_zero_term = new Ge(plus_term->clone(),zero_constant->clone());
        Lt_ptr remainder_lt_denominator_term = new Lt(plus_term->clone(),div_term->term_list->at(1)->clone());

        Lt_ptr numerator_lt_zero_term = new Lt(div_term->term_list->at(0)->clone(),zero_constant->clone());
        Gt_ptr remainder_gt_neg_denominator_term = new Gt(plus_term->clone(),neg_denominator_term);
        Le_ptr remainder_le_zero_term = new Le(plus_term,zero_constant);

        // result is OR of the AND of each case
        TermList_ptr pos_and_termlist = new TermList();
        pos_and_termlist->push_back(numerator_ge_zero_term);
        pos_and_termlist->push_back(remainder_ge_zero_term);
        pos_and_termlist->push_back(remainder_lt_denominator_term);
        And_ptr pos_and_term = new And(pos_and_termlist);

        TermList_ptr neg_and_termlist = new TermList();
        neg_and_termlist->push_back(numerator_lt_zero_term);
        neg_and_termlist->push_back(remainder_gt_neg_denominator_term);
        neg_and_termlist->push_back(remainder_le_zero_term);
        And_ptr neg_and_term = new And(neg_and_termlist);

        TermList_ptr or_termlist = new TermList();
        or_termlist->push_back(pos_and_term);
        or_termlist->push_back(neg_and_term);
        Or_ptr or_term = new Or(or_termlist);

        term = or_term;
        delete eq_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  }

  // check for equality with concat where prefix var is same on both sides
  if(Term::Type::QUALIDENTIFIER == eq_term->left_term->type() && Term::Type::CONCAT == eq_term->right_term->type()) {
    Concat_ptr concat_term = dynamic_cast<Concat_ptr>(eq_term->right_term);
    QualIdentifier_ptr left_var = dynamic_cast<QualIdentifier_ptr>(eq_term->left_term);
    
    if(Term::Type::QUALIDENTIFIER == concat_term->term_list->at(0)->type()) {
      QualIdentifier_ptr right_var = dynamic_cast<QualIdentifier_ptr>(concat_term->term_list->at(0));
      
      // if same variable, replace term
      if(left_var->getVarName() == right_var->getVarName()) {
        callback_ = [this, eq_term](Term_ptr & term) mutable {
          Concat_ptr concat_term = dynamic_cast<Concat_ptr>(eq_term->right_term);
          delete eq_term->left_term;
          eq_term->left_term = generate_term_constant("",Primitive::Type::STRING);
          delete concat_term->term_list->at(0);
          concat_term->term_list->at(0) = nullptr;
          concat_term->term_list->erase(concat_term->term_list->begin());
        };
        
        return;
      } else {
        symbol_table_->increment_variable_usage(left_var->getVarName());
        
        for(auto it : *concat_term->term_list) {
          if(QualIdentifier_ptr qualid = dynamic_cast<QualIdentifier_ptr>(it)) {
            symbol_table_->set_variable_concat(qualid->getVarName(),true);
          }
        }
      }
    } else {
      symbol_table_->increment_variable_usage(left_var->getVarName());
    }
  } else if(Term::Type::QUALIDENTIFIER == eq_term->right_term->type() && Term::Type::CONCAT == eq_term->left_term->type()) {
    Concat_ptr concat_term = dynamic_cast<Concat_ptr>(eq_term->left_term);
    QualIdentifier_ptr right_var = dynamic_cast<QualIdentifier_ptr>(eq_term->right_term);

    if(Term::Type::QUALIDENTIFIER == concat_term->term_list->at(0)->type()) {
      QualIdentifier_ptr left_var = dynamic_cast<QualIdentifier_ptr>(concat_term->term_list->at(0));
      
      // if same variable, replace term
      if(left_var->getVarName() == right_var->getVarName()) {
        callback_ = [this, eq_term](Term_ptr & term) mutable {
          Concat_ptr concat_term = dynamic_cast<Concat_ptr>(eq_term->left_term);
          delete eq_term->right_term;
          eq_term->right_term = generate_term_constant("",Primitive::Type::STRING);
          delete concat_term->term_list->at(0);
          concat_term->term_list->at(0) = nullptr;
          concat_term->term_list->erase(concat_term->term_list->begin());
        };

        return;
      } else {
        symbol_table_->increment_variable_usage(right_var->getVarName());
        
        for(auto it : *concat_term->term_list) {
          if(QualIdentifier_ptr qualid = dynamic_cast<QualIdentifier_ptr>(it)) {
            symbol_table_->set_variable_concat(qualid->getVarName(),true);
          }
        }
      }
    } else {
      symbol_table_->increment_variable_usage(right_var->getVarName());
    }
  }
  else if(CharAt_ptr charat_term = dynamic_cast<CharAt_ptr>(eq_term->left_term)) {
    if(Minus_ptr minus_term = dynamic_cast<Minus_ptr>(charat_term->index_term)) {
      if(Len_ptr len_term = dynamic_cast<Len_ptr>(minus_term->left_term)) {
        if(Term::Type::QUALIDENTIFIER == charat_term->subject_term->type()
              && Ast2Dot::isEquivalent(charat_term->subject_term,len_term->term)
              && Term::Type::TERMCONSTANT == minus_term->right_term->type()
              && Term::Type::TERMCONSTANT == eq_term->right_term->type()) {

          auto minus_right_term = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
          auto right_constant = dynamic_cast<TermConstant_ptr>(eq_term->right_term);
          auto qi_term = dynamic_cast<QualIdentifier_ptr>(len_term->term);
          if(std::stoi(minus_right_term->getValue()) == right_constant->getValue().length()) {

            callback_ = [eq_term,qi_term,right_constant](Term_ptr & term) mutable {
              auto ends_term = new Ends(qi_term->clone(),right_constant->clone());
              delete eq_term;
              term = ends_term;
            };
          }
        }
      }
    }
  }

  else if (IndexOf_ptr indexof_term = dynamic_cast<IndexOf_ptr>(eq_term->left_term)) {
    if(Term::Type::QUALIDENTIFIER == indexof_term->subject_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->search_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->from_index->type()
          && Term::Type::TERMCONSTANT == eq_term->right_term->type()) {
      auto subject_term = dynamic_cast<QualIdentifier_ptr>(indexof_term->subject_term);
      auto search_term = dynamic_cast<TermConstant_ptr>(indexof_term->search_term);
      auto from_index = dynamic_cast<TermConstant_ptr>(indexof_term->from_index);
      auto right_constant = dynamic_cast<TermConstant_ptr>(eq_term->right_term);

      if(from_index->getValue() == "0") {
        if(right_constant->getValue() == "-1") {
          callback_ = [eq_term, indexof_term](Term_ptr & term) mutable {
            auto contains = new NotContains(indexof_term->subject_term, indexof_term->search_term);
            indexof_term->subject_term = nullptr;
            indexof_term->search_term = nullptr;
            delete term;
            term = contains;
          };
        } else {
          std::string regex = std::string(std::stoi(right_constant->getValue()),'.') + search_term->getValue() + ".*";
          callback_ = [eq_term, indexof_term, regex, this](Term_ptr & term) mutable {
            auto in_term = new In(indexof_term->subject_term, generate_term_constant(regex,Primitive::Type::REGEX));
            indexof_term->subject_term = nullptr;
            delete term;
            term = in_term;
          };
        }
      }
    }
  }
  else if(SubString_ptr sub_string_term = dynamic_cast<SubString_ptr>(eq_term->left_term)) {
    if(Minus_ptr minus_term = dynamic_cast<Minus_ptr>(sub_string_term->end_index_term)) {
      if(Len_ptr len_term = dynamic_cast<Len_ptr>(minus_term->left_term)) {
        if(Ast2Dot::isEquivalent(sub_string_term->subject_term,len_term->term)
                && Ast2Dot::isEquivalent(sub_string_term->start_index_term,minus_term->right_term)
                && Term::Type::TERMCONSTANT == eq_term->right_term->type()) {
          // eq_term is just restricting the end of the string variable to be whatever is on the right hand side
          // the end occurs at start_index_term
          if(Plus_ptr plus_term = dynamic_cast<Plus_ptr>(sub_string_term->start_index_term)) {
            if(IndexOf_ptr indexof_term = dynamic_cast<IndexOf_ptr>(plus_term->term_list->at(1))) {
              if(Term::Type::QUALIDENTIFIER == sub_string_term->subject_term->type()
                    && Term::Type::QUALIDENTIFIER == indexof_term->subject_term->type()
                    && Term::Type::TERMCONSTANT == indexof_term->search_term->type()
                    && Term::Type::TERMCONSTANT == indexof_term->from_index->type()) {

                auto plus_first_term = dynamic_cast<TermConstant_ptr>(plus_term->term_list->at(0));
                auto eq_right_term = dynamic_cast<TermConstant_ptr>(eq_term->right_term);
                auto indexof_search_term = dynamic_cast<TermConstant_ptr>(indexof_term->search_term);
                auto indexof_start_term = dynamic_cast<TermConstant_ptr>(indexof_term->from_index);

                if(indexof_start_term->getValue() == "0") {
                  std::string regex = ".*" + indexof_search_term->getValue() + std::string(std::stoi(plus_first_term->getValue())-1,'.') + eq_right_term->getValue();

                  callback_ = [sub_string_term,regex,this](Term_ptr & term) mutable {
                    auto in_term = new In(sub_string_term->subject_term,generate_term_constant(regex,Primitive::Type::REGEX));
                    sub_string_term->subject_term = nullptr;

                    delete term;
                    term = in_term;
                  };
                }

              }
            }
          }

        }
      }
    }
  } else if(SubString_ptr sub_string_term = dynamic_cast<SubString_ptr>(eq_term->right_term)) {
    if(Minus_ptr minus_term = dynamic_cast<Minus_ptr>(sub_string_term->end_index_term)) {

      if(Len_ptr len_term = dynamic_cast<Len_ptr>(minus_term->left_term)) {
        if(Ast2Dot::isEquivalent(sub_string_term->subject_term,len_term->term)
                && Ast2Dot::isEquivalent(sub_string_term->start_index_term,minus_term->right_term)
                && Term::Type::TERMCONSTANT == eq_term->left_term->type()) {
          // eq_term is just restricting the end of the string variable to be whatever is on the right hand side
          // the end occurs at start_index_term
          if(Plus_ptr plus_term = dynamic_cast<Plus_ptr>(sub_string_term->start_index_term)) {
            if(IndexOf_ptr indexof_term = dynamic_cast<IndexOf_ptr>(plus_term->term_list->at(1))) {
              if(Term::Type::QUALIDENTIFIER == sub_string_term->subject_term->type()
                    && Term::Type::QUALIDENTIFIER == indexof_term->subject_term->type()
                    && Term::Type::TERMCONSTANT == indexof_term->search_term->type()
                    && Term::Type::TERMCONSTANT == indexof_term->from_index->type()) {

                auto plus_first_term = dynamic_cast<TermConstant_ptr>(plus_term->term_list->at(0));
                auto eq_right_term = dynamic_cast<TermConstant_ptr>(eq_term->left_term);
                auto indexof_search_term = dynamic_cast<TermConstant_ptr>(indexof_term->search_term);
                auto indexof_start_term = dynamic_cast<TermConstant_ptr>(indexof_term->from_index);

                if(indexof_start_term->getValue() == "0") {
                  std::string regex = ".*" + indexof_search_term->getValue() + std::string(std::stoi(plus_first_term->getValue())-1,'.') + eq_right_term->getValue();

                  callback_ = [sub_string_term,regex,this](Term_ptr & term) mutable {
                    auto in_term = new In(sub_string_term->subject_term,generate_term_constant(regex,Primitive::Type::REGEX));
                    sub_string_term->subject_term = nullptr;
                    delete term;
                    term = in_term;
                  };
                }

              }
            }
          }

        }
      }
    }
  }

  // EXPERIMENTAL!
//    else if(Term::Type::QUALIDENTIFIER == eq_term->left_term->type() and Term::Type::QUALIDENTIFIER == eq_term->right_term->type()) {
//    auto count_var = symbol_table_->get_count_variable();
//    auto rep_count_var = symbol_table_->get_representative_variable_of_at_scope(symbol_table_->top_scope(),count_var);

//    auto left_var = symbol_table_->get_variable(eq_term->left_term);
//    auto right_var = symbol_table_->get_variable(eq_term->right_term);

//    if(left_var->getType() == Variable::Type::STRING and left_var->getName() == rep_count_var->getName()) {
//      symbol_table_->increment_variable_usage(left_var->getName());
//      symbol_table_->increment_variable_usage(right_var->getName());
//    }
//    else if(right_var->getType() == Variable::Type::STRING and right_var->getName() == rep_count_var->getName()) {
//      symbol_table_->increment_variable_usage(left_var->getName());
//      symbol_table_->increment_variable_usage(right_var->getName());
//    }
//  }
 
 else if(Term::Type::TERMCONSTANT != eq_term->right_term->type() and Term::Type::QUALIDENTIFIER != eq_term->right_term->type()
 								and Term::Type::QUALIDENTIFIER == eq_term->left_term->type()) {
 	auto left_var = symbol_table_->get_variable(eq_term->left_term);
 	symbol_table_->increment_variable_usage(left_var->getName());
 }
 else if(Len_ptr len_term = dynamic_cast<Len_ptr>(eq_term->left_term)) {
   QualIdentifier_ptr qualid_term = dynamic_cast<QualIdentifier_ptr>(len_term->term);
   if(qualid_term != nullptr) {
     auto left_var = symbol_table_->get_variable(qualid_term);
     symbol_table_->increment_variable_usage(left_var->getName());
   }
 }
 else if(Len_ptr len_term = dynamic_cast<Len_ptr>(eq_term->right_term)) {
   QualIdentifier_ptr qualid_term = dynamic_cast<QualIdentifier_ptr>(len_term->term);
   if(qualid_term != nullptr) {
     auto right_var = symbol_table_->get_variable(qualid_term);
     symbol_table_->increment_variable_usage(right_var->getName());
   }
 }
 else if(Term::Type::QUALIDENTIFIER == eq_term->left_term->type()) {
   auto left_var = symbol_table_->get_variable(eq_term->left_term);
   if(left_var->getType() == Variable::Type::STRING) {
     symbol_table_->increment_variable_usage(left_var->getName());
   }
 }
 else if(Term::Type::QUALIDENTIFIER == eq_term->right_term->type()) {
   auto right_var = symbol_table_->get_variable(eq_term->right_term);
   if(right_var->getType() == Variable::Type::STRING) {
     symbol_table_->increment_variable_usage(right_var->getName());
   }
 }

  if (Ast2Dot::isEquivalent(eq_term->left_term, eq_term->right_term)) {
    add_callback_to_replace_with_bool(eq_term, true);
  } else if (check_and_process_len_transformation(eq_term, eq_term->left_term, eq_term->right_term)) {
    if (Ast2Dot::isEquivalent(eq_term->left_term, eq_term->right_term)) {
      add_callback_to_replace_with_bool(eq_term, true);
    } else {
      DVLOG(VLOG_LEVEL) << "Applying 'in' transformation for length: '" << *eq_term << "'";
      callback_ = [this,eq_term](Term_ptr & term) mutable {
//        LOG(INFO) << "+++++++ eq +++++++";
//        Ast2Dot::inspectAST(term);
      	symbol_table_->remove_unsorted_constraint(eq_term);
        if(Term::Type::TERMCONSTANT == eq_term->left_term->type()) {
          term = new In(eq_term->right_term, eq_term->left_term);
        } else {
          term = new In(eq_term->left_term, eq_term->right_term);
        }
        symbol_table_->add_unsorted_constraint(term);
        eq_term->left_term = nullptr;
        eq_term->right_term = nullptr;
        delete eq_term;
//        Ast2Dot::inspectAST(term);
//        std::cin.get();
      };
    }
  } else if (check_and_process_for_contains_transformation(eq_term->left_term, eq_term->right_term, -1)
      or check_and_process_for_contains_transformation(eq_term->right_term, eq_term->left_term, -1)) {
    DVLOG(VLOG_LEVEL) << "Applying 'notContains' transformation (validate behavior): '" << *eq_term << "'";
    callback_ = [eq_term](Term_ptr & term) mutable {
      term = new NotContains(eq_term->left_term, eq_term->right_term);
      eq_term->left_term = nullptr;
      eq_term->right_term = nullptr;
      delete eq_term;
    };
  }

  ss_flag = false;
  DVLOG(VLOG_LEVEL) << "post visit end: " << *eq_term << "@" << eq_term;
}

void SyntacticOptimizer::visitNotEq(NotEq_ptr not_eq_term) {

  if(Ite_ptr ite_term = dynamic_cast<Ite_ptr>(not_eq_term->left_term)) {
    if(Ast2Dot::isEquivalent(ite_term->then_branch,not_eq_term->right_term)) {
      callback_ = [not_eq_term, ite_term](Term_ptr & term) mutable {
//        Ast2Dot::inspectAST(term);
        term = new Not(ite_term->cond);
        ite_term->cond = nullptr;
//        Ast2Dot::inspectAST(term);
//        std::cin.get();
        delete not_eq_term;
      };
      return;
    } else if(Ast2Dot::isEquivalent(ite_term->else_branch,not_eq_term->right_term)) {
      callback_ = [not_eq_term, ite_term](Term_ptr & term) mutable {
//        Ast2Dot::inspectAST(term);
        term = ite_term->cond;
        ite_term->cond = nullptr;
        delete not_eq_term;
//        Ast2Dot::inspectAST(term);
//        std::cin.get();
      };
      return;
    }
  }

  visit_and_callback(not_eq_term->left_term);
  visit_and_callback(not_eq_term->right_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_eq_term << "@" << not_eq_term;
  
  if(Term::Type::QUALIDENTIFIER == not_eq_term->right_term->type() && Term::Type::QUALIDENTIFIER != not_eq_term->left_term->type()) {
    auto temp = not_eq_term->left_term;
    not_eq_term->left_term = not_eq_term->right_term;
    not_eq_term->right_term = temp;
  }
  
  
  bool match_p = match_prefix(not_eq_term->left_term, not_eq_term->right_term);
  if (!match_p) {
    add_callback_to_replace_with_bool(not_eq_term, true);  //there is no constraint on the variable!
    return;
  }
  bool match_s = match_suffix(not_eq_term->left_term, not_eq_term->right_term);
  if (!match_s) {
    add_callback_to_replace_with_bool(not_eq_term, true);
    return;
  }

  visit_and_callback(not_eq_term->left_term);
  visit_and_callback(not_eq_term->right_term);

  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;

  constant_term_checker_left.start(not_eq_term->left_term, Optimization::ConstantTermChecker::Mode::FULL);
  constant_term_checker_right.start(not_eq_term->right_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker_left.is_constant() and constant_term_checker_right.is_constant()) {
    bool result = (constant_term_checker_left.get_constant_as_string() != constant_term_checker_right.get_constant_as_string());
    add_callback_to_replace_with_bool(not_eq_term, result);
    return;
  } else if(constant_term_checker_left.is_constant() and (Term::Type::QUALIDENTIFIER == not_eq_term->right_term->type())) {
    auto var = symbol_table_->get_variable(not_eq_term->right_term);
    std::string constant = constant_term_checker_left.get_constant_as_string();
    if(Variable::Type::BOOL == var->getType() and constant == "true") {
      callback_ = [not_eq_term] (Term_ptr & term) mutable {
        Primitive_ptr primitive = new Primitive("false",Primitive::Type::BOOL);
        TermConstant_ptr term_constant = new TermConstant(primitive);
        term = new Eq(not_eq_term->right_term,term_constant);
        not_eq_term->right_term = nullptr;
        delete not_eq_term;
      };
    } else if(Variable::Type::BOOL == var->getType() and constant == "false") {
      callback_ = [not_eq_term] (Term_ptr & term) mutable {
        Primitive_ptr primitive = new Primitive("true",Primitive::Type::BOOL);
        TermConstant_ptr term_constant = new TermConstant(primitive);
        term = new Eq(not_eq_term->right_term,term_constant);
        not_eq_term->right_term = nullptr;
        delete not_eq_term;
      };
    }
  } else if(constant_term_checker_left.is_constant() and constant_term_checker_left.get_constant_as_string() == "true") {
    callback_ = [not_eq_term] (Term_ptr & term) mutable {
      term = new Not(not_eq_term->right_term);
      not_eq_term->right_term = nullptr;
      delete not_eq_term;
    };
  } else if(constant_term_checker_left.is_constant() and constant_term_checker_left.get_constant_as_string() == "false") {
    callback_ = [not_eq_term] (Term_ptr & term) mutable {
      term = not_eq_term->right_term;
      not_eq_term->right_term = nullptr;
      delete not_eq_term;
    };
  } else if(constant_term_checker_right.is_constant() and (Term::Type::QUALIDENTIFIER == not_eq_term->left_term->type())) {
    auto var = symbol_table_->get_variable(not_eq_term->left_term);
    std::string constant = constant_term_checker_right.get_constant_as_string();
    if(Variable::Type::BOOL == var->getType() and constant == "true") {
      callback_ = [not_eq_term] (Term_ptr & term) mutable {
        Primitive_ptr primitive = new Primitive("false",Primitive::Type::BOOL);
        TermConstant_ptr term_constant = new TermConstant(primitive);
        term = new Eq(not_eq_term->left_term,term_constant);
        not_eq_term->left_term = nullptr;
        delete not_eq_term;
      };
    } else if(Variable::Type::BOOL == var->getType() and constant == "false") {
      callback_ = [not_eq_term] (Term_ptr & term) mutable {
        Primitive_ptr primitive = new Primitive("true",Primitive::Type::BOOL);
        TermConstant_ptr term_constant = new TermConstant(primitive);
        term = new Eq(not_eq_term->left_term,term_constant);
        not_eq_term->left_term = nullptr;
        delete not_eq_term;
      };
    }
  } else if(constant_term_checker_right.is_constant() and constant_term_checker_right.get_constant_as_string() == "true") {
    callback_ = [not_eq_term] (Term_ptr & term) mutable {
      term = new Not(not_eq_term->left_term);
      not_eq_term->left_term = nullptr;
      delete not_eq_term;
    };
  } else if(constant_term_checker_right.is_constant() and constant_term_checker_right.get_constant_as_string() == "false") {
    callback_ = [not_eq_term] (Term_ptr & term) mutable {
      term = not_eq_term->left_term;
      not_eq_term->left_term = nullptr;
      delete not_eq_term;
    };
  }

  if(not_eq_term->left_term->type() == Term::Type::DIV and not_eq_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr left_div_term = dynamic_cast<Div_ptr>(not_eq_term->left_term);
    Div_ptr right_div_term = dynamic_cast<Div_ptr>(not_eq_term->left_term);
    if(left_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == left_div_term->term_list->at(1)->type()
          and right_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == right_div_term->term_list->at(1)->type()) {
      callback_ = [not_eq_term](Term_ptr & term) mutable {
        Div_ptr left_div_term = dynamic_cast<Div_ptr>(not_eq_term->left_term);
        Div_ptr right_div_term = dynamic_cast<Div_ptr>(not_eq_term->right_term);

        TermList_ptr left_times_list = new TermList();
        left_times_list->push_back(right_div_term->term_list->at(1)->clone());
        left_times_list->push_back(left_div_term->term_list->at(0)->clone());
        
        TermList_ptr right_times_list = new TermList();
        right_times_list->push_back(left_div_term->term_list->at(1)->clone());
        right_times_list->push_back(right_div_term->term_list->at(0)->clone());

        term = new NotEq(new Times(left_times_list), new Times(right_times_list));
        delete not_eq_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(not_eq_term->left_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr div_term = dynamic_cast<Div_ptr>(not_eq_term->left_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [not_eq_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(not_eq_term->left_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(not_eq_term->right_term->clone());
        Times_ptr times_term = new Times(times_list);
        term = new NotEq(div_term->term_list->at(0)->clone(),times_term);
        delete not_eq_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(not_eq_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr div_term = dynamic_cast<Div_ptr>(not_eq_term->right_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [not_eq_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(not_eq_term->right_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(not_eq_term->left_term->clone());
        Times_ptr times_term = new Times(times_list);
        term = new NotEq(times_term,div_term->term_list->at(0)->clone());
        delete not_eq_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  }

  // check for equality with concat where prefix var is same on both sides
  if(Term::Type::QUALIDENTIFIER == not_eq_term->left_term->type() && Term::Type::CONCAT == not_eq_term->right_term->type()) {
    Concat_ptr concat_term = dynamic_cast<Concat_ptr>(not_eq_term->right_term);
    if(Term::Type::QUALIDENTIFIER == concat_term->term_list->at(0)->type()) {
      QualIdentifier_ptr left_var = dynamic_cast<QualIdentifier_ptr>(not_eq_term->left_term);
      QualIdentifier_ptr right_var = dynamic_cast<QualIdentifier_ptr>(concat_term->term_list->at(0));
      // if same variable, replace term
      if(left_var->getVarName() == right_var->getVarName()) {
        callback_ = [this, not_eq_term](Term_ptr & term) mutable {
          Concat_ptr concat_term = dynamic_cast<Concat_ptr>(not_eq_term->right_term);
          delete not_eq_term->left_term;
          not_eq_term->left_term = generate_term_constant("",Primitive::Type::STRING);
          delete concat_term->term_list->at(0);
          concat_term->term_list->at(0) = nullptr;
          concat_term->term_list->erase(concat_term->term_list->begin());
        };
        return;
      }
    }
  } else if(Term::Type::QUALIDENTIFIER == not_eq_term->right_term->type() && Term::Type::CONCAT == not_eq_term->left_term->type()) {
    Concat_ptr concat_term = dynamic_cast<Concat_ptr>(not_eq_term->left_term);
    if(Term::Type::QUALIDENTIFIER == concat_term->term_list->at(0)->type()) {
      QualIdentifier_ptr right_var = dynamic_cast<QualIdentifier_ptr>(not_eq_term->right_term);
      QualIdentifier_ptr left_var = dynamic_cast<QualIdentifier_ptr>(concat_term->term_list->at(0));
      // if same variable, replace term
      if(left_var->getVarName() == right_var->getVarName()) {
        callback_ = [this, not_eq_term](Term_ptr & term) mutable {
          Concat_ptr concat_term = dynamic_cast<Concat_ptr>(not_eq_term->left_term);
          delete not_eq_term->right_term;
          not_eq_term->right_term = generate_term_constant("",Primitive::Type::STRING);
          delete concat_term->term_list->at(0);
          concat_term->term_list->at(0) = nullptr;
          concat_term->term_list->erase(concat_term->term_list->begin());
        };
      }
      return;
    }
  }
  else if (IndexOf_ptr indexof_term = dynamic_cast<IndexOf_ptr>(not_eq_term->left_term)) {
    if(Term::Type::QUALIDENTIFIER == indexof_term->subject_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->search_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->from_index->type()
          && Term::Type::TERMCONSTANT == not_eq_term->right_term->type()) {
      auto subject_term = dynamic_cast<QualIdentifier_ptr>(indexof_term->subject_term);
      auto search_term = dynamic_cast<TermConstant_ptr>(indexof_term->search_term);
      auto from_index = dynamic_cast<TermConstant_ptr>(indexof_term->from_index);
      auto right_constant = dynamic_cast<TermConstant_ptr>(not_eq_term->right_term);

      if(from_index->getValue() == "0") {
        if(right_constant->getValue() == "-1") {
          callback_ = [not_eq_term, indexof_term](Term_ptr & term) mutable {
            auto contains = new Contains(indexof_term->subject_term, indexof_term->search_term);
            indexof_term->subject_term = nullptr;
            indexof_term->search_term = nullptr;
            delete term;
            term = contains;
          };
        } else if(right_constant->getValue() == "-1") {
          callback_ = [not_eq_term, indexof_term](Term_ptr & term) mutable {
            auto contains = new NotContains(indexof_term->subject_term, indexof_term->search_term);
            indexof_term->subject_term = nullptr;
            indexof_term->search_term = nullptr;
            delete term;
            term = contains;
          };
        }
      }
    }
  }
  else if(CharAt_ptr charat_term = dynamic_cast<CharAt_ptr>(not_eq_term->left_term)) {
    if(Minus_ptr minus_term = dynamic_cast<Minus_ptr>(charat_term->index_term)) {
      if(Len_ptr len_term = dynamic_cast<Len_ptr>(minus_term->left_term)) {

        if(Term::Type::QUALIDENTIFIER == charat_term->subject_term->type()
              && Ast2Dot::isEquivalent(charat_term->subject_term,len_term->term)
              && Term::Type::TERMCONSTANT == minus_term->right_term->type()
              && Term::Type::TERMCONSTANT == not_eq_term->right_term->type()) {

          auto minus_right_term = dynamic_cast<TermConstant_ptr>(minus_term->right_term);
          auto right_constant = dynamic_cast<TermConstant_ptr>(not_eq_term->right_term);
          auto qi_term = dynamic_cast<QualIdentifier_ptr>(len_term->term);

//          LOG(INFO) << minus_right_term->getValue();
//          LOG(INFO) << right_constant->getValue();
//          LOG(FATAL) << "Yep";
          if(std::stoi(minus_right_term->getValue()) == right_constant->getValue().length()) {
            callback_ = [not_eq_term,qi_term,right_constant](Term_ptr & term) mutable {
//              Ast2Dot::inspectAST(term);
              auto not_ends_term = new NotEnds(qi_term->clone(),right_constant->clone());
              delete not_eq_term;
              term = not_ends_term;
//              Ast2Dot::inspectAST(term);
//              std::cin.get();
            };
          }
        }
      }
    }
  }

  if(Term::Type::QUALIDENTIFIER == not_eq_term->left_term->type()) {
		auto left_var = symbol_table_->get_variable(not_eq_term->left_term);
		if(left_var->getType() == Variable::Type::STRING) {
			symbol_table_->increment_variable_usage(left_var->getName());
		}
	}
  if(Term::Type::QUALIDENTIFIER == not_eq_term->right_term->type()) {
		auto right_var = symbol_table_->get_variable(not_eq_term->right_term);
		if(right_var->getType() == Variable::Type::STRING) {
			symbol_table_->increment_variable_usage(right_var->getName());
		}
	}


  if (Ast2Dot::isEquivalent(not_eq_term->left_term, not_eq_term->right_term)) {
    add_callback_to_replace_with_bool(not_eq_term, false);
  } else if (check_and_process_len_transformation(not_eq_term, not_eq_term->left_term, not_eq_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *not_eq_term << "'";
    if (Ast2Dot::isEquivalent(not_eq_term->left_term, not_eq_term->right_term)) {
      add_callback_to_replace_with_bool(not_eq_term, false);
    } else {
      DVLOG(VLOG_LEVEL) << "Applying notIn transformation for length: '" << *not_eq_term << "'";
      callback_ = [not_eq_term](Term_ptr & term) mutable {
//        LOG(INFO) << " ====== noteq ====== ";
//        Ast2Dot::inspectAST(term);
        term = new NotIn(not_eq_term->left_term, not_eq_term->right_term);
        not_eq_term->left_term = nullptr;
        not_eq_term->right_term = nullptr;
        delete not_eq_term;
//        Ast2Dot::inspectAST(term);
//        std::cin.get();
      };
    }
  } else if (check_and_process_for_contains_transformation(not_eq_term->left_term, not_eq_term->right_term, -1)
      or check_and_process_for_contains_transformation(not_eq_term->right_term, not_eq_term->left_term, -1)) {
    DVLOG(VLOG_LEVEL) << "Applying Contains transformation: '" << *not_eq_term << "'";
    callback_ = [not_eq_term](Term_ptr & term) mutable {
      term = new Contains(not_eq_term->left_term, not_eq_term->right_term);
      not_eq_term->left_term = nullptr;
      not_eq_term->right_term = nullptr;
      delete not_eq_term;
    };
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_eq_term << "@" << not_eq_term;
}

void SyntacticOptimizer::visitGt(Gt_ptr gt_term) {
  visit_and_callback(gt_term->left_term);
  visit_and_callback(gt_term->right_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *gt_term << "@" << gt_term;

  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;

  constant_term_checker_left.start(gt_term->left_term, Optimization::ConstantTermChecker::Mode::FULL);
  constant_term_checker_right.start(gt_term->right_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker_left.is_constant_int() && constant_term_checker_right.is_constant_int()) {
    bool result = (constant_term_checker_left.get_constant_int() > constant_term_checker_right.get_constant_int());
    add_callback_to_replace_with_bool(gt_term, result);
    return;
  }

  if(gt_term->left_term->type() == Term::Type::DIV and gt_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr left_div_term = dynamic_cast<Div_ptr>(gt_term->left_term);
    Div_ptr right_div_term = dynamic_cast<Div_ptr>(gt_term->left_term);
    if(left_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == left_div_term->term_list->at(1)->type()
          and right_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == right_div_term->term_list->at(1)->type()) {
      callback_ = [gt_term](Term_ptr & term) mutable {
        Div_ptr left_div_term = dynamic_cast<Div_ptr>(gt_term->left_term);
        Div_ptr right_div_term = dynamic_cast<Div_ptr>(gt_term->right_term);

        TermList_ptr left_times_list = new TermList();
        left_times_list->push_back(right_div_term->term_list->at(1)->clone());
        left_times_list->push_back(left_div_term->term_list->at(0)->clone());
        
        TermList_ptr right_times_list = new TermList();
        right_times_list->push_back(left_div_term->term_list->at(1)->clone());
        right_times_list->push_back(right_div_term->term_list->at(0)->clone());

        term = new Gt(new Times(left_times_list), new Times(right_times_list));
        delete gt_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(gt_term->left_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(gt_term->left_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [gt_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(gt_term->left_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(gt_term->right_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "1";
          term = new Lt(div_term->term_list->at(0)->clone(),times_term);
        } else {
          term = new Gt(div_term->term_list->at(0)->clone(),times_term);
        }
        delete gt_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(gt_term->right_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(gt_term->right_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [gt_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(gt_term->right_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(gt_term->left_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "2";
          term = new Lt(times_term, div_term->term_list->at(0)->clone());
        } else {
          term = new Gt(times_term, div_term->term_list->at(0)->clone());
        }
        delete gt_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  }

  if (Ast2Dot::isEquivalent(gt_term->left_term, gt_term->right_term)) {
    add_callback_to_replace_with_bool(gt_term, false);
  } else if (check_and_process_len_transformation(gt_term, gt_term->left_term, gt_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *gt_term << "'";
    if (Ast2Dot::isEquivalent(gt_term->left_term, gt_term->right_term)) {
      add_callback_to_replace_with_bool(gt_term, false);
    } else {
      callback_ = [gt_term](Term_ptr & term) mutable {
        if(Term::Type::TERMCONSTANT == gt_term->right_term->type()) {
          term = new In(gt_term->left_term, gt_term->right_term);
        } else {
          term = new In(gt_term->right_term, gt_term->left_term);
        }
        gt_term->left_term = nullptr;
        gt_term->right_term = nullptr;
        delete gt_term;
      };
    }
  } else if (check_and_process_for_contains_transformation(gt_term->left_term, gt_term->right_term, -1)
      or check_and_process_for_contains_transformation(gt_term->right_term, gt_term->left_term, -1)) {
    DVLOG(VLOG_LEVEL) << "Applying 'contains' transformation: '" << *gt_term << "'";
    callback_ = [gt_term](Term_ptr & term) mutable {
      term = new Contains(gt_term->left_term, gt_term->right_term);
      gt_term->left_term = nullptr;
      gt_term->right_term = nullptr;
      delete gt_term;
    };
  } else if (IndexOf_ptr indexof_term = dynamic_cast<IndexOf_ptr>(gt_term->left_term)) {
    if(Term::Type::QUALIDENTIFIER == indexof_term->subject_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->search_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->from_index->type()
          && Term::Type::TERMCONSTANT == gt_term->right_term->type()) {
      auto subject_term = dynamic_cast<QualIdentifier_ptr>(indexof_term->subject_term);
      auto search_term = dynamic_cast<TermConstant_ptr>(indexof_term->search_term);
      auto from_index = dynamic_cast<TermConstant_ptr>(indexof_term->from_index);
      auto right_constant = dynamic_cast<TermConstant_ptr>(gt_term->right_term);

      if(right_constant->getValue() == "0") {
        std::string not_char = "(.&~(" + search_term->getValue() + "))";
        std::string regex = std::string(std::stoi(from_index->getValue()),'.') + not_char + ".*" + search_term->getValue() + ".*";
        callback_ = [gt_term, indexof_term, regex, this](Term_ptr & term) mutable {
//          Ast2Dot::inspectAST(term);
          auto contains = new In(indexof_term->subject_term, generate_term_constant(regex,Primitive::Type::REGEX));
          indexof_term->subject_term = nullptr;
//          indexof_term->search_term = nullptr;
          delete term;
          term = contains;
//          Ast2Dot::inspectAST(term);
//          std::cin.get();
        };
      }
    }
//    else
//    if(Len_ptr len_term = dynamic_cast<Len_ptr>(gt_term->right_term)) {
//      if(Ast2Dot::isEquivalent(indexof_term->subject_term,len_term->term)) {
//        add_callback_to_replace_with_bool(gt_term,false);
//      }
//    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *gt_term << "@" << gt_term;
}

void SyntacticOptimizer::visitGe(Ge_ptr ge_term) {
  visit_and_callback(ge_term->left_term);
  visit_and_callback(ge_term->right_term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *ge_term << "@" << ge_term;

  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;

  constant_term_checker_left.start(ge_term->left_term, Optimization::ConstantTermChecker::Mode::FULL);
  constant_term_checker_right.start(ge_term->right_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker_left.is_constant_int() && constant_term_checker_right.is_constant_int()) {
    bool result = (constant_term_checker_left.get_constant_int() >= constant_term_checker_right.get_constant_int());
    add_callback_to_replace_with_bool(ge_term, result);
    return;
  }

  if(ge_term->left_term->type() == Term::Type::DIV and ge_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr left_div_term = dynamic_cast<Div_ptr>(ge_term->left_term);
    Div_ptr right_div_term = dynamic_cast<Div_ptr>(ge_term->left_term);
    if(left_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == left_div_term->term_list->at(1)->type()
          and right_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == right_div_term->term_list->at(1)->type()) {
      callback_ = [ge_term](Term_ptr & term) mutable {
        Div_ptr left_div_term = dynamic_cast<Div_ptr>(ge_term->left_term);
        Div_ptr right_div_term = dynamic_cast<Div_ptr>(ge_term->right_term);

        TermList_ptr left_times_list = new TermList();
        left_times_list->push_back(right_div_term->term_list->at(1)->clone());
        left_times_list->push_back(left_div_term->term_list->at(0)->clone());
        
        TermList_ptr right_times_list = new TermList();
        right_times_list->push_back(left_div_term->term_list->at(1)->clone());
        right_times_list->push_back(right_div_term->term_list->at(0)->clone());

        term = new Ge(new Times(left_times_list), new Times(right_times_list));
        delete ge_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(ge_term->left_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(ge_term->left_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [ge_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(ge_term->left_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(ge_term->right_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "3";
          term = new Le(div_term->term_list->at(0)->clone(),times_term);
        } else {
          term = new Ge(div_term->term_list->at(0)->clone(),times_term);
        }
        delete ge_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(ge_term->right_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(ge_term->right_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [ge_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(ge_term->right_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(ge_term->left_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "4";
          term = new Le(times_term, div_term->term_list->at(0)->clone());
        } else {
          term = new Ge(times_term, div_term->term_list->at(0)->clone());
        }
        delete ge_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  }

  if (Ast2Dot::isEquivalent(ge_term->left_term, ge_term->right_term)) {
    add_callback_to_replace_with_bool(ge_term, true);
  } else if (check_and_process_len_transformation(ge_term, ge_term->left_term, ge_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *ge_term << "'";
    if (Ast2Dot::isEquivalent(ge_term->left_term, ge_term->right_term)) {
      add_callback_to_replace_with_bool(ge_term, true);
    } else {
      callback_ = [ge_term](Term_ptr & term) mutable {
        if(Term::Type::TERMCONSTANT == ge_term->right_term->type()) {
          term = new In(ge_term->left_term, ge_term->right_term);
        } else {
          term = new In(ge_term->right_term, ge_term->left_term);
        }
        ge_term->left_term = nullptr;
        ge_term->right_term = nullptr;
        delete ge_term;
      };
    }
  } else if (check_and_process_for_contains_transformation(ge_term->left_term, ge_term->right_term, 0)
      or check_and_process_for_contains_transformation(ge_term->right_term, ge_term->left_term, 0)) {
    DVLOG(VLOG_LEVEL) << "Applying 'contains' transformation: '" << *ge_term << "'";
    callback_ = [ge_term](Term_ptr & term) mutable {
      term = new Contains(ge_term->left_term, ge_term->right_term);
      ge_term->left_term = nullptr;
      ge_term->right_term = nullptr;
      delete ge_term;
    };
  } 
  else if (IndexOf_ptr indexof_term = dynamic_cast<IndexOf_ptr>(ge_term->left_term)) {
    if(Term::Type::QUALIDENTIFIER == indexof_term->subject_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->search_term->type()
          && Term::Type::TERMCONSTANT == indexof_term->from_index->type()
          && Term::Type::TERMCONSTANT == ge_term->right_term->type()) {
      auto subject_term = dynamic_cast<QualIdentifier_ptr>(indexof_term->subject_term);
      auto search_term = dynamic_cast<TermConstant_ptr>(indexof_term->search_term);
      auto from_index = dynamic_cast<TermConstant_ptr>(indexof_term->from_index);
      auto right_constant = dynamic_cast<TermConstant_ptr>(ge_term->right_term);

      if(right_constant->getValue() == "0") {
        std::string regex = std::string(std::stoi(from_index->getValue()),'.') + ".*" + search_term->getValue() + ".*";
        callback_ = [ge_term, indexof_term, regex, this](Term_ptr & term) mutable {
          auto contains = new In(indexof_term->subject_term, generate_term_constant(regex,Primitive::Type::REGEX));
          indexof_term->subject_term = nullptr;
//          indexof_term->search_term = nullptr;
          delete term;
          term = contains;
        };
      }
    } else
    if(Len_ptr len_term = dynamic_cast<Len_ptr>(ge_term->right_term)) {
      if(Ast2Dot::isEquivalent(indexof_term->subject_term,len_term->term)) {
        add_callback_to_replace_with_bool(ge_term,false);
      }
    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *ge_term << "@" << ge_term;
}

void SyntacticOptimizer::visitLt(Lt_ptr lt_term) {
  visit_and_callback(lt_term->left_term);
  visit_and_callback(lt_term->right_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *lt_term << "@" << lt_term;

  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;

  constant_term_checker_left.start(lt_term->left_term, Optimization::ConstantTermChecker::Mode::FULL);
  constant_term_checker_right.start(lt_term->right_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker_left.is_constant_int() && constant_term_checker_right.is_constant_int()) {
    bool result = (constant_term_checker_left.get_constant_int() < constant_term_checker_right.get_constant_int());
    add_callback_to_replace_with_bool(lt_term, result);
    return;
  }

  if(lt_term->left_term->type() == Term::Type::DIV and lt_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr left_div_term = dynamic_cast<Div_ptr>(lt_term->left_term);
    Div_ptr right_div_term = dynamic_cast<Div_ptr>(lt_term->left_term);
    if(left_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == left_div_term->term_list->at(1)->type()
          and right_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == right_div_term->term_list->at(1)->type()) {
      callback_ = [lt_term](Term_ptr & term) mutable {
        Div_ptr left_div_term = dynamic_cast<Div_ptr>(lt_term->left_term);
        Div_ptr right_div_term = dynamic_cast<Div_ptr>(lt_term->right_term);

        TermList_ptr left_times_list = new TermList();
        left_times_list->push_back(right_div_term->term_list->at(1)->clone());
        left_times_list->push_back(left_div_term->term_list->at(0)->clone());
        
        TermList_ptr right_times_list = new TermList();
        right_times_list->push_back(left_div_term->term_list->at(1)->clone());
        right_times_list->push_back(right_div_term->term_list->at(0)->clone());

        term = new Lt(new Times(left_times_list), new Times(right_times_list));
        delete lt_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(lt_term->left_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(lt_term->left_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [lt_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(lt_term->left_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(lt_term->right_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "5";
          term = new Gt(div_term->term_list->at(0)->clone(),times_term);
        } else {
          term = new Lt(div_term->term_list->at(0)->clone(),times_term);
        }
        delete lt_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(lt_term->right_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(lt_term->right_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [lt_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(lt_term->right_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(lt_term->left_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "6";
          term = new Gt(times_term, div_term->term_list->at(0)->clone());
        } else {
          term = new Lt(times_term, div_term->term_list->at(0)->clone());
        }
        delete lt_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  }

  if (Ast2Dot::isEquivalent(lt_term->left_term, lt_term->right_term)) {
    add_callback_to_replace_with_bool(lt_term, false);
  } else if (check_and_process_len_transformation(lt_term, lt_term->left_term, lt_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *lt_term << "'";
    if (Ast2Dot::isEquivalent(lt_term->left_term, lt_term->right_term)) {
      add_callback_to_replace_with_bool(lt_term, false);
    } else {
      callback_ = [lt_term](Term_ptr & term) mutable {
        if(Term::Type::TERMCONSTANT == lt_term->right_term->type()) {
          term = new In(lt_term->left_term, lt_term->right_term);
        } else {
          term = new In(lt_term->right_term, lt_term->left_term);
        }
        lt_term->left_term = nullptr;
        lt_term->right_term = nullptr;
        delete lt_term;
      };
    }
  } else if (check_and_process_for_contains_transformation(lt_term->left_term, lt_term->right_term, 0)
      or check_and_process_for_contains_transformation(lt_term->right_term, lt_term->left_term, 0)) {
    DVLOG(VLOG_LEVEL) << "Applying notContains transformation: '" << *lt_term << "'";
    callback_ = [lt_term](Term_ptr & term) mutable {
      term = new NotContains(lt_term->left_term, lt_term->right_term);
      lt_term->left_term = nullptr;
      lt_term->right_term = nullptr;
      delete lt_term;
    };
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *lt_term << "@" << lt_term;
}

void SyntacticOptimizer::visitLe(Le_ptr le_term) {
  visit_and_callback(le_term->left_term);
  visit_and_callback(le_term->right_term);


  DVLOG(VLOG_LEVEL) << "post visit start: " << *le_term << "@" << le_term;

  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;

  constant_term_checker_left.start(le_term->left_term, Optimization::ConstantTermChecker::Mode::FULL);
  constant_term_checker_right.start(le_term->right_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker_left.is_constant_int() && constant_term_checker_right.is_constant_int()) {
    bool result = (constant_term_checker_left.get_constant_int() <= constant_term_checker_right.get_constant_int());
    add_callback_to_replace_with_bool(le_term, result);
    return;
  }
  
  if(le_term->left_term->type() == Term::Type::DIV and le_term->right_term->type() == Term::Type::DIV) {
    LOG(FATAL) << "IMPLEMENT ME";
    Div_ptr left_div_term = dynamic_cast<Div_ptr>(le_term->left_term);
    Div_ptr right_div_term = dynamic_cast<Div_ptr>(le_term->left_term);
    if(left_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == left_div_term->term_list->at(1)->type()
          and right_div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == right_div_term->term_list->at(1)->type()) {
      callback_ = [le_term](Term_ptr & term) mutable {
        Div_ptr left_div_term = dynamic_cast<Div_ptr>(le_term->left_term);
        Div_ptr right_div_term = dynamic_cast<Div_ptr>(le_term->right_term);

        TermList_ptr left_times_list = new TermList();
        left_times_list->push_back(right_div_term->term_list->at(1)->clone());
        left_times_list->push_back(left_div_term->term_list->at(0)->clone());
        
        TermList_ptr right_times_list = new TermList();
        right_times_list->push_back(left_div_term->term_list->at(1)->clone());
        right_times_list->push_back(right_div_term->term_list->at(0)->clone());

        term = new Le(new Times(left_times_list), new Times(right_times_list));
        delete le_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(le_term->left_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(le_term->left_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [le_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(le_term->left_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(le_term->right_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "7";
          term = new Ge(div_term->term_list->at(0)->clone(),times_term);
        } else {
          term = new Le(div_term->term_list->at(0)->clone(),times_term);
        }
        delete le_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  } else if(le_term->right_term->type() == Term::Type::DIV) {
    Div_ptr div_term = dynamic_cast<Div_ptr>(le_term->right_term);
    if(div_term->term_list->size() == 2 && Term::Type::TERMCONSTANT == div_term->term_list->at(1)->type()) {
      callback_ = [le_term](Term_ptr & term) mutable {
        Div_ptr div_term = dynamic_cast<Div_ptr>(le_term->right_term);
        TermList_ptr times_list = new TermList();
        times_list->push_back(div_term->term_list->at(1)->clone());
        times_list->push_back(le_term->left_term->clone());
        Times_ptr times_term = new Times(times_list);
        TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(div_term->term_list->at(1));
        int num = std::stoi(term_constant->getValue());
        // if negative, flip inequality
        if(num < 0) {
          LOG(FATAL) << "8";
          term = new Ge(times_term, div_term->term_list->at(0)->clone());
        } else {
          term = new Le(times_term, div_term->term_list->at(0)->clone());
        }
        delete le_term;
      };
      return;
    }
    LOG(FATAL) << "Operation not supported";
  }

  if (Ast2Dot::isEquivalent(le_term->left_term, le_term->right_term)) {
    add_callback_to_replace_with_bool(le_term, true);
  } else if (check_and_process_len_transformation(le_term, le_term->left_term, le_term->right_term)) {
    DVLOG(VLOG_LEVEL) << "Applying len transformation: '" << *le_term << "'";
    if (Ast2Dot::isEquivalent(le_term->left_term, le_term->right_term)) {
      add_callback_to_replace_with_bool(le_term, true);
    } else {
      callback_ = [le_term](Term_ptr & term) mutable {
        if(Term::Type::TERMCONSTANT == le_term->right_term->type()) {
          term = new In(le_term->left_term, le_term->right_term);
        } else {
          term = new In(le_term->right_term, le_term->left_term);
        }
        le_term->left_term = nullptr;
        le_term->right_term = nullptr;
        delete le_term;
      };
    }
  } else if (check_and_process_for_contains_transformation(le_term->left_term, le_term->right_term, -1)
      or check_and_process_for_contains_transformation(le_term->right_term, le_term->left_term, -1)) {
    DVLOG(VLOG_LEVEL) << "Applying notContains transformation: '" << *le_term << "'";
    callback_ = [le_term](Term_ptr & term) mutable {
      term = new NotContains(le_term->left_term, le_term->right_term);
      le_term->left_term = nullptr;
      le_term->right_term = nullptr;
      delete le_term;
    };
  }

  DVLOG(VLOG_LEVEL) << "post visit end: " << *le_term << "@" << le_term;
}

void SyntacticOptimizer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : *(concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *concat_term << "@" << concat_term;
  TermConstant_ptr initial_term_constant = nullptr;
  Optimization::ConstantTermChecker string_constant_checker;
  int pos = 0;
  for (auto iter = concat_term->term_list->begin(); iter != concat_term->term_list->end();) {
    if (Term::Type::CONCAT == (*iter)->type()) {
      Concat_ptr sub_concat_term = dynamic_cast<Concat_ptr>(*iter);
      concat_term->term_list->erase(iter);
      concat_term->term_list->insert(iter, sub_concat_term->term_list->begin(), sub_concat_term->term_list->end());
      sub_concat_term->term_list->clear();
      delete sub_concat_term;
      iter = concat_term->term_list->begin() + pos;  // insertion invalidates iter, reset it
      continue;
    } else if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter)) {
      if (term_constant->getValue() == "") {
        delete term_constant;  // deallocate
        // *iter = nullptr;
        concat_term->term_list->erase(iter);
        continue;  // iterator updated by erase
      } else {
      	if (initial_term_constant == nullptr) {
      		initial_term_constant = term_constant;
				} else {
					append_constant(initial_term_constant, term_constant);
					delete term_constant;  // deallocate
					concat_term->term_list->erase(iter);
					continue;  // iterator updated by erase
				}
      }
    } else {
      if (initial_term_constant) {  // if there is a constant regex makes it string
        string_constant_checker.start(initial_term_constant);
        if (string_constant_checker.is_constant_string()) {
          initial_term_constant->primitive->setData(string_constant_checker.get_constant_string());
          initial_term_constant->primitive->setType(Primitive::Type::STRING);
        }
      }
      initial_term_constant = nullptr;
    }
    iter++;
    pos++;
  }

  if (concat_term->term_list->size() == 1) {
    callback_ = [concat_term] (Term_ptr & term) mutable {
      term = concat_term->term_list->front();
      concat_term->term_list->clear();
      delete concat_term;
    };
  } else if(concat_term->term_list->size() == 0) {
    callback_ = [this,concat_term] (Term_ptr & term) mutable {
      term = generate_term_constant("",Primitive::Type::STRING);
      concat_term->term_list->clear();
      delete concat_term;
    };
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *concat_term << "@" << concat_term;
}

void SyntacticOptimizer::visitIn(In_ptr in_term) {
  visit_and_callback(in_term->left_term);
  visit_and_callback(in_term->right_term);
  
  DVLOG(VLOG_LEVEL) << "post visit start: " << *in_term << "@" << in_term;
  
  if(ToRegex_ptr to_regex_term = dynamic_cast<ToRegex_ptr>(in_term->right_term)) {
    if(Term::Type::CONCAT == to_regex_term->term->type()) {
      callback_ = [to_regex_term, in_term](Term_ptr & term) {
        Eq_ptr eq_term = new Eq(in_term->left_term, to_regex_term->term);
        to_regex_term->term = nullptr;
        delete to_regex_term;
        in_term->left_term = nullptr;
        in_term->right_term = nullptr;
        delete in_term;
        term = eq_term;
      };
      DVLOG(VLOG_LEVEL) << "post visit end: " << *in_term << "@" << in_term;
      return;
    }
  }
  
  if (Ast2Dot::isEquivalent(in_term->left_term, in_term->right_term)) {
    add_callback_to_replace_with_bool(in_term, true);
  // } else if (check_and_process_constant_string( { in_term->left_term, in_term->right_term })) {
  // 	callback_ = [in_term] (Term_ptr & term) mutable {
  //     term = new Eq(in_term->left_term, in_term->right_term);
  //     in_term->left_term = nullptr; in_term->right_term = nullptr;
  //     delete in_term;
  //   };
  } else if (Term::Type::TERMCONSTANT != in_term->left_term->type() and Term::Type::TERMCONSTANT == in_term->right_term->type()) {
    // optimize when regular expression is the empty language (return false)
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(in_term->right_term);
    if(Primitive::Type::REGEX == term_constant->getValueType()) {
      Util::RegularExpression_ptr regex = new Util::RegularExpression(term_constant->getValue());
      if(regex->type() == Util::RegularExpression::Type::EMPTY) {
        add_callback_to_replace_with_bool(in_term, false);
      }
    }
  } else if (Term::Type::TERMCONSTANT != in_term->right_term->type() and Term::Type::TERMCONSTANT == in_term->left_term->type()) {
    // optimize when regular expression is the empty language (return false)
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(in_term->left_term);
    if(Primitive::Type::REGEX == term_constant->getValueType()) {
      Util::RegularExpression_ptr regex = new Util::RegularExpression(term_constant->getValue());
      if(regex->type() == Util::RegularExpression::Type::EMPTY) {
        add_callback_to_replace_with_bool(in_term, false);
      }
    }
  } 
  DVLOG(VLOG_LEVEL) << "post visit end: " << *in_term << "@" << in_term;
}

void SyntacticOptimizer::visitNotIn(NotIn_ptr not_in_term) {
  visit_and_callback(not_in_term->left_term);
  visit_and_callback(not_in_term->right_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_in_term << "@" << not_in_term;

  if(ToRegex_ptr to_regex_term = dynamic_cast<ToRegex_ptr>(not_in_term->right_term)) {
    if(Term::Type::CONCAT == to_regex_term->term->type()) {
      callback_ = [to_regex_term, not_in_term](Term_ptr & term) {
        NotEq_ptr not_eq_term = new NotEq(not_in_term->left_term, to_regex_term->term);
        to_regex_term->term = nullptr;
        delete to_regex_term;
        not_in_term->left_term = nullptr;
        not_in_term->right_term = nullptr;
        delete not_in_term;
        term = not_eq_term;
      };
      DVLOG(VLOG_LEVEL) << "post visit end: " << *not_in_term << "@" << not_in_term;
      return;
    }
  }

  if (Ast2Dot::isEquivalent(not_in_term->left_term, not_in_term->right_term)) {
    add_callback_to_replace_with_bool(not_in_term, false);
  // } else if (check_and_process_constant_string( { not_in_term->left_term, not_in_term->right_term })) {
  //   callback_ = [not_in_term] (Term_ptr & term) mutable {
  //     term = new NotEq(not_in_term->left_term, not_in_term->right_term);
  //     not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;
  //     delete not_in_term;
  //   };
  } else if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(not_in_term->right_term)) {
    if (Primitive::Type::REGEX == term_constant->getValueType()) {
      std::string data = term_constant->getValue();
      if (data.find("~") == 0) {
        data = data.substr(1);
      } else {
        data = "~(" + data + ")";
      }
      term_constant->primitive->setData(data);
      callback_ = [not_in_term](Term_ptr & term) mutable {
        term = new In(not_in_term->left_term, not_in_term->right_term);
        not_in_term->left_term = nullptr; not_in_term->right_term = nullptr;
        delete not_in_term;
      };
    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_in_term << "@" << not_in_term;
}

void SyntacticOptimizer::visitLen(Len_ptr len_term) {
  visit_and_callback(len_term->term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *len_term << "@" << len_term;

  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(len_term->term)) {
    if (Primitive::Type::STRING == term_constant->getValueType()) {
      DVLOG(VLOG_LEVEL) << "computing 'len' for string constant";
      std::string value = term_constant->getValue();
      int len = value.length();
      std::string str_len = std::to_string(len);
      callback_ = [this, len_term, str_len](Term_ptr & term) mutable {
        term = generate_term_constant(str_len, Primitive::Type::NUMERAL);
        delete len_term;
      };
    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *len_term << "@" << len_term;
}

void SyntacticOptimizer::visitContains(Contains_ptr contains_term) {
  visit_and_callback(contains_term->subject_term);
  visit_and_callback(contains_term->search_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *contains_term << "@" << contains_term;

  Optimization::ConstantTermChecker constant_term_checker;
  Optimization::ConstantTermChecker constant_term_checker_subject;

  constant_term_checker.start(contains_term->search_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker.is_constant_string()) {
    std::string search_ = constant_term_checker.get_constant_string();
    constant_term_checker_subject.start(contains_term->subject_term, Optimization::ConstantTermChecker::Mode::FULL);
    //If they are both constants, we can check the contains directly
    if (constant_term_checker_subject.is_constant_string()) {
      std::string subject_ = constant_term_checker_subject.get_constant_string();
      if (subject_.find(search_) != std::string::npos) {
        add_callback_to_replace_with_bool(contains_term, true);
      } else {
        add_callback_to_replace_with_bool(contains_term, false);
      }
    }
    constant_term_checker_subject.start(contains_term->subject_term, Optimization::ConstantTermChecker::Mode::PREFIX);
    //check if the search term is contained in the prefix
    if (constant_term_checker_subject.is_constant_string()) {
      std::string subject_prefix = constant_term_checker_subject.get_constant_string();
      if (subject_prefix.find(search_) != std::string::npos) {
        add_callback_to_replace_with_bool(contains_term, true);
      }
    }
    constant_term_checker_subject.start(contains_term->subject_term, Optimization::ConstantTermChecker::Mode::SUFFIX);
    //check if the search term is contained in the suffix
    if (constant_term_checker_subject.is_constant_string()) {
      std::string subject_suffix = constant_term_checker_subject.get_constant_string();
      if (subject_suffix.find(search_) != std::string::npos) {
        add_callback_to_replace_with_bool(contains_term, true);
      }
    }
  } else if(Ast2Dot::isEquivalent(contains_term->subject_term,contains_term->search_term)) {
    add_callback_to_replace_with_bool(contains_term,true);
  }

//This is now redundent.
  /*else if (Ast2Dot::isEquivalent(contains_term->subject_term, contains_term->search_term)) {
   add_callback_to_replace_with_bool(contains_term, true);
   }*/
  DVLOG(VLOG_LEVEL) << "post visit end: " << *contains_term << "@" << contains_term;
}

void SyntacticOptimizer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_and_callback(not_contains_term->subject_term);
  visit_and_callback(not_contains_term->search_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_contains_term << "@" << not_contains_term;

  Optimization::ConstantTermChecker constant_term_checker;
  Optimization::ConstantTermChecker constant_term_checker_subject;

  constant_term_checker.start(not_contains_term->search_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker.is_constant_string()) {
    std::string search_ = constant_term_checker.get_constant_string();
    constant_term_checker_subject.start(not_contains_term->subject_term, Optimization::ConstantTermChecker::Mode::FULL);
    //If they are both constants, we can check the contains directly
    if (constant_term_checker_subject.is_constant_string()) {
      std::string subject_ = constant_term_checker_subject.get_constant_string();
      if (subject_.find(search_) != std::string::npos) {
        add_callback_to_replace_with_bool(not_contains_term, false);
      } else {
        add_callback_to_replace_with_bool(not_contains_term, true);
      }
    }
    constant_term_checker_subject.start(not_contains_term->subject_term,
                                        Optimization::ConstantTermChecker::Mode::PREFIX);
    //check if the search term is contained in the prefix
    if (constant_term_checker_subject.is_constant_string()) {
      std::string subject_prefix = constant_term_checker_subject.get_constant_string();
      if (subject_prefix.find(search_) != std::string::npos) {
        add_callback_to_replace_with_bool(not_contains_term, false);
      }
    }
    constant_term_checker_subject.start(not_contains_term->subject_term,
                                        Optimization::ConstantTermChecker::Mode::SUFFIX);
    //check if the search term is contained in the suffix
    if (constant_term_checker_subject.is_constant_string()) {
      std::string subject_suffix = constant_term_checker_subject.get_constant_string();
      if (subject_suffix.find(search_) != std::string::npos) {
        add_callback_to_replace_with_bool(not_contains_term, false);
      }
    }
  } else if(Ast2Dot::isEquivalent(not_contains_term->subject_term,not_contains_term->search_term)) {
    add_callback_to_replace_with_bool(not_contains_term, false);
  }

  /*if (Ast2Dot::isEquivalent(not_contains_term->subject_term, not_contains_term->search_term)) {
   add_callback_to_replace_with_bool(not_contains_term, false);
   }*/
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_contains_term << "@" << not_contains_term;
}

void SyntacticOptimizer::visitBegins(Begins_ptr begins_term) {
  visit_and_callback(begins_term->subject_term);
  visit_and_callback(begins_term->search_term);

  bool match = match_prefix(begins_term->subject_term, begins_term->search_term);
  if (!match) {
    add_callback_to_replace_with_bool(begins_term, false);
    return;
  }

  visit_and_callback(begins_term->subject_term);
  visit_and_callback(begins_term->search_term);

  Optimization::ConstantTermChecker constant_term_checker;

  constant_term_checker.start(begins_term->search_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker.is_constant_string()) {
    if (constant_term_checker.get_constant_string() == "") {
      add_callback_to_replace_with_bool(begins_term, true);
    }
  } else if (Ast2Dot::isEquivalent(begins_term->subject_term, begins_term->search_term)) {
    add_callback_to_replace_with_bool(begins_term, true);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *begins_term << "@" << begins_term;
  if (Ast2Dot::isEquivalent(begins_term->subject_term, begins_term->search_term)) {
    add_callback_to_replace_with_bool(begins_term, true);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *begins_term << "@" << begins_term;
}

void SyntacticOptimizer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_and_callback(not_begins_term->subject_term);
  visit_and_callback(not_begins_term->search_term);

  bool match = match_prefix(not_begins_term->subject_term, not_begins_term->search_term);
  if (!match) {
    add_callback_to_replace_with_bool(not_begins_term, true);
    return;
  }

  visit_and_callback(not_begins_term->subject_term);
  visit_and_callback(not_begins_term->search_term);

  Optimization::ConstantTermChecker constant_term_checker;

  constant_term_checker.start(not_begins_term->search_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker.is_constant_string()) {
    if (constant_term_checker.get_constant_string() == "") {
      add_callback_to_replace_with_bool(not_begins_term, false);
    }
  } else if (Ast2Dot::isEquivalent(not_begins_term->subject_term, not_begins_term->search_term)) {
    add_callback_to_replace_with_bool(not_begins_term, false);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_begins_term << "@" << not_begins_term;
  if (Ast2Dot::isEquivalent(not_begins_term->subject_term, not_begins_term->search_term)) {
    add_callback_to_replace_with_bool(not_begins_term, false);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_begins_term << "@" << not_begins_term;
}

void SyntacticOptimizer::visitEnds(Ends_ptr ends_term) {
  visit_and_callback(ends_term->subject_term);
  visit_and_callback(ends_term->search_term);

  bool match = match_suffix(ends_term->subject_term, ends_term->search_term);
  if (!match) {
    add_callback_to_replace_with_bool(ends_term, false);
    return;
  }

  visit_and_callback(ends_term->subject_term);
  visit_and_callback(ends_term->search_term);

  Optimization::ConstantTermChecker constant_term_checker;

  constant_term_checker.start(ends_term->search_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker.is_constant_string()) {
    if (constant_term_checker.get_constant_string() == "") {
      add_callback_to_replace_with_bool(ends_term, true);
    }
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *ends_term << "@" << ends_term;
  if (Ast2Dot::isEquivalent(ends_term->subject_term, ends_term->search_term)) {
    add_callback_to_replace_with_bool(ends_term, true);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *ends_term << "@" << ends_term;
}

void SyntacticOptimizer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_and_callback(not_ends_term->subject_term);
  visit_and_callback(not_ends_term->search_term);

  bool match = match_suffix(not_ends_term->subject_term, not_ends_term->search_term);
  if (!match) {
    add_callback_to_replace_with_bool(not_ends_term, true);
    return;
  }

  visit_and_callback(not_ends_term->subject_term);
  visit_and_callback(not_ends_term->search_term);

  Optimization::ConstantTermChecker constant_term_checker;

  constant_term_checker.start(not_ends_term->search_term, Optimization::ConstantTermChecker::Mode::FULL);

  if (constant_term_checker.is_constant_string()) {
    if (constant_term_checker.get_constant_string() == "") {
      add_callback_to_replace_with_bool(not_ends_term, false);
    }
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *not_ends_term << "@" << not_ends_term;
  if (Ast2Dot::isEquivalent(not_ends_term->subject_term, not_ends_term->search_term)) {
    add_callback_to_replace_with_bool(not_ends_term, false);
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *not_ends_term << "@" << not_ends_term;
}

void SyntacticOptimizer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_and_callback(index_of_term->subject_term);
  visit_and_callback(index_of_term->search_term);
  if (index_of_term->from_index) {
    visit_and_callback(index_of_term->from_index);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *index_of_term << "@" << index_of_term;
  if (index_of_term->from_index) {
    IndexOf::Mode mode;
    int mode_value = check_and_process_index_operation(index_of_term, index_of_term->subject_term,
                                                       index_of_term->from_index);
    mode = static_cast<IndexOf::Mode>(mode_value);
    if (IndexOf::Mode::NONE != mode) {
      index_of_term->setMode(mode);
    }
  } else if(index_of_term->subject_term->type() == Term::Type::TERMCONSTANT
              && index_of_term->search_term->type() == Term::Type::TERMCONSTANT) {
    auto subject = dynamic_cast<TermConstant_ptr>(index_of_term->subject_term);
    auto search = dynamic_cast<TermConstant_ptr>(index_of_term->search_term);
    size_t found = subject->getValue().find(search->getValue());
    std::string value = "";
    if(found == std::string::npos) {
      value = "-1";
    } else {
      value = std::to_string(found);
    }
    DVLOG(VLOG_LEVEL) << "Applying 'indexOf' transformation";
    callback_ = [this, index_of_term, value](Term_ptr & term) mutable {
      term = generate_term_constant(value, Primitive::Type::NUMERAL);
      delete index_of_term;
    };
    return;
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *index_of_term << "@" << index_of_term;
}

void SyntacticOptimizer::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_and_callback(last_index_of_term->subject_term);
  visit_and_callback(last_index_of_term->search_term);
  if (last_index_of_term->from_index) {
    visit_and_callback(last_index_of_term->from_index);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *last_index_of_term << "@" << last_index_of_term;
  if (last_index_of_term->from_index) {
    LastIndexOf::Mode mode;
    int mode_value = check_and_process_index_operation(last_index_of_term, last_index_of_term->subject_term,
                                                       last_index_of_term->from_index);
    mode = static_cast<LastIndexOf::Mode>(mode_value);
    if (LastIndexOf::Mode::NONE != mode) {
      last_index_of_term->setMode(mode);
    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *last_index_of_term << "@" << last_index_of_term;
}

void SyntacticOptimizer::visitCharAt(CharAt_ptr char_at_term) {
  visit_and_callback(char_at_term->subject_term);
  visit_and_callback(char_at_term->index_term);

  // DVLOG(VLOG_LEVEL) << "post visit start: " << *char_at_term << "@" << char_at_term;
  // Optimization::CharAtOptimization char_at_optimizer(char_at_term);
  // char_at_optimizer.start();
  // if (char_at_optimizer.is_optimizable()) {
  //   std::string str_value = char_at_optimizer.get_char_at_result_as_string();
  //   DVLOG(VLOG_LEVEL) << "Applying charAt transformation: '" << str_value << "'";
  //   callback_ = [this, char_at_term, str_value](Term_ptr & term) mutable {
  //     term = generate_term_constant(str_value, Primitive::Type::STRING);
  //     delete char_at_term;
  //   };
  // } else if (char_at_optimizer.is_index_updated()) {
  //   // there is a possible change in concat term, re-process subtree
  //   DVLOG(VLOG_LEVEL) << "char at optimization -> re visit term start" << *(char_at_term->subject_term);
  //   visit_and_callback(char_at_term->subject_term);
  //   DVLOG(VLOG_LEVEL) << "char at optimization -> re visit term end" << *(char_at_term->subject_term);
  // }
  // DVLOG(VLOG_LEVEL) << "post visit end: " << *char_at_term << "@" << char_at_term;
}

void SyntacticOptimizer::visitSubString(SubString_ptr sub_string_term) {
  visit_and_callback(sub_string_term->subject_term);
  visit_and_callback(sub_string_term->start_index_term);
  if (sub_string_term->end_index_term) {
    visit_and_callback(sub_string_term->end_index_term);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *sub_string_term << "@" << sub_string_term;
  Optimization::SubstringOptimization substring_optimizer(sub_string_term);
  substring_optimizer.start();
  if (substring_optimizer.is_optimizable()) {
    std::string value = substring_optimizer.get_substring_result();
    DVLOG(VLOG_LEVEL) << "Applying 'subString' transformation";
    callback_ = [this, sub_string_term, value](Term_ptr & term) mutable {
      term = generate_term_constant(value, Primitive::Type::STRING);
      delete sub_string_term;
    };
    return;
  } else if(auto term_constant = dynamic_cast<TermConstant_ptr>(sub_string_term->subject_term)) {
    if(term_constant->getValue() == "") {
      std::string value = "";
      DVLOG(VLOG_LEVEL) << "Applying 'subString' transformation";
      callback_ = [this, sub_string_term, value](Term_ptr & term) mutable {
        term = generate_term_constant(value, Primitive::Type::STRING);
        delete sub_string_term;
      };
      return;
    }
    else if(sub_string_term->start_index_term->type() == Term::Type::TERMCONSTANT
                && sub_string_term->end_index_term->type() == Term::Type::TERMCONSTANT) {
      auto index = dynamic_cast<TermConstant_ptr>(sub_string_term->start_index_term);
      auto length = dynamic_cast<TermConstant_ptr>(sub_string_term->end_index_term);
      int index_val = std::stoi(index->getValue());
      int length_val = std::stoi(length->getValue());
      if(index_val == 0 && length_val >= 0) {
        std::string value = std::string(term_constant->getValue(),index_val,length_val);
        DVLOG(VLOG_LEVEL) << "Applying 'subString' transformation";
        callback_ = [this, sub_string_term, value](Term_ptr & term) mutable {
          term = generate_term_constant(value, Primitive::Type::STRING);
          delete sub_string_term;
        };
        return;
      }
    }
  }

  if (substring_optimizer.is_index_updated()) {
    DVLOG(VLOG_LEVEL) << "substring optimization -> re visit term start" << *(sub_string_term->subject_term);
    visit_and_callback(sub_string_term->subject_term);
    DVLOG(VLOG_LEVEL) << "substring optimization -> re visit term end" << *(sub_string_term->subject_term);
  }



  if(!ss_flag) {
    std::string ss_string = Ast2Dot::toString(sub_string_term);
    if(symbol_table_->ss_term_vars.find(ss_string) == symbol_table_->ss_term_vars.end()) {
      std::string temp_var_name = symbol_table_->get_var_name_for_node(sub_string_term,Variable::Type::STRING);
      auto temp_var = new Variable(temp_var_name,Variable::Type::STRING);
      symbol_table_->add_variable(temp_var);
      symbol_table_->ss_term_vars[ss_string] = temp_var;

      auto temp_qi_term = generate_qual_identifier(temp_var_name);
      ss_terms.push_back(new Eq(temp_qi_term,sub_string_term));

      callback_ = [this,sub_string_term,ss_string](Term_ptr & term) mutable {
        auto temp_qi_term = generate_qual_identifier(symbol_table_->ss_term_vars[ss_string]->getName());
        term = temp_qi_term;
      };

    } else {
      callback_ = [this,sub_string_term,ss_string](Term_ptr & term) mutable {
        auto temp_qi_term = generate_qual_identifier(symbol_table_->ss_term_vars[ss_string]->getName());
        term = temp_qi_term;
      };
    }
  }

  // TODO Below code is disabled temporarily, trying to get a better solution

//  SubString::Mode mode;
//  if (sub_string_term->end_index_term) {
//    mode = check_and_process_subString(sub_string_term, sub_string_term->start_index_term,
//                                       sub_string_term->end_index_term);
//  } else {
//    mode = check_and_process_subString(sub_string_term, sub_string_term->start_index_term);
//  }
//
//  if (SubString::Mode::NONE != mode) {
//    sub_string_term->setMode(mode);
//  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *sub_string_term << "@" << sub_string_term;
}

void SyntacticOptimizer::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_and_callback(to_upper_term->subject_term);
  Optimization::ConstantTermChecker string_constant_checker;
  string_constant_checker.start(to_upper_term->subject_term);
  if (string_constant_checker.is_constant_string()) {
    std::string data = string_constant_checker.get_constant_string();
    std::transform(data.begin(), data.end(), data.begin(), ::toupper);
    DVLOG(VLOG_LEVEL) << "Applying toupper transformation.";
    callback_ = [this, to_upper_term, data](Term_ptr & term) mutable {
      term = generate_term_constant(data, Primitive::Type::STRING);
      delete to_upper_term;
    };
  }
}

void SyntacticOptimizer::visitToLower(ToLower_ptr to_lower_term) {
  visit_and_callback(to_lower_term->subject_term);
  Optimization::ConstantTermChecker string_constant_checker;
  string_constant_checker.start(to_lower_term->subject_term);
  if (string_constant_checker.is_constant_string()) {
    std::string data = string_constant_checker.get_constant_string();
    std::transform(data.begin(), data.end(), data.begin(), ::tolower);
    DVLOG(VLOG_LEVEL) << "Applying tolower transformation.";
    callback_ = [this, to_lower_term, data](Term_ptr & term) mutable {
      term = generate_term_constant(data, Primitive::Type::STRING);
      delete to_lower_term;
    };
  }
}

void SyntacticOptimizer::visitTrim(Trim_ptr trim_term) {
  visit_and_callback(trim_term->subject_term);
// TODO add optimization
}

void SyntacticOptimizer::visitToString(ToString_ptr to_string_term) {
  visit_and_callback(to_string_term->subject_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *to_string_term << "@" << to_string_term;
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_string_term->subject_term)) {
    if (Primitive::Type::NUMERAL == term_constant->getValueType()) {
      std::string str_value = term_constant->getValue();
      if(str_value == "-1") {
        str_value = "";
      }
      DVLOG(VLOG_LEVEL) << "Applying 'toString' transformation: '" << str_value << "'";
      callback_ = [this, to_string_term, str_value](Term_ptr & term) mutable {
        term = generate_term_constant(str_value, Primitive::Type::STRING);
        delete to_string_term;
      };
    }
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *to_string_term << "@" << to_string_term;
}

void SyntacticOptimizer::visitToInt(ToInt_ptr to_int_term) {
  visit_and_callback(to_int_term->subject_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *to_int_term << "@" << to_int_term;
  Optimization::ConstantTermChecker string_constant_checker;
  string_constant_checker.start(to_int_term->subject_term);
  if (string_constant_checker.is_constant_string()) {
    std::string data = string_constant_checker.get_constant_string();
    bool is_num = !data.empty();
    for(auto c : data) {
      if(!is_num || !std::isdigit(c)) {
        is_num = false;
        break;
      }
    }

//    std::transform(data.begin(), data.end(), data.begin(), ::tolower);
    if(!is_num) {
      data = "-1";
    } else {
      data = std::to_string(std::stoi(data));
    }
    DVLOG(VLOG_LEVEL) << "Applying toint transformation: result = " << data;
    callback_ = [this, to_int_term, data](Term_ptr & term) mutable {
      term = generate_term_constant(data, Primitive::Type::NUMERAL);
      delete to_int_term;
    };
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *to_int_term << "@" << to_int_term;
}

void SyntacticOptimizer::visitReplace(Replace_ptr replace_term) {
  visit_and_callback(replace_term->subject_term);
  visit_and_callback(replace_term->search_term);
  visit_and_callback(replace_term->replace_term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *replace_term << "@" << replace_term;
  if (Ast2Dot::isEquivalent(replace_term->search_term, replace_term->replace_term)) {
    callback_ = [replace_term](Term_ptr & term) mutable {
      term = replace_term->subject_term;
      replace_term->subject_term = nullptr;
      delete replace_term;
    };
  }
  DVLOG(VLOG_LEVEL) << "post visit end: " << *replace_term << "@" << replace_term;
}

void SyntacticOptimizer::visitCount(Count_ptr count_term) {
  visit_and_callback(count_term->subject_term);
  visit_and_callback(count_term->bound_term);
}

void SyntacticOptimizer::visitIte(Ite_ptr ite_term) {

  // if transform_ite_ is true and we reach this point, then we couldn't optimize either branch away
  if(not transform_ite_) {
    return;
  }

  visit_and_callback(ite_term->cond);
  visit_and_callback(ite_term->then_branch);
  visit_and_callback(ite_term->else_branch);
  

  callback_ = [ite_term, this] (Term_ptr& term) mutable {
    auto ast_sort_computer = new AstSortComputer(root_,symbol_table_);
    ast_sort_computer->start(term);

  	Term_ptr ite_condition = ite_term->cond;
  	Term_ptr ite_then_branch = ite_term->then_branch;
  	Term_ptr ite_else_branch = ite_term->else_branch;

  	Term_ptr then_branch_term = nullptr;
		Term_ptr else_branch_term = nullptr;
		Term_ptr true_cond = ite_condition;
		Term_ptr false_cond = nullptr;

		auto ite_sort = ast_sort_computer->GetTermSort(term);
    Variable::Type temp_var_type;
    switch(ite_sort) {
      case Sort::Type::STRING:
        temp_var_type = Variable::Type::STRING;
        break;
      case Sort::Type::INT:
        temp_var_type = Variable::Type::INT;
        break;
      case Sort::Type::BOOL:
        temp_var_type = Variable::Type::BOOL;
        break;
      default:
        LOG(FATAL) << "Unknown variable type!";
        break;
    }


    std::string temp_var_name = symbol_table_->get_var_name_for_node(ite_term,temp_var_type);
    auto temp_var = new Variable(temp_var_name,temp_var_type);
    symbol_table_->add_variable(temp_var);
    
    auto temp_qi_term = generate_qual_identifier(temp_var_name);

		if (Not_ptr not_term = dynamic_cast<Not_ptr>(true_cond)) {
			false_cond = not_term->term->clone();
		} else {
			false_cond = new Not(true_cond->clone());
		}

    // (ite P Q R)
    // (P => Q) && (~P => R)
    // (~P || Q) && (P || R)
    // TermList_ptr left_term_list = new TermList();
    // TermList_ptr right_term_list = new TermList();

    // left_term_list->push_back(false_cond);
    // left_term_list->push_back(ite_then_branch);

    // right_term_list->push_back(true_cond);
    // right_term_list->push_back(ite_else_branch);

    // Or_ptr left_or = new Or(left_term_list);
    // Or_ptr right_or = new Or(right_term_list);

    // TermList_ptr and_term_list = new TermList();
    // and_term_list->push_back(left_or);
    // and_term_list->push_back(right_or);

    // And_ptr and_term = new And(and_term_list);

		// // process then branch
		if (And_ptr then_branch = dynamic_cast<And_ptr>(ite_then_branch)) {
			then_branch->term_list->insert(then_branch->term_list->begin(), true_cond);
			then_branch_term = then_branch;
		} else if (Or_ptr then_branch = dynamic_cast<Or_ptr>(ite_then_branch)) {
			then_branch->term_list->insert(then_branch->term_list->begin(), true_cond);
			then_branch_term = then_branch;
		} else {
			TermList_ptr local_term_list = new TermList();
			local_term_list->push_back(true_cond);
			if(!ast_sort_computer->IsBoolTerm(ite_then_branch)) {
        local_term_list->push_back(new Eq(temp_qi_term->clone(),ite_then_branch));
      } else {
        local_term_list->push_back(ite_then_branch);
      }
      then_branch_term = new And(local_term_list);
		}
		// process else branch
		if (And_ptr else_branch = dynamic_cast<And_ptr>(ite_else_branch)) {
			else_branch->term_list->insert(else_branch->term_list->begin(), false_cond);
			else_branch_term = else_branch;
		} else if (Or_ptr else_branch = dynamic_cast<Or_ptr>(ite_else_branch)) {
			else_branch->term_list->insert(else_branch->term_list->begin(), false_cond);
			else_branch_term = else_branch;
		} else {
			TermList_ptr local_term_list = new TermList();
			local_term_list->push_back(false_cond);
			if(!ast_sort_computer->IsBoolTerm(ite_else_branch)) {
        local_term_list->push_back(new Eq(temp_qi_term->clone(),ite_else_branch));
      } else {
        local_term_list->push_back(ite_else_branch);
      }
			else_branch_term = new And(local_term_list);
		}
		TermList_ptr term_list = new TermList();
		term_list->push_back(then_branch_term);
		term_list->push_back(else_branch_term);

		Or_ptr or_term = new Or(term_list);
//    Ast2Dot::inspectAST(term);
//    Ast2Dot::inspectAST(or_term);
    if(!ast_sort_computer->IsBoolTerm(ite_then_branch) || !ast_sort_computer->IsBoolTerm(ite_else_branch)) {

      term = temp_qi_term->clone();

      ite_terms_.push_back(or_term);
    } else {
		  term = or_term;
    }
//    Ast2Dot::inspectAST(term);
//    std::cin.get();

    ite_term->cond = nullptr;
		ite_term->then_branch = nullptr;
		ite_term->else_branch = nullptr;
		delete ite_term;

    //delete temp_qi_term;
		delete ast_sort_computer;
  };

}

void SyntacticOptimizer::visitReConcat(ReConcat_ptr re_concat_term) {
  for (auto& term_ptr : *(re_concat_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_concat_term << "@" << re_concat_term;
  TermConstant_ptr initial_term_constant = nullptr;
  Optimization::ConstantTermChecker string_constant_checker;
  int pos = 0;
  for (auto iter = re_concat_term->term_list->begin(); iter != re_concat_term->term_list->end();) {
    if (Term::Type::CONCAT == (*iter)->type()) {
      Concat_ptr sub_concat_term = dynamic_cast<Concat_ptr>(*iter);
      re_concat_term->term_list->erase(iter);
      re_concat_term->term_list->insert(iter, sub_concat_term->term_list->begin(), sub_concat_term->term_list->end());
      sub_concat_term->term_list->clear();
      delete sub_concat_term;
      iter = re_concat_term->term_list->begin() + pos;  // insertion invalidates iter, reset it
      continue;
    } else if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter)) {
      if (initial_term_constant == nullptr) {
        initial_term_constant = term_constant;
      } else {
        append_constant(initial_term_constant, term_constant);
        delete term_constant;  // deallocate
        re_concat_term->term_list->erase(iter);
        continue;
      }
    } else {
      if (initial_term_constant) {  // if there is a constant regex makes it string
        string_constant_checker.start(initial_term_constant);
        if (string_constant_checker.is_constant_string()) {
          initial_term_constant->primitive->setData(string_constant_checker.get_constant_string());
          initial_term_constant->primitive->setType(Primitive::Type::STRING);
        }
        string_constant_checker.end();
      }
      initial_term_constant = nullptr;
    }
    iter++;
    pos++;
  }

  callback_ = [re_concat_term] (Term_ptr & term) mutable {
    if (re_concat_term->term_list->size() == 1) {
      term = re_concat_term->term_list->front();
      re_concat_term->term_list->clear();
    } else {
      term = new Concat(re_concat_term->term_list);
      re_concat_term->term_list = nullptr;
    }
    delete re_concat_term;
  };
  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_concat_term << "@" << re_concat_term;
}

void SyntacticOptimizer::visitReUnion(ReUnion_ptr re_union_term) {
  for (auto& term_ptr : *(re_union_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_union_term << "@" << re_union_term;
  Util::RegularExpression_ptr union_regex = Util::RegularExpression::makeEmpty();
  Util::RegularExpression_ptr child_regex = nullptr, tmp_regex = nullptr;
  for (auto term : *(re_union_term->term_list)) {
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term)) {
      if (Primitive::Type::STRING == term_constant->getValueType() or Primitive::Type::REGEX == term_constant->getValueType()) {
        if(Primitive::Type::STRING == term_constant->getValueType()) {
          child_regex = new Util::RegularExpression(Util::RegularExpression::escape_raw_string(term_constant->getValue()));
        } else {
          child_regex = new Util::RegularExpression(term_constant->getValue());
        }
        tmp_regex = union_regex;
        union_regex = Util::RegularExpression::makeUnion(tmp_regex->clone(), child_regex->clone());
        delete tmp_regex; delete child_regex;
      } else {
        LOG(FATAL) << "un-expected constant as a parameter to 're.union'";
      }
    } else {
      LOG(FATAL)<< "un-expected term as a parameter to 're.union'";
    }
  }

  auto regex_term_constant = generate_term_constant(union_regex->str(), Primitive::Type::REGEX);

  delete union_regex;
  callback_ = [regex_term_constant, re_union_term] (Term_ptr & term) mutable {
    term = regex_term_constant;
    delete re_union_term;
  };
  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_union_term << "@" << re_union_term;
}

//void SyntacticOptimizer::visitReInter(ReInter_ptr re_inter_term) {
//  for (auto& term_ptr : *(re_inter_term->term_list)) {
//    visit_and_callback(term_ptr);
//  }
//
//  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_inter_term << "@" << re_inter_term;
//  TermConstant_ptr intersection_regex_term_constant = nullptr;
//
//  for (auto iter = re_inter_term->term_list->begin(); iter != re_inter_term->term_list->end();) {
//    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(*iter)) {
//      if(term_constant->getValueType() == Primitive::Type::STRING) {
//        LOG(INFO) << term_constant->getValue() << "        STRING";
//      }
//      if (intersection_regex_term_constant == nullptr) {
//        intersection_regex_term_constant = term_constant;
//
//        std::string value = "";
////        if(term_constant->getValueType() == Primitive::Type::STRING) {
////          value = Util::RegularExpression::escape_raw_string(term_constant->getValue());
////        } else {
//          value = term_constant->getValue();
////        }
//
//        if (*(value.begin()) != '(' or *(value.end() - 1) != ')') {
//          value = "(" + value + ")";
//          intersection_regex_term_constant->primitive->setData(value);
//        }
//      } else {
//        std::stringstream ss;
//        ss << intersection_regex_term_constant->getValue() << "&";
//
//        std::string value = "";
////        if(term_constant->getValueType() == Primitive::Type::STRING) {
////          value = Util::RegularExpression::escape_raw_string(term_constant->getValue());
////        } else {
//          value = term_constant->getValue();
////        }
//
//        if (*(value.begin()) != '(' or *(value.end() - 1) != ')') {
//          ss << "(" << value << ")";
//        } else {
//          ss << value;
//        }
//        intersection_regex_term_constant->primitive->setData("(" + ss.str() + ")");
//        delete term_constant;  // deallocate
//        re_inter_term->term_list->erase(iter);
//        continue;
//      }
//    } else {
//      LOG(FATAL)<< "un-expected term as a parameter to 're.inter'";
//    }
//    iter++;
//  }
//
//  callback_ = [re_inter_term] (Term_ptr & term) mutable {
//    term = re_inter_term->term_list->front();
//    re_inter_term->term_list->clear();
//    delete re_inter_term;
//  };
//  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_inter_term << "@" << re_inter_term;
//}

void SyntacticOptimizer::visitReInter(ReInter_ptr re_inter_term) {
  for (auto& term_ptr : *(re_inter_term->term_list)) {
    visit_and_callback(term_ptr);
  }

  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_inter_term << "@" << re_inter_term;
  Util::RegularExpression_ptr inter_regex = Util::RegularExpression::makeAnyString();
  Util::RegularExpression_ptr child_regex = nullptr, tmp_regex = nullptr;
  for (auto term : *(re_inter_term->term_list)) {
    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term)) {
      if (Primitive::Type::STRING == term_constant->getValueType() or Primitive::Type::REGEX == term_constant->getValueType()) {
        if(Primitive::Type::STRING == term_constant->getValueType()) {
          child_regex = new Util::RegularExpression(Util::RegularExpression::escape_raw_string(term_constant->getValue()));
        } else {
          child_regex = new Util::RegularExpression(term_constant->getValue());
        }
        tmp_regex = inter_regex;
        inter_regex = Util::RegularExpression::makeIntersection(tmp_regex->clone(), child_regex->clone());
        delete tmp_regex; delete child_regex;
      } else {
        LOG(FATAL) << "un-expected constant as a parameter to 're.inter'";
      }
    } else {
      LOG(FATAL)<< "un-expected term as a parameter to 're.inter'";
    }
  }

  auto regex_term_constant = generate_term_constant(inter_regex->str(), Primitive::Type::REGEX);
  delete inter_regex;
  callback_ = [regex_term_constant, re_inter_term] (Term_ptr & term) mutable {
    term = regex_term_constant;
    delete re_inter_term;
  };
  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_inter_term << "@" << re_inter_term;
}

void SyntacticOptimizer::visitReStar(ReStar_ptr re_star_term) {
  visit_and_callback(re_star_term->term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_star_term << "@" << re_star_term;
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(re_star_term->term)) {
    std::string value = "";
    if(term_constant->getValueType() == Primitive::Type::STRING) {
      value = Util::RegularExpression::escape_raw_string(term_constant->getValue());
    } else {
      value = term_constant->getValue();
    }
    value = "(" + value + ")*";
    term_constant->primitive->setData(value);
    term_constant->primitive->setType(Primitive::Type::REGEX);
  } else {
    LOG(FATAL)<< "un-expected term as a parameter to 're.star'";
  }

  callback_ = [re_star_term] (Term_ptr & term) mutable {
    term = re_star_term->term;
    re_star_term->term = nullptr;
    delete re_star_term;
  };
  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_star_term << "@" << re_star_term;
}

void SyntacticOptimizer::visitRePlus(RePlus_ptr re_plus_term) {
  visit_and_callback(re_plus_term->term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_plus_term << "@" << re_plus_term;
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(re_plus_term->term)) {
    std::string value = "";
    if(term_constant->getValueType() == Primitive::Type::STRING) {
      value = Util::RegularExpression::escape_raw_string(term_constant->getValue());
    } else {
      value = term_constant->getValue();
    }
    value = "(" + value + ")+";
    term_constant->primitive->setData(value);
    term_constant->primitive->setType(Primitive::Type::REGEX);
  } else {
    LOG(FATAL)<< "un-expected term as a parameter to 're.plus'";
  }

  callback_ = [re_plus_term] (Term_ptr & term) mutable {
    term = re_plus_term->term;
    re_plus_term->term = nullptr;
    delete re_plus_term;
  };
  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_plus_term << "@" << re_plus_term;
}

void SyntacticOptimizer::visitReOpt(ReOpt_ptr re_opt_term) {
  visit_and_callback(re_opt_term->term);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_opt_term << "@" << re_opt_term;
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(re_opt_term->term)) {
    std::string value = "";
    if(term_constant->getValueType() == Primitive::Type::STRING) {
      value = Util::RegularExpression::escape_raw_string(term_constant->getValue());
    } else {
      value = term_constant->getValue();
    }
    value = "(" + value + ")?";
    term_constant->primitive->setData(value);
    term_constant->primitive->setType(Primitive::Type::REGEX);
  } else {
    LOG(FATAL)<< "un-expected term as a parameter to 're.plus'";
  }

  callback_ = [re_opt_term] (Term_ptr & term) mutable {
    term = re_opt_term->term;
    re_opt_term->term = nullptr;
    delete re_opt_term;
  };
  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_opt_term << "@" << re_opt_term;
}

void SyntacticOptimizer::visitReLoop(ReLoop_ptr re_loop_term) {
  visit_and_callback(re_loop_term->term);
  visit_and_callback(re_loop_term->lower);
  visit_and_callback(re_loop_term->upper);
  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_loop_term << "@" << re_loop_term;

  auto regex_term = dynamic_cast<TermConstant_ptr>(re_loop_term->term);
  auto lower_term = dynamic_cast<TermConstant_ptr>(re_loop_term->lower);
  auto upper_term = dynamic_cast<TermConstant_ptr>(re_loop_term->upper);

  if(regex_term != nullptr && lower_term != nullptr && upper_term != nullptr) {
    std::string value = "";
    if(regex_term->getValueType() == Primitive::Type::STRING) {
      value = "(" + Util::RegularExpression::escape_raw_string(regex_term->getValue()) + ")" +
          "{" + lower_term->getValue() + "," + upper_term->getValue() + "}";
    } else {
      value = "(" + regex_term->getValue() + ")" +
          "{" + lower_term->getValue() + "," + upper_term->getValue() + "}";
    }
    regex_term->primitive->setData(value);
    regex_term->primitive->setType(Primitive::Type::REGEX);
  } else {
    LOG(FATAL) << "Unexpected term as a parameter to 're.loop'";
  }

  callback_ = [re_loop_term] (Term_ptr & term) mutable {
    term = re_loop_term->term;
    re_loop_term->term = nullptr;
    delete re_loop_term;
  };

  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_loop_term << "@" << re_loop_term;
}

void SyntacticOptimizer::visitReComp(ReComp_ptr re_comp_term) {
  visit_and_callback(re_comp_term->term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_comp_term << "@" << re_comp_term;

  auto regex_term = dynamic_cast<TermConstant_ptr>(re_comp_term->term);

  if(regex_term != nullptr) {
    std::string value = "";
    if(regex_term->getValueType() == Primitive::Type::STRING) {
      value = "(~(" + Util::RegularExpression::escape_raw_string(regex_term->getValue()) + "))";
    } else {
      value = "(~(" + regex_term->getValue() + "))";
    }
    regex_term->primitive->setData(value);
    regex_term->primitive->setType(Primitive::Type::REGEX);
  } else {
    LOG(FATAL) << "Unexpected term as a paramter to 're.comp'";
  }

  callback_ = [re_comp_term] (Term_ptr & term) mutable {
    term = re_comp_term->term;
    re_comp_term->term = nullptr;
    delete re_comp_term;
  };

  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_comp_term << "@" << re_comp_term;
}

void SyntacticOptimizer::visitReDiff(ReDiff_ptr re_diff_term) {
  visit_and_callback(re_diff_term->left_term);
  visit_and_callback(re_diff_term->right_term);


  DVLOG(VLOG_LEVEL) << "post visit start: " << *re_diff_term << "@" << re_diff_term;

  auto left_regex_term = dynamic_cast<TermConstant_ptr>(re_diff_term->left_term);
  auto right_regex_term = dynamic_cast<TermConstant_ptr>(re_diff_term->right_term);

  if(left_regex_term != nullptr && right_regex_term != nullptr) {
    std::string left = left_regex_term->getValue();
    std::string right = right_regex_term->getValue();

    if(left_regex_term->getValueType() == Primitive::Type::STRING) {
      left = Util::RegularExpression::escape_raw_string(left);
    }

    if(right_regex_term->getValueType() == Primitive::Type::STRING) {
      right = Util::RegularExpression::escape_raw_string(right);
    }

    std::string value = "((" + left + ")"
                       + "&~(" + right + "))";

    left_regex_term->primitive->setData(value);
    left_regex_term->primitive->setType(Primitive::Type::REGEX);
  } else {
    LOG(FATAL) << "Unexpected term as a paramter to 're.comp'";
  }

  callback_ = [re_diff_term] (Term_ptr & term) mutable {
    term = re_diff_term->left_term;
    re_diff_term->left_term = nullptr;
    delete re_diff_term;
  };

  DVLOG(VLOG_LEVEL) << "post visit end: " << *re_diff_term << "@" << re_diff_term;
}

void SyntacticOptimizer::visitToRegex(ToRegex_ptr to_regex_term) {
  visit_and_callback(to_regex_term->term);

  DVLOG(VLOG_LEVEL) << "post visit start: " << *to_regex_term << "@" << to_regex_term;
  if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(to_regex_term->term)) {
    if (Primitive::Type::STRING == term_constant->getValueType()) {
      DVLOG(VLOG_LEVEL) << "Transforming operation: '" << *to_regex_term << "'";//      }
      std::string data = term_constant->getValue();
      if(data.empty()) {
        term_constant->primitive->setData("~(.+)");
      } else {
        term_constant->primitive->setData(Util::RegularExpression::escape_raw_string(data));
      }
      term_constant->primitive->setType(Primitive::Type::REGEX);
      callback_ = [to_regex_term] (Term_ptr & term) mutable {
        term = to_regex_term->term;
        to_regex_term->term = nullptr;
        delete to_regex_term;
      };
    }
  } else if(QualIdentifier_ptr qualid = dynamic_cast<QualIdentifier_ptr>(to_regex_term->term)) {
    callback_ = [to_regex_term] (Term_ptr & term) mutable {
      term = to_regex_term->term;
      to_regex_term->term = nullptr;
      delete to_regex_term;
    };
  } 
  DVLOG(VLOG_LEVEL) << "post visit end: " << *to_regex_term << "@" << to_regex_term;
}

void SyntacticOptimizer::visitUnknownTerm(Unknown_ptr unknown_term) {
//  LOG(FATAL)<< "check unknown term" << *unknown_term;
}

void SyntacticOptimizer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void SyntacticOptimizer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  if(symbol_table_->has_variable_binding(qi_term->identifier->symbol->getData())) {
    auto replacement_term = symbol_table_->get_variable_binding(qi_term->identifier->symbol->getData());
    callback_ = [qi_term, replacement_term] (Term_ptr & term) {
      delete qi_term;
      term = replacement_term;
    };
  }
}

void SyntacticOptimizer::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "post visit start: " << *term_constant << "@" << term_constant;
  // Optimization::ConstantTermChecker string_constant_checker;
  // string_constant_checker.start(term_constant);
  DVLOG(VLOG_LEVEL) << "post visit end: " << *term_constant << "@" << term_constant;
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
  if(symbol_table_->has_variable_binding(var_binding->symbol->getData())) {
    LOG(FATAL) << "Duplicate binding found...";
  }

  symbol_table_->add_variable_binding(var_binding->symbol->getData(),var_binding->term);
}

void SyntacticOptimizer::visit_and_callback(Term_ptr & term) {
  visit(term);
  if (callback_) {
    callback_(term);
    callback_ = nullptr;
    visit_and_callback(term);  // TODO be carefull!!
  }
}

void SyntacticOptimizer::append_constant(TermConstant_ptr left_constant, TermConstant_ptr right_constant) {
  std::stringstream ss;

  if(Primitive::Type::REGEX == left_constant->getValueType() && Primitive::Type::STRING == right_constant->getValueType()) {
    ss << left_constant->getValue() << Util::RegularExpression::escape_raw_string(right_constant->getValue());
  } else if(Primitive::Type::STRING == left_constant->getValueType() && Primitive::Type::REGEX == right_constant->getValueType()) {
    ss << Util::RegularExpression::escape_raw_string(left_constant->getValue()) << right_constant->getValue();
  } else {
    ss << left_constant->getValue() << right_constant->getValue();
  }

//  ss << left_constant->getValue() << right_constant->getValue();
  left_constant->primitive->setData(ss.str());
  if (Primitive::Type::REGEX == left_constant->getValueType()
            or Primitive::Type::REGEX == right_constant->getValueType()) {
    left_constant->primitive->setType(Primitive::Type::REGEX);
  }
}

// TODO: Currently only supports arithmetic types; expand to string constraints
bool SyntacticOptimizer::check_condition_against_term(SMT::Term_ptr cond, SMT::Term_ptr term) {
  // simple equivalence check, works regardless of term types
  // if they match, term is assumed to be true (MUST BE UNDER AND) so cond must also be true (for sat)
  if(Ast2Dot::toString(cond) == Ast2Dot::toString(term)) {
    return true;
  }
  QualIdentifier_ptr cond_qualid = nullptr;
  TermConstant_ptr cond_termconstant = nullptr;
  bool is_cond_equality = true;

  Theory::ArithmeticFormula_ptr left_formula = new Theory::ArithmeticFormula();
  Theory::ArithmeticFormula_ptr right_formula = new Theory::ArithmeticFormula();
  

  // only check condition satisfiability for eq,neq conditions
  // a more aggressive analysis is required for terms beyond those
  if(Eq_ptr eq_cond_term = dynamic_cast<Eq_ptr>(cond)) {
    if(Term::Type::QUALIDENTIFIER == eq_cond_term->left_term->type() and Term::Type::TERMCONSTANT == eq_cond_term->right_term->type()) {
      cond_qualid = dynamic_cast<QualIdentifier_ptr>(eq_cond_term->left_term);
      cond_termconstant = dynamic_cast<TermConstant_ptr>(eq_cond_term->right_term);
      is_cond_equality = true;
      left_formula->SetType(Theory::ArithmeticFormula::Type::EQ);
    } else if(Term::Type::QUALIDENTIFIER == eq_cond_term->right_term->type() and Term::Type::TERMCONSTANT == eq_cond_term->left_term->type()) {
      cond_qualid = dynamic_cast<QualIdentifier_ptr>(eq_cond_term->right_term);
      cond_termconstant = dynamic_cast<TermConstant_ptr>(eq_cond_term->left_term);
      is_cond_equality = true;
      left_formula->SetType(Theory::ArithmeticFormula::Type::EQ);
    } else {
      return false;
    }
  } else if(NotEq_ptr not_eq_cond_term = dynamic_cast<NotEq_ptr>(cond)) {
    if(Term::Type::QUALIDENTIFIER == not_eq_cond_term->left_term->type() and Term::Type::TERMCONSTANT == not_eq_cond_term->right_term->type()) {
      cond_qualid = dynamic_cast<QualIdentifier_ptr>(not_eq_cond_term->left_term);
      cond_termconstant = dynamic_cast<TermConstant_ptr>(not_eq_cond_term->right_term);
      is_cond_equality = false;
      left_formula->SetType(Theory::ArithmeticFormula::Type::NOTEQ);
    } else if(Term::Type::QUALIDENTIFIER == not_eq_cond_term->right_term->type() and Term::Type::TERMCONSTANT == not_eq_cond_term->left_term->type()) {
      cond_qualid = dynamic_cast<QualIdentifier_ptr>(not_eq_cond_term->right_term);
      cond_termconstant = dynamic_cast<TermConstant_ptr>(not_eq_cond_term->left_term);
      is_cond_equality = false;
      left_formula->SetType(Theory::ArithmeticFormula::Type::NOTEQ);
    } else {
      return false;
    }
  } else {
    return false;
  }
  QualIdentifier_ptr term_qualid = nullptr;
  TermConstant_ptr term_termconstant = nullptr;
  Term::Type term_type;

  // extract variable and constant from term for further processing
  switch(term->type()) {
    case Term::Type::EQ: {
      term_type = Term::Type::EQ;
      right_formula->SetType(Theory::ArithmeticFormula::Type::EQ);
      Eq_ptr eq_term = dynamic_cast<Eq_ptr>(term);
      if(Term::Type::QUALIDENTIFIER == eq_term->left_term->type() and Term::Type::TERMCONSTANT == eq_term->right_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(eq_term->left_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(eq_term->right_term);
      } else if(Term::Type::QUALIDENTIFIER == eq_term->right_term->type() and Term::Type::TERMCONSTANT == eq_term->left_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(eq_term->right_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(eq_term->left_term);
      } 
      break;
    }
    case Term::Type::NOTEQ: {
      term_type = Term::Type::NOTEQ;
      right_formula->SetType(Theory::ArithmeticFormula::Type::NOTEQ);
      NotEq_ptr not_eq_term = dynamic_cast<NotEq_ptr>(term);
      if(Term::Type::QUALIDENTIFIER == not_eq_term->left_term->type() and Term::Type::TERMCONSTANT == not_eq_term->right_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(not_eq_term->left_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(not_eq_term->right_term);
      } else if(Term::Type::QUALIDENTIFIER == not_eq_term->right_term->type() and Term::Type::TERMCONSTANT == not_eq_term->left_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(not_eq_term->right_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(not_eq_term->left_term);
      } 
      break;
    }
    case Term::Type::LT: {
      term_type = Term::Type::LT;
      right_formula->SetType(Theory::ArithmeticFormula::Type::LT);
      Lt_ptr lt_term = dynamic_cast<Lt_ptr>(term);
      if(Term::Type::QUALIDENTIFIER == lt_term->left_term->type() and Term::Type::TERMCONSTANT == lt_term->right_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(lt_term->left_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(lt_term->right_term);
      } else if(Term::Type::QUALIDENTIFIER == lt_term->right_term->type() and Term::Type::TERMCONSTANT == lt_term->left_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(lt_term->right_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(lt_term->left_term);
        term_type = Term::Type::GT; // for consistency, var on left, constant on right
        right_formula->SetType(Theory::ArithmeticFormula::Type::GT);
      }
      break;
    }
    case Term::Type::LE: {
      term_type = Term::Type::LE;
      right_formula->SetType(Theory::ArithmeticFormula::Type::LE);
      Le_ptr le_term = dynamic_cast<Le_ptr>(term);
      if(Term::Type::QUALIDENTIFIER == le_term->left_term->type() and Term::Type::TERMCONSTANT == le_term->right_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(le_term->left_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(le_term->right_term);
      } else if(Term::Type::QUALIDENTIFIER == le_term->right_term->type() and Term::Type::TERMCONSTANT == le_term->left_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(le_term->right_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(le_term->left_term);
        term_type = Term::Type::GE; // for consistency, var on left, constant on right
        right_formula->SetType(Theory::ArithmeticFormula::Type::GE);
      }
      break;
    }
    case Term::Type::GT: {
      term_type = Term::Type::GT;
      right_formula->SetType(Theory::ArithmeticFormula::Type::GT);
      Gt_ptr gt_term = dynamic_cast<Gt_ptr>(term);
      if(Term::Type::QUALIDENTIFIER == gt_term->left_term->type() and Term::Type::TERMCONSTANT == gt_term->right_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(gt_term->left_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(gt_term->right_term);
      } else if(Term::Type::QUALIDENTIFIER == gt_term->right_term->type() and Term::Type::TERMCONSTANT == gt_term->left_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(gt_term->right_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(gt_term->left_term);
        term_type = Term::Type::LT; // for consistency, var on left, constant on right
        right_formula->SetType(Theory::ArithmeticFormula::Type::LT);
      }
      break;
    }
    case Term::Type::GE: {
      term_type = Term::Type::GE;
      right_formula->SetType(Theory::ArithmeticFormula::Type::GE);
      Ge_ptr ge_term = dynamic_cast<Ge_ptr>(term);
      if(Term::Type::QUALIDENTIFIER == ge_term->left_term->type() and Term::Type::TERMCONSTANT == ge_term->right_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(ge_term->left_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(ge_term->right_term);
      } else if(Term::Type::QUALIDENTIFIER == ge_term->right_term->type() and Term::Type::TERMCONSTANT == ge_term->left_term->type()) {
        term_qualid = dynamic_cast<QualIdentifier_ptr>(ge_term->right_term);
        term_termconstant = dynamic_cast<TermConstant_ptr>(ge_term->left_term);
        term_type = Term::Type::LE; // for consistency, var on left, constant on right
        right_formula->SetType(Theory::ArithmeticFormula::Type::LE);
      }
      break;
    }
    default: {
      break;
    }
  }
  // sanity check and variables must match
  if(term_qualid == nullptr or term_termconstant == nullptr or term_qualid->getVarName() != cond_qualid->getVarName()) {
    return false;
  }
  // now do actual analysis
  int cond_constant = std::stoi(cond_termconstant->getValue());
  int term_constant = std::stoi(term_termconstant->getValue());


  left_formula->AddVariable(cond_qualid->getVarName(),1);
  left_formula->SetConstant(-1 * cond_constant);
  right_formula->AddVariable(cond_qualid->getVarName(),1);
  right_formula->SetConstant(-1 * term_constant);

  Theory::BinaryIntAutomaton_ptr left_auto = Theory::BinaryIntAutomaton::MakeAutomaton(left_formula, not Option::Solver::USE_SIGNED_INTEGERS);
  Theory::BinaryIntAutomaton_ptr right_auto = Theory::BinaryIntAutomaton::MakeAutomaton(right_formula, not Option::Solver::USE_SIGNED_INTEGERS);

  Theory::BinaryIntAutomaton_ptr result_auto = left_auto->Intersect(right_auto);
  bool result = not result_auto->IsEmptyLanguage();

  delete left_auto;
  delete right_auto;
  delete result_auto;

  return result;

  switch(term_type) {
    case Term::Type::EQ: {
LOG(INFO) << "EQ";      
      break;
    }
    case Term::Type::NOTEQ: {
LOG(INFO) << "NOTEQ";
      break;
    }
    case Term::Type::LT: {
LOG(INFO) << "LT";
      if(is_cond_equality and cond_constant < term_constant) {
        return true;
      }
      break;
    }
    case Term::Type::LE: {
LOG(INFO) << "LE";
      if(is_cond_equality and cond_constant <= term_constant) {
        return true;
      }
      break;
    }
    case Term::Type::GT: {
LOG(INFO) << "GT";
      if(is_cond_equality and cond_constant > term_constant) {
        return true;
      }
      break;
    }
    case Term::Type::GE: {
LOG(INFO) << "GE";
      if(is_cond_equality and cond_constant >= term_constant) {
        return true;
      }
      break;
    }
    default: {
      break;
    }
  }
  LOG(INFO) << 6;
  return false;
}

bool SyntacticOptimizer::check_and_process_constant_string(std::initializer_list<SMT::Term_ptr> terms) {
  Optimization::ConstantTermChecker constant_term_checker;
  for (auto term : terms) {
    constant_term_checker.start(term, Optimization::ConstantTermChecker::Mode::ONLY_TERM_CONSTANT);
    if (constant_term_checker.is_constant()) {
      return true;
    }
  }

  return false;
}

bool SyntacticOptimizer::check_and_process_len_transformation(Term_ptr operation, Term_ptr & left_term,
                                                              Term_ptr & right_term) {
  // It may be better to solve arithmetic constraints with LIA for precision
//  if (Option::Solver::LIA_ENGINE_ENABLED) {
   
  // if(Term::Type::EQ == operation->type()) {
  //   return __check_and_process_len_transformation(operation->type(), left_term, right_term)
  //       || __check_and_process_len_transformation(syntactic_reverse_relation(operation->type()), right_term, left_term);
  //  } else {
     return false;
  //  }
//  }

}

bool SyntacticOptimizer::__check_and_process_len_transformation(Term::Type operation, Term_ptr & left_term,
                                                                Term_ptr & right_term) {
  if (Len_ptr len_ptr = dynamic_cast<Len_ptr>(left_term)) {

    if (TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(right_term)) {
      if (term_constant->getValueType() == Primitive::Type::NUMERAL) {// && Term::Type::QUALIDENTIFIER == len_ptr->term->type()) {
      	int value = std::stoi(term_constant->getValue());
      	if(value != 0) return false;
				DVLOG(VLOG_LEVEL) << "Computing len transformation";
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

        regex_template.replace(regex_template.find("%s"), 2, l_value);  // replace l
        regex_template.replace(regex_template.find("%s"), 2, r_value);  // replace r

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

Term::Type SyntacticOptimizer::syntactic_reverse_relation(Term::Type operation) {
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
bool SyntacticOptimizer::check_and_process_for_contains_transformation(Term_ptr & left_term, Term_ptr & right_term,
                                                                       int compare_value) {
  TermConstant_ptr expected_constant_term = nullptr;
  if (compare_value < 0 and Term::Type::UMINUS == right_term->type()) {
    UMinus_ptr u_minus_term = dynamic_cast<UMinus_ptr>(right_term);
    if (Term::Type::TERMCONSTANT == u_minus_term->term->type()) {
      expected_constant_term = dynamic_cast<TermConstant_ptr>(u_minus_term->term);
      compare_value = -compare_value;
    }
  } else if (Term::Type::TERMCONSTANT == right_term->type()) {
    expected_constant_term = dynamic_cast<TermConstant_ptr>(right_term);
  }


  if (expected_constant_term == nullptr or Primitive::Type::NUMERAL != expected_constant_term->getValueType()) {
    return false;
  } else if (compare_value != std::stol(expected_constant_term->getValue())) {
    return false;
  }

  if (IndexOf_ptr index_of_term = dynamic_cast<IndexOf_ptr>(left_term)) {
    if (IndexOf::Mode::DEFAULT == index_of_term->getMode()) {
      Term_ptr tmp_term = right_term;
      right_term = index_of_term->search_term;
      left_term = index_of_term->subject_term;
      index_of_term->subject_term = nullptr;
      index_of_term->search_term = nullptr;
      delete index_of_term;
      delete tmp_term;
      return true;
    }
  } else if (LastIndexOf_ptr last_index_of_term = dynamic_cast<LastIndexOf_ptr>(left_term)) {
    if (LastIndexOf::Mode::DEFAULT == last_index_of_term->getMode()) {
      Term_ptr tmp_term = right_term;
      right_term = last_index_of_term->search_term;
      left_term = last_index_of_term->subject_term;
      last_index_of_term->subject_term = nullptr;
      last_index_of_term->search_term = nullptr;
      delete last_index_of_term;
      delete tmp_term;
      return true;
    }
  }

  return false;
}

/**
 * Checks only immediate children, may need to implement more sophisticated analysis for such optimizations
 */
SubString::Mode SyntacticOptimizer::check_and_process_subString(SubString_ptr sub_string_term, Term_ptr & index_term) {
  switch (index_term->type()) {
    case Term::Type::INDEXOF: {
      IndexOf_ptr index_of_term = dynamic_cast<IndexOf_ptr>(index_term);
      if (Ast2Dot::isEquivalent(sub_string_term->subject_term, index_of_term->subject_term)) {
        switch (index_of_term->getMode()) {
          case IndexOf::Mode::DEFAULT: {
            index_term = index_of_term->search_term;
            index_of_term->search_term = nullptr;
            delete index_of_term;
            break;
          }
          case IndexOf::Mode::FROMINDEX: {
            callback_ =
                [this, sub_string_term, index_of_term, &index_term](Term_ptr & term) mutable {
                  Let_ptr let_term = this->generateLetTermFor(sub_string_term, SubString::Mode::FROMINDEX, index_of_term, index_term);
                  term = let_term;
                };
            break;
          }
          case IndexOf::Mode::FROMFIRSTOF: {
            // add callback for let construct
            callback_ =
                [this, sub_string_term, index_of_term, &index_term](Term_ptr & term) mutable {
                  Let_ptr let_term = this->generateLetTermFor(sub_string_term, SubString::Mode::FROMFIRSTOF, index_of_term, index_term);
                  term = let_term;
                };
            break;
          }
          case IndexOf::Mode::FROMLASTOF: {
            // add callback for let construct
            callback_ = [this, sub_string_term, index_of_term, &index_term](Term_ptr & term) mutable {
              // Generate string binding for local substring
                Let_ptr let_term = this->generateLetTermFor(sub_string_term, SubString::Mode::FROMLASTOF, index_of_term, index_term);
                term = let_term;
              };
            break;
          }
          default:
            break;
        }
        return SubString::Mode::FROMFIRSTOF;
      }
      break;
    }  // end of IndexOf case
    case Term::Type::LASTINDEXOF: {
      LastIndexOf_ptr last_index_of_term = dynamic_cast<LastIndexOf_ptr>(index_term);
      if (Ast2Dot::isEquivalent(sub_string_term->subject_term, last_index_of_term->subject_term)) {
        switch (last_index_of_term->getMode()) {
          case LastIndexOf::Mode::DEFAULT: {
            index_term = last_index_of_term->search_term;
            last_index_of_term->search_term = nullptr;
            delete last_index_of_term;
            break;
          }
          case LastIndexOf::Mode::FROMINDEX: {
            callback_ =
                [this, sub_string_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                  Let_ptr let_term = this->generateLetTermFor(sub_string_term, SubString::Mode::FROMINDEX, last_index_of_term, index_term);
                  term = let_term;
                };
            break;
          }
          case LastIndexOf::Mode::FROMFIRSTOF: {
            // add callback for let construct
            callback_ =
                [this, sub_string_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                  Let_ptr let_term = this->generateLetTermFor(sub_string_term, SubString::Mode::FROMFIRSTOF, last_index_of_term, index_term);
                  term = let_term;
                };
            break;
          }
          case LastIndexOf::Mode::FROMLASTOF: {
            // add callback for let construct
            callback_ = [this, sub_string_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
              // Generate string binding for local substring
                Let_ptr let_term = this->generateLetTermFor(sub_string_term, SubString::Mode::FROMLASTOF, last_index_of_term, index_term);
                term = let_term;
              };
            break;
          }
          default:
            break;
        }
        return SubString::Mode::FROMLASTOF;
      }
      break;
    }  // end LastIndexOf case
    default:
      break;
  }
  return SubString::Mode::NONE;  // do not change anything
}

SubString::Mode SyntacticOptimizer::check_and_process_subString(SubString_ptr sub_string_term,
                                                                Term_ptr & start_index_term,
                                                                Term_ptr & end_index_term) {
  SubString::Mode start_index_mode = check_and_process_subString(sub_string_term, start_index_term);
  if (callback_) {
    // first let the callback called in a new callback and visit the substring again for end index
    // decide on what to do when there is an end index
    LOG(FATAL)<< "case not handled, fix me";
  }
  SubString::Mode end_index_mode = check_and_process_subString(sub_string_term, end_index_term);

  if (SubString::Mode::FROMINDEX == start_index_mode and SubString::Mode::FROMINDEX == end_index_mode) {
    return SubString::Mode::FROMINDEXTOINDEX;
  } else if (SubString::Mode::FROMINDEX == start_index_mode and SubString::Mode::FROMFIRSTOF == end_index_mode) {
    return SubString::Mode::FROMINDEXTOFIRSTOF;
  } else if (SubString::Mode::FROMINDEX == start_index_mode and SubString::Mode::FROMLASTOF == end_index_mode) {
    return SubString::Mode::FROMINDEXTOLASTOF;
  } else if (SubString::Mode::FROMFIRSTOF == start_index_mode and SubString::Mode::FROMINDEX == end_index_mode) {
    return SubString::Mode::FROMFIRSTOFTOINDEX;
  } else if (SubString::Mode::FROMFIRSTOF == start_index_mode and SubString::Mode::FROMFIRSTOF == end_index_mode) {
    return SubString::Mode::FROMFIRSTOFTOFIRSTOF;
  } else if (SubString::Mode::FROMFIRSTOF == start_index_mode and SubString::Mode::FROMLASTOF == end_index_mode) {
    return SubString::Mode::FROMFIRSTOFTOLASTOF;
  } else if (SubString::Mode::FROMLASTOF == start_index_mode and SubString::Mode::FROMINDEX == end_index_mode) {
    return SubString::Mode::FROMLASTOFTOINDEX;
  } else if (SubString::Mode::FROMLASTOF == start_index_mode and SubString::Mode::FROMFIRSTOF == end_index_mode) {
    return SubString::Mode::FROMLASTOFTOFIRSTOF;
  } else if (SubString::Mode::FROMLASTOF == start_index_mode and SubString::Mode::FROMLASTOF == end_index_mode) {
    return SubString::Mode::FROMLASTOFTOLASTOF;
  }

  return SubString::Mode::NONE;  // do not change anything
}

Let_ptr SyntacticOptimizer::generateLetTermFor(SubString_ptr sub_string_term, SubString::Mode local_substring_mode,
                                               LastIndexOf_ptr last_index_of_term, Term_ptr & index_term) {
  Let_ptr let_term = nullptr;
  // Generate string binding for local substring
  Variable_ptr string_var = generate_local_var(Variable::Type::STRING);
  SubString_ptr str_bind_term = new SubString(sub_string_term->subject_term->clone(),
                                              last_index_of_term->from_index->clone());
  str_bind_term->setMode(local_substring_mode);
  VarBinding_ptr str_binding = new VarBinding(new Primitive(string_var->getName(), Primitive::Type::SYMBOL),
                                              str_bind_term);
  QualIdentifier_ptr binded_str_var_identifier = generate_qual_identifier(string_var->getName());

  VarBindingList_ptr var_bindings = new VarBindingList();
  var_bindings->push_back(str_binding);

  // modify substring
  delete sub_string_term->subject_term;
  sub_string_term->subject_term = binded_str_var_identifier->clone();
  index_term = last_index_of_term->search_term;
  last_index_of_term->search_term = nullptr;
  delete last_index_of_term;
  sub_string_term->setMode(SubString::Mode::FROMLASTOF);  // to be safe

  // generate let
  let_term = new Let(var_bindings, sub_string_term);
  return let_term;
}

Let_ptr SyntacticOptimizer::generateLetTermFor(SubString_ptr sub_string_term, SubString::Mode local_substring_mode,
                                               IndexOf_ptr index_of_term, Term_ptr & index_term) {
  Let_ptr let_term = nullptr;
  // Generate string binding for local substring
  Variable_ptr string_var = generate_local_var(Variable::Type::STRING);
  SubString_ptr str_bind_term = new SubString(sub_string_term->subject_term->clone(),
                                              index_of_term->from_index->clone());
  str_bind_term->setMode(local_substring_mode);
  VarBinding_ptr str_binding = new VarBinding(new Primitive(string_var->getName(), Primitive::Type::SYMBOL),
                                              str_bind_term);
  QualIdentifier_ptr binded_str_var_identifier = generate_qual_identifier(string_var->getName());

  VarBindingList_ptr var_bindings = new VarBindingList();
  var_bindings->push_back(str_binding);

  // modify substring
  delete sub_string_term->subject_term;
  sub_string_term->subject_term = binded_str_var_identifier->clone();
  index_term = index_of_term->search_term;
  index_of_term->search_term = nullptr;
  delete index_of_term;
  sub_string_term->setMode(SubString::Mode::FROMFIRSTOF);  // to be safe

  // generate let
  let_term = new Let(var_bindings, sub_string_term);
  return let_term;
}

int SyntacticOptimizer::check_and_process_index_operation(Term_ptr curent_term, Term_ptr subject_term,
                                                          Term_ptr & index_term) {
  switch (index_term->type()) {
    case Term::Type::INDEXOF: {
      IndexOf_ptr index_of_term = dynamic_cast<IndexOf_ptr>(index_term);
      if (Ast2Dot::isEquivalent(subject_term, index_of_term->subject_term)) {
        DVLOG(VLOG_LEVEL) << "'indexOf' operation mode optimization";
        switch (index_of_term->getMode()) {
          case IndexOf::Mode::DEFAULT: {
            index_term = index_of_term->search_term;
            index_of_term->search_term = nullptr;
            delete index_of_term;
            break;
          }
          case IndexOf::Mode::FROMINDEX: {
            if (IndexOf_ptr current_cast_term = dynamic_cast<IndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMINDEX, index_of_term, index_term);
                    term = let_term;
                  };
            } else if (LastIndexOf_ptr current_cast_term = dynamic_cast<LastIndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMINDEX, index_of_term, index_term);
                    term = let_term;
                  };
            }
            break;
          }
          case IndexOf::Mode::FROMFIRSTOF: {
            if (IndexOf_ptr current_cast_term = dynamic_cast<IndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMFIRSTOF, index_of_term, index_term);
                    term = let_term;
                  };
            } else if (LastIndexOf_ptr current_cast_term = dynamic_cast<LastIndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMFIRSTOF, index_of_term, index_term);
                    term = let_term;
                  };
            }
            break;
          }
          case IndexOf::Mode::FROMLASTOF: {
            if (IndexOf_ptr current_cast_term = dynamic_cast<IndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMLASTOF, index_of_term, index_term);
                    term = let_term;
                  };
            } else if (LastIndexOf_ptr current_cast_term = dynamic_cast<LastIndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMLASTOF, index_of_term, index_term);
                    term = let_term;
                  };
            }
            break;
          }
          default:
            // add let bindings for other modes of indexof operation to make it work with default mode
            LOG(FATAL)<< "implement cases where index_term is optimized index operation";
            break;
          }
        return static_cast<int>(IndexOf::Mode::FROMFIRSTOF);
      } else {
        DVLOG(VLOG_LEVEL) << "index operation optimization fails, please extend implementation";
      }
      break;
    }
    case Term::Type::LASTINDEXOF: {
      LastIndexOf_ptr last_index_of_term = dynamic_cast<LastIndexOf_ptr>(index_term);
      if (Ast2Dot::isEquivalent(subject_term, last_index_of_term->subject_term)) {
        DVLOG(VLOG_LEVEL) << "'lastIndexOf' operation mode optimization";
        switch (last_index_of_term->getMode()) {
          case LastIndexOf::Mode::DEFAULT: {
            index_term = last_index_of_term->search_term;
            last_index_of_term->search_term = nullptr;
            delete last_index_of_term;
            break;
          }
          case LastIndexOf::Mode::FROMINDEX: {
            if (IndexOf_ptr current_cast_term = dynamic_cast<IndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMINDEX, last_index_of_term, index_term);
                    term = let_term;
                  };
            } else if (LastIndexOf_ptr current_cast_term = dynamic_cast<LastIndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMINDEX, last_index_of_term, index_term);
                    term = let_term;
                  };
            }
            break;
          }
          case LastIndexOf::Mode::FROMFIRSTOF: {
            if (IndexOf_ptr current_cast_term = dynamic_cast<IndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMFIRSTOF, last_index_of_term, index_term);
                    term = let_term;
                  };
            } else if (LastIndexOf_ptr current_cast_term = dynamic_cast<LastIndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMFIRSTOF, last_index_of_term, index_term);
                    term = let_term;
                  };
            }
            break;
          }
          case LastIndexOf::Mode::FROMLASTOF: {
            if (IndexOf_ptr current_cast_term = dynamic_cast<IndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMLASTOF, last_index_of_term, index_term);
                    term = let_term;
                  };
            } else if (LastIndexOf_ptr current_cast_term = dynamic_cast<LastIndexOf_ptr>(curent_term)) {
              callback_ =
                  [this, current_cast_term, last_index_of_term, &index_term](Term_ptr & term) mutable {
                    Let_ptr let_term = this->generateLetTermFor(current_cast_term, SubString::Mode::FROMLASTOF, last_index_of_term, index_term);
                    term = let_term;
                  };
            }
            break;
          }
          default:
            // add let bindings for other modes of lastIndexof operation to make it work with default mode
            LOG(FATAL)<< "implement cases where index_term is optimized index operation";
            break;
          }
        return static_cast<int>(LastIndexOf::Mode::FROMLASTOF);
      } else {
        DVLOG(VLOG_LEVEL) << "index operation optimization fails, please extend implementation";
      }
      break;
    }
    default:
      break;
  }

  return 0;  // do not change anything
}

Let_ptr SyntacticOptimizer::generateLetTermFor(IndexOf_ptr index_of_term, SubString::Mode local_substring_mode,
                                               IndexOf_ptr param_index_of_term, Term_ptr & index_term) {
  Let_ptr let_term = nullptr;
  // Generate string binding for local substring
  Variable_ptr string_var = generate_local_var(Variable::Type::STRING);
  SubString_ptr str_bind_term = new SubString(index_of_term->subject_term->clone(),
                                              param_index_of_term->from_index->clone());
  str_bind_term->setMode(local_substring_mode);
  VarBinding_ptr str_binding = new VarBinding(new Primitive(string_var->getName(), Primitive::Type::SYMBOL),
                                              str_bind_term);
  QualIdentifier_ptr binded_str_var_identifier = generate_qual_identifier(string_var->getName());

  VarBindingList_ptr var_bindings = new VarBindingList();
  var_bindings->push_back(str_binding);

  // modify substring
  delete index_of_term->subject_term;
  index_of_term->subject_term = binded_str_var_identifier->clone();
  index_term = param_index_of_term->search_term;
  param_index_of_term->search_term = nullptr;
  delete param_index_of_term;
  index_of_term->setMode(IndexOf::Mode::FROMFIRSTOF);  // to be safe

  // generate let
  let_term = new Let(var_bindings, index_of_term);
  return let_term;
}

Let_ptr SyntacticOptimizer::generateLetTermFor(IndexOf_ptr index_of_term, SubString::Mode local_substring_mode,
                                               LastIndexOf_ptr param_last_index_of_term, Term_ptr & index_term) {
  Let_ptr let_term = nullptr;
  // Generate string binding for local substring
  Variable_ptr string_var = generate_local_var(Variable::Type::STRING);
  SubString_ptr str_bind_term = new SubString(index_of_term->subject_term->clone(),
                                              param_last_index_of_term->from_index->clone());
  str_bind_term->setMode(local_substring_mode);
  VarBinding_ptr str_binding = new VarBinding(new Primitive(string_var->getName(), Primitive::Type::SYMBOL),
                                              str_bind_term);
  QualIdentifier_ptr binded_str_var_identifier = generate_qual_identifier(string_var->getName());

  VarBindingList_ptr var_bindings = new VarBindingList();
  var_bindings->push_back(str_binding);

  // modify substring
  delete index_of_term->subject_term;
  index_of_term->subject_term = binded_str_var_identifier->clone();
  index_term = param_last_index_of_term->search_term;
  param_last_index_of_term->search_term = nullptr;
  delete param_last_index_of_term;
  index_of_term->setMode(IndexOf::Mode::FROMLASTOF);  // to be safe

  // generate let
  let_term = new Let(var_bindings, index_of_term);
  return let_term;
}

Let_ptr SyntacticOptimizer::generateLetTermFor(LastIndexOf_ptr last_index_of_term, SubString::Mode local_substring_mode,
                                               IndexOf_ptr param_index_of_term, Term_ptr & index_term) {
  Let_ptr let_term = nullptr;
  // Generate string binding for local substring
  Variable_ptr string_var = generate_local_var(Variable::Type::STRING);
  SubString_ptr str_bind_term = new SubString(last_index_of_term->subject_term->clone(),
                                              param_index_of_term->from_index->clone());
  str_bind_term->setMode(local_substring_mode);
  VarBinding_ptr str_binding = new VarBinding(new Primitive(string_var->getName(), Primitive::Type::SYMBOL),
                                              str_bind_term);
  QualIdentifier_ptr binded_str_var_identifier = generate_qual_identifier(string_var->getName());

  VarBindingList_ptr var_bindings = new VarBindingList();
  var_bindings->push_back(str_binding);

  // modify substring
  delete last_index_of_term->subject_term;
  last_index_of_term->subject_term = binded_str_var_identifier->clone();
  index_term = param_index_of_term->search_term;
  param_index_of_term->search_term = nullptr;
  delete param_index_of_term;
  last_index_of_term->setMode(LastIndexOf::Mode::FROMFIRSTOF);  // to be safe

  // generate let
  let_term = new Let(var_bindings, last_index_of_term);
  return let_term;
}

Let_ptr SyntacticOptimizer::generateLetTermFor(LastIndexOf_ptr last_index_of_term, SubString::Mode local_substring_mode,
                                               LastIndexOf_ptr param_last_index_of_term, Term_ptr & index_term) {
  Let_ptr let_term = nullptr;
  // Generate string binding for local substring
  Variable_ptr string_var = generate_local_var(Variable::Type::STRING);
  SubString_ptr str_bind_term = new SubString(last_index_of_term->subject_term->clone(),
                                              param_last_index_of_term->from_index->clone());
  str_bind_term->setMode(local_substring_mode);
  VarBinding_ptr str_binding = new VarBinding(new Primitive(string_var->getName(), Primitive::Type::SYMBOL),
                                              str_bind_term);
  QualIdentifier_ptr binded_str_var_identifier = generate_qual_identifier(string_var->getName());

  VarBindingList_ptr var_bindings = new VarBindingList();
  var_bindings->push_back(str_binding);

  // modify substring
  delete last_index_of_term->subject_term;
  last_index_of_term->subject_term = binded_str_var_identifier->clone();
  index_term = param_last_index_of_term->search_term;
  param_last_index_of_term->search_term = nullptr;
  delete param_last_index_of_term;
  last_index_of_term->setMode(LastIndexOf::Mode::FROMLASTOF);  // to be safe

  // generate let
  let_term = new Let(var_bindings, last_index_of_term);
  return let_term;
}

Term_ptr SyntacticOptimizer::generate_term_constant(std::string data, Primitive::Type type) {
  return new TermConstant(new Primitive(data, type));
}

void SyntacticOptimizer::add_callback_to_replace_with_bool(Term_ptr term, bool value) {
  DVLOG(VLOG_LEVEL) << "Replacing with '" << std::boolalpha << value << "': '" << *term << "'";
  std::stringstream ss;
  ss << std::boolalpha << value;
  std::string term_value = ss.str();
  callback_ = [this, term, term_value](Term_ptr & ref_term) mutable {
    ref_term = generate_term_constant(term_value, Primitive::Type::BOOL);
    if(term_value == "true") {
    	symbol_table_->refactor_scope(term,ref_term);
    }
    delete term;
  };
}

bool SyntacticOptimizer::check_bool_term(Term_ptr term) {
	QualIdentifier_ptr qi_term = dynamic_cast<QualIdentifier_ptr>(term);
	if(qi_term) {
		Variable_ptr var = symbol_table_->get_variable(qi_term->getVarName());
		if(Variable::Type::BOOL == var->getType()) {
			return true;
		}
	}
	return false;
}

Eq_ptr SyntacticOptimizer::generate_eq_bool_constant(Term_ptr term, std::string value) {
	QualIdentifier_ptr qi_term = dynamic_cast<QualIdentifier_ptr>(term);
	Primitive_ptr prim = new Primitive(value,Primitive::Type::BOOL);
	TermConstant_ptr term_constant = new TermConstant(prim);
	Eq_ptr eq_term = new Eq(qi_term->clone(),term_constant);
	return eq_term;
}

bool SyntacticOptimizer::check_bool_constant_value(Term_ptr term, std::string value) {
  if (Term::Type::TERMCONSTANT == term->type()) {
    TermConstant_ptr term_constant = dynamic_cast<TermConstant_ptr>(term);
    if (Primitive::Type::BOOL == term_constant->getValueType() and value == term_constant->getValue()) {
      return true;
    }
  }

  return false;
}

//Function to match and remove the longest shared prefix of two terms
bool SyntacticOptimizer::match_prefix(Term_ptr left, Term_ptr right) {
  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;
  constant_term_checker_left.start(left, Optimization::ConstantTermChecker::Mode::PREFIX);
  constant_term_checker_right.start(right, Optimization::ConstantTermChecker::Mode::PREFIX);

  //If both are not constant prefixes no matching can be done
  if (!constant_term_checker_right.is_constant_string() or !constant_term_checker_left.is_constant_string()) {
    return true;
  } else {
    std::string left_value = constant_term_checker_left.get_constant_string();
    std::string right_value = constant_term_checker_right.get_constant_string();
    if (left_value.size() <= right_value.size()) {
      if (equal(left_value.begin(), left_value.end(), right_value.begin())) {  //check if the smaller is a prefix of the larger.
        //If so, remove the prefix appropriately
        Optimization::ConstantTermOptimization term_matcher_left;
        term_matcher_left.start(left, left_value.size(), Optimization::ConstantTermOptimization::Mode::PREFIX);
        Optimization::ConstantTermOptimization term_matcher_right;
        term_matcher_right.start(right, left_value.size(), Optimization::ConstantTermOptimization::Mode::PREFIX);
        return true;
      } else {
        return false;
      }
    } else {
      if (equal(right_value.begin(), right_value.end(), left_value.begin())) {
        Optimization::ConstantTermOptimization term_matcher_left;
        term_matcher_left.start(left, right_value.size(), Optimization::ConstantTermOptimization::Mode::PREFIX);
        Optimization::ConstantTermOptimization term_matcher_right;
        term_matcher_right.start(right, right_value.size(), Optimization::ConstantTermOptimization::Mode::PREFIX);
        return true;
      } else {
        return false;
      }
    }
  }
  return true;
}

//Function to match and remove the longest shared suffix of two terms
bool SyntacticOptimizer::match_suffix(Term_ptr left, Term_ptr right) {
  Optimization::ConstantTermChecker constant_term_checker_left;
  Optimization::ConstantTermChecker constant_term_checker_right;
  constant_term_checker_left.start(left, Optimization::ConstantTermChecker::Mode::SUFFIX);
  constant_term_checker_right.start(right, Optimization::ConstantTermChecker::Mode::SUFFIX);

  //If both are not constant prefixes no matching can be done
  if (!constant_term_checker_right.is_constant_string() or !constant_term_checker_left.is_constant_string()) {
    return true;
  } else {
    std::string left_value = constant_term_checker_left.get_constant_string();
    std::string right_value = constant_term_checker_right.get_constant_string();
    if (left_value.size() <= right_value.size()) {
      if (equal(left_value.rbegin(), left_value.rend(), right_value.rbegin())) {  //check if the smaller is a suffix of the larger.
        //If so, remove the prefix appropriately
        Optimization::ConstantTermOptimization term_matcher_left;
        term_matcher_left.start(left, left_value.size(), Optimization::ConstantTermOptimization::Mode::SUFFIX);
        Optimization::ConstantTermOptimization term_matcher_right;
        term_matcher_right.start(right, left_value.size(), Optimization::ConstantTermOptimization::Mode::SUFFIX);
        return true;
      } else {
        return false;
      }
    } else {
      if (equal(right_value.rbegin(), right_value.rend(), left_value.rbegin())) {
        Optimization::ConstantTermOptimization term_matcher_left;
        term_matcher_left.start(left, right_value.size(), Optimization::ConstantTermOptimization::Mode::SUFFIX);
        Optimization::ConstantTermOptimization term_matcher_right;
        term_matcher_right.start(right, right_value.size(), Optimization::ConstantTermOptimization::Mode::SUFFIX);
        return true;
      } else {
        return false;
      }
    }
  }
  return true;
}

void SyntacticOptimizer::record_ite_relation(Term_ptr term) {
	// term must be an OR after ite transformation
	Or_ptr or_term = dynamic_cast<Or_ptr>(term);
	// left child must be AND term corresponding to then branch
	And_ptr then_branch = dynamic_cast<And_ptr>(or_term->term_list->at(0));
	// right child must be AND term corresponding to else branch
	And_ptr else_branch = dynamic_cast<And_ptr>(or_term->term_list->at(1));
	// first then_branch child corresponds to ite_then_condition
	Term_ptr then_condition = then_branch->term_list->at(0)->clone();
	// first else_branch child corresponds to ite_else_condition
	Term_ptr else_condition = else_branch->term_list->at(0)->clone();
	symbol_table_->add_or_ite(term,then_condition,else_condition);
}

/**
 * TODO Let symbol table to generate names
 */
Variable_ptr SyntacticOptimizer::generate_local_var(Variable::Type type) {
  Variable_ptr variable = nullptr;
  std::stringstream local_var_name;
  local_var_name << Variable::LOCAL_VAR_PREFIX << name_counter++;
  variable = new Variable(local_var_name.str(), type);
  symbol_table_->add_variable(variable);
  return variable;
}

QualIdentifier_ptr SyntacticOptimizer::generate_qual_identifier(std::string var_name) {
  return new QualIdentifier(new Identifier(new Primitive(var_name, Primitive::Type::SYMBOL)));
}

} /* namespace Solver */
} /* namespace Vlab */

