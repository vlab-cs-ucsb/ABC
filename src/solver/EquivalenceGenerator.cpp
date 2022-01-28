/*
 * EquivalenceGenerator.cpp
 *
  *  Created on: May 4, 2015
 *      Author: baki, tegan
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "EquivalenceGenerator.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int EquivalenceGenerator::VLOG_LEVEL = 19;

EquivalenceGenerator::EquivalenceGenerator(Script_ptr script, SymbolTable_ptr symbol_table)
    : AstTraverser(script),
      has_constant_substitution_(false),
      symbol_table_(symbol_table),
      left_variable_{nullptr},
      right_variable_{nullptr},
      term_constant_{nullptr},
      unclassified_term_{nullptr} {
  setCallbacks();
  sub_term  =false;
}

EquivalenceGenerator::~EquivalenceGenerator() {
}

void EquivalenceGenerator::start() {
  DVLOG(VLOG_LEVEL) << "Starting the EquivalenceGenerator";
  has_constant_substitution_ = false;
  symbol_table_->push_scope(root_, false);
  visitScript(root_);
  symbol_table_->pop_scope();
  end();
}

void EquivalenceGenerator::end() {
#ifndef NDEBUG
  if (VLOG_IS_ON(VLOG_LEVEL)) {
    for(auto& table_entry : symbol_table_->get_equivalance_class_table()) {
      DVLOG(VLOG_LEVEL) << " equivalence scope: " << "@" << table_entry.first;
      std::set<EquivalenceClass_ptr> unique_ones;
      for (auto& map_entry : table_entry.second) {
        unique_ones.insert(map_entry.second);
      }
      for (auto equiv : unique_ones) {
        DVLOG(VLOG_LEVEL) << " equivalence: " << *equiv;
      }
    }
  }
#endif

  EquivClassRuleRunner rule_runner(root_, symbol_table_);
  rule_runner.start();
}

void EquivalenceGenerator::setCallbacks() {
  auto term_callback = [] (Term_ptr term) -> bool {
    return false;
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

/**
 * Visit children that are not disjunction first
 */
void EquivalenceGenerator::visitAnd(And_ptr and_term) {
  TermList or_terms;
  for (auto term : *(and_term->term_list)) {
    if (Term::Type::OR not_eq term->type()) {
      visit(term);
    } else {
      or_terms.push_back(term);
    }
  }

  if(!has_constant_substitution_) {
  	sub_term = true;
  	for (auto term : *(and_term->term_list)) {
			if (Term::Type::OR not_eq term->type()) {
				visit(term);
			}
//			else {
//				or_terms.push_back(term);
//			}
		}

  	for (auto term : or_terms) {
			visit(term);
		}
  	sub_term = false;
  }
}

void EquivalenceGenerator::visitOr(Or_ptr or_term) {
  for (auto term : *(or_term->term_list)) {
  	if(term->type() == Term::Type::AND) {
			symbol_table_->push_scope(term, false);
			visit(term);
			symbol_table_->pop_scope();
  	}
  }
}

/**
 * conditions sets member variables based on the conditions
 * @left_variable_, @right_variable_, @term_constant_, @unclassified_term_
 */
void EquivalenceGenerator::visitEq(Eq_ptr eq_term) {
  DVLOG(VLOG_LEVEL) << "visit start: " << *eq_term << "@" << eq_term;

  if (!sub_term and is_equiv_of_variables(eq_term->left_term, eq_term->right_term)) {
    auto left_equiv_class = symbol_table_->get_equivalence_class_of(left_variable_);
    auto right_equiv_class = symbol_table_->get_equivalence_class_of(right_variable_);
    if (left_equiv_class and right_equiv_class) { // merge them
      update_equiv_class_and_symbol_table(left_equiv_class, right_equiv_class);
    } else if (left_equiv_class) { // add right variable
      update_equiv_class_and_symbol_table(left_equiv_class, right_variable_);
    } else if (right_equiv_class) { // add left variable
      update_equiv_class_and_symbol_table(right_equiv_class, left_variable_);
    } else { // create a new equivalence class
      create_equiv_class_and_update_symbol_table(left_variable_, right_variable_);
    }
  }
  else if (!sub_term and is_equiv_of_variable_and_constant(eq_term->left_term, eq_term->right_term)) {
    auto equiv_class = symbol_table_->get_equivalence_class_of(left_variable_);
    if (equiv_class) {
    	has_constant_substitution_ = true;
      update_equiv_class_and_symbol_table(equiv_class, term_constant_);
    } else if(equiv_class == nullptr) {
    	has_constant_substitution_ = true;
      create_equiv_class_and_update_symbol_table(left_variable_, term_constant_);
    }
  }
  else if (sub_term and is_equiv_of_bool_var_and_term(eq_term->left_term, eq_term->right_term)) {
  	has_constant_substitution_ = true;
    auto equiv_class = symbol_table_->get_equivalence_class_of(left_variable_);
    if (equiv_class) {
      update_equiv_class_and_symbol_table(equiv_class, unclassified_term_);
    } else {
      create_equiv_class_and_update_symbol_table(left_variable_, unclassified_term_);
    }
  } else { // equivalence of other terms, cannot handle for now

  }

  left_variable_ = nullptr;
  right_variable_ = nullptr;
  term_constant_ = nullptr;
  unclassified_term_ = nullptr;

  DVLOG(VLOG_LEVEL) << "visit end: " << *eq_term << "@" << eq_term;
}

bool EquivalenceGenerator::has_constant_substitution() {
  return has_constant_substitution_;
}

/**
 * checks and sets members variables @left_variable_, @right_variable based on result
 */
bool EquivalenceGenerator::is_equiv_of_variables(SMT::Term_ptr left_term, SMT::Term_ptr right_term) {
  if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(left_term)) {
    if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(right_term)) {
      left_variable_ = symbol_table_->get_variable(left_id->getVarName());
      right_variable_ = symbol_table_->get_variable(right_id->getVarName());
      DVLOG(VLOG_LEVEL)<< "variable equivalence: " << left_variable_->getName() << " = " << right_variable_->getName();
      return true;
    }
  }
  return false;
}

/**
 * When true saves variable in @left_variable_ member and saves constant in @term_constant_ member
 */
bool EquivalenceGenerator::is_equiv_of_variable_and_constant(SMT::Term_ptr left_term, SMT::Term_ptr right_term) {
  //return false;
  Optimization::ConstantTermChecker constant_term_checker;
  if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(left_term)) {
    constant_term_checker.start(right_term, Optimization::ConstantTermChecker::Mode::ONLY_TERM_CONSTANT);
    if (constant_term_checker.is_constant()) {
      left_variable_ = symbol_table_->get_variable(left_id->getVarName());
      term_constant_ = constant_term_checker.get_term_constant();
      DVLOG(VLOG_LEVEL)<< "variable to constant equivalence: " << left_variable_->getName() << " = " << term_constant_->getValue();
      return true;
    }
  } else if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(right_term)) {
    constant_term_checker.start(left_term, Optimization::ConstantTermChecker::Mode::ONLY_TERM_CONSTANT);
    if (constant_term_checker.is_constant()) {
      left_variable_ = symbol_table_->get_variable(right_id->getVarName()); // we use @left_variable_ member in that case
      term_constant_ = constant_term_checker.get_term_constant();
      DVLOG(VLOG_LEVEL)<< "variable to constant equivalence: " << left_variable_->getName() << " = " << term_constant_->getValue();
      return true;
    }
  }
  return false;
}

/**
 * We can replace bool variables with the terms they are assigned
 * Assumes you already checked for equivalence of variables
 */
bool EquivalenceGenerator::is_equiv_of_bool_var_and_term(SMT::Term_ptr left_term, SMT::Term_ptr right_term) {
  if (QualIdentifier_ptr left_id = dynamic_cast<QualIdentifier_ptr>(left_term)) {
    auto variable = symbol_table_->get_variable(left_id->getVarName());
    auto rep_var = symbol_table_->get_representative_variable_of_at_scope(symbol_table_->top_scope(),variable);
    if (Variable::Type::BOOL == variable->getType()) {
      left_variable_ = variable;
      unclassified_term_ = right_term;
      DVLOG(VLOG_LEVEL)<< "bool variable to term equivalence: " << left_variable_->getName() << " = " << *unclassified_term_;
      return true;
    }
    // if we're simply counting query variable, no need to keep terms which are essentially "macros"
    // i.e., only used in equality once and substituted everywhere else
    else if(Option::Solver::CONCAT_COLLAPSE_HEURISTIC and symbol_table_->is_macro_variable(variable->getName())) { // and symbol_table_->has_count_variable()) {
      
      auto count_var = symbol_table_->get_count_variable();
      auto rep_count_var = symbol_table_->get_representative_variable_of_at_scope(symbol_table_->top_scope(),count_var);
      if(rep_var->getName() == rep_count_var->getName()) {
        return false;
      }


    if(Concat_ptr right_id = dynamic_cast<Concat_ptr>(right_term)) {
      if(right_id->term_list->at(0)->type() == Term::Type::QUALIDENTIFIER and right_id->term_list->at(1)->type() == Term::Type::TERMCONSTANT) {
        return false;
      }
    }

      left_variable_ = variable;
      unclassified_term_ = right_term;
      DVLOG(VLOG_LEVEL)<< "non-bool variable to term equivalence: " << left_variable_->getName() << " = " << *unclassified_term_;
      return true;
    }

  } else if (QualIdentifier_ptr right_id = dynamic_cast<QualIdentifier_ptr>(right_term)) {
    auto variable = symbol_table_->get_variable(right_id->getVarName());
    if (Variable::Type::BOOL == variable->getType()) {
      left_variable_ = variable; // we use @left_variable_ member in that case
      unclassified_term_ = left_term;
      DVLOG(VLOG_LEVEL)<< "bool variable to term equivalence: " << left_variable_->getName() << " = " << *unclassified_term_;
      return true;
    }
  }
  return false;
}

void EquivalenceGenerator::update_equiv_class_and_symbol_table(EquivalenceClass_ptr left_equiv,
                                                               EquivalenceClass_ptr right_equiv) {
//  DVLOG(VLOG_LEVEL)<< "merge: " << *left_equiv << " U " << *right_equiv;
  left_equiv->merge(right_equiv);
  for (auto variable : right_equiv->get_variables()) {
    symbol_table_->add_variable_equiv_class_mapping(variable, left_equiv);
  }
  delete right_equiv;
}

void EquivalenceGenerator::update_equiv_class_and_symbol_table(EquivalenceClass_ptr equiv, SMT::Variable_ptr variable) {
//  DVLOG(VLOG_LEVEL)<< "add variable: " << variable->getName() << " >> " << *equiv;
  equiv->add(variable);
  symbol_table_->add_variable_equiv_class_mapping(variable, equiv);
}

void EquivalenceGenerator::update_equiv_class_and_symbol_table(EquivalenceClass_ptr equiv, SMT::TermConstant_ptr term_constant) {
//  DVLOG(VLOG_LEVEL)<< "constant: \"" << term_constant->getValue() << "\" >> " << *equiv;
  equiv->add(term_constant);
}

void EquivalenceGenerator::update_equiv_class_and_symbol_table(EquivalenceClass_ptr equiv, SMT::Term_ptr term) {
  DVLOG(VLOG_LEVEL)<< "add term: " << *term << " >> " << *equiv;
  equiv->add(term);
}

void EquivalenceGenerator::create_equiv_class_and_update_symbol_table(SMT::Variable_ptr left_variable,
                                                                      SMT::Variable_ptr right_variable) {
  auto equiv = new EquivalenceClass(left_variable, right_variable);
  symbol_table_->add_variable_equiv_class_mapping(left_variable, equiv);
  symbol_table_->add_variable_equiv_class_mapping(right_variable, equiv);
}

void EquivalenceGenerator::create_equiv_class_and_update_symbol_table(SMT::Variable_ptr variable, SMT::TermConstant_ptr term_constant) {
  auto equiv = new EquivalenceClass(variable, term_constant);
  symbol_table_->add_variable_equiv_class_mapping(variable, equiv);
}

void EquivalenceGenerator::create_equiv_class_and_update_symbol_table(SMT::Variable_ptr variable, SMT::Term_ptr term) {
  auto equiv = new EquivalenceClass(variable, term);
  symbol_table_->add_variable_equiv_class_mapping(variable, equiv);
}

} /* namespace Solver */
} /* namespace Vlab */

