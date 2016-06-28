/*
 * EquivalenceClass.cpp
 *
 *  Created on: Jun 27, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "EquivalenceClass.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

EquivalenceClass::EquivalenceClass(Variable_ptr v1, Term_ptr term) {
  type_ = v1->getType();
  representative_variable_ = v1;
  representative_term_ = term->clone();
  rep_string = term->str();
  variables_.insert(v1);
  unclassified_terms_.insert(term);
}

EquivalenceClass::EquivalenceClass(Variable_ptr v1, TermConstant_ptr term_constant) {
  type_ = v1->getType();
  representative_variable_ = v1;
  representative_term_ = term_constant->clone();
  rep_string = term_constant->getValue();
  variables_.insert(v1);
  constants_.insert(term_constant);
}

EquivalenceClass::EquivalenceClass(Variable_ptr v1, Variable_ptr v2) {
  type_ = v1->getType();
  representative_variable_ = v1;
  representative_term_ = new QualIdentifier(new Identifier(new Primitive(v1->getName(), Primitive::Type::SYMBOL)));
  rep_string = v1->getName();
  variables_.insert(v1);
  variables_.insert(v2);
}

EquivalenceClass::~EquivalenceClass() {
  delete representative_term_;
}

EquivalenceClass::EquivalenceClass(const EquivalenceClass& other)
    : type_ { other.type_ },
      representative_variable_ { other.representative_variable_ } {
  representative_term_ = other.representative_term_->clone();
  variables_ = other.variables_;
  constants_ = other.constants_;
  unclassified_terms_ = other.unclassified_terms_;
}

EquivalenceClass_ptr EquivalenceClass::clone() const {
  return new EquivalenceClass(*this);
}

Variable::Type EquivalenceClass::get_type() {
  return type_;
}

bool EquivalenceClass::has_constant() const {
  return false;
}

std::string EquivalenceClass::str() const {
  std::stringstream ss;

  ss << "id variable: " << representative_variable_->getName();
  ss << " - replacement: " << rep_string << " ==> ";
  for (auto var : variables_) {
    ss << var->getName() << " ";
  }
  for (auto c : constants_) {
    ss << "\"" << c->getValue() << "\" ";
  }

  for (auto t : unclassified_terms_) {
    ss << *t << " ";
  }
  return ss.str();
}

void EquivalenceClass::add(Variable_ptr variable) {
  variables_.insert(variable);
}

/**
 * a constant is always preferred as representative term
 */
void EquivalenceClass::add(TermConstant_ptr constant) {
  bool can_update_representative_term_to_constant = false;
  if (constants_.size() == 0) {
    can_update_representative_term_to_constant = true;
  }
  constants_.insert(constant);
  // if we do not have a constant but now if we do, update representative term
  if (can_update_representative_term_to_constant) {
    delete representative_term_;
    auto rep_constant = (*(constants_.begin()));
    representative_term_ = rep_constant->clone();
    rep_string = rep_constant->getValue();
  }
}

/**
 * This case happens only for boolean terms
 * if there is no any constant, an unclassified term  can be representative term
 */
void EquivalenceClass::add(Term_ptr unclassified_term) {
  bool can_update_representative_term = false;
  if (constants_.size() == 0 and unclassified_terms_.size() == 0) {
    can_update_representative_term = true;
  }
  unclassified_terms_.insert(unclassified_term);
  if (can_update_representative_term) {
    delete representative_term_;
    representative_term_ = (*(unclassified_terms_.begin()))->clone();
    rep_string = representative_term_->str();
  }
}

int EquivalenceClass::get_number_of_variables() {
  return variables_.size();
}

std::set<Variable_ptr>& EquivalenceClass::get_variables() {
  return variables_;
}

Variable_ptr EquivalenceClass::get_representative_variable() {
  return representative_variable_;
}

Term_ptr EquivalenceClass::get_representative_term() {
  return representative_term_;
}

/**
 * Do not change representative variable
 * Do not change representative term unless there is a constant
 */
void EquivalenceClass::merge(EquivalenceClass_ptr other) {
  bool can_update_representative_term_to_constant = false;
  bool can_update_representative_term_to_unclassified_term = false;
  if (constants_.size() == 0) {
    can_update_representative_term_to_constant = true;
    if (unclassified_terms_.size() == 0) {
      can_update_representative_term_to_unclassified_term = true;
    }
  }

  variables_.insert(other->variables_.begin(), other->variables_.end());
  constants_.insert(other->constants_.begin(), other->constants_.end());
  unclassified_terms_.insert(other->unclassified_terms_.begin(), other->unclassified_terms_.end());

  // if we do not have a constant but now if we do, update representative term
  if (can_update_representative_term_to_constant and constants_.size() > 0) {
    delete representative_term_;
    auto rep_constant = (*(constants_.begin()));
    representative_term_ = rep_constant->clone();
    rep_string = rep_constant->getValue();
  } else if (can_update_representative_term_to_unclassified_term and unclassified_terms_.size() > 0) {
    delete representative_term_;
    representative_term_ = (*(unclassified_terms_.begin()))->clone();
    rep_string = representative_term_->str();
  }
}

std::ostream& operator<<(std::ostream& os, const EquivalenceClass& equiv_class) {
  return os << equiv_class.str();
}

} /* namespace Solver */
} /* namespace Vlab */
