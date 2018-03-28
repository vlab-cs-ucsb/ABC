/*
 * ConstraintInformation.cpp
 *
 *  Created on: Jun 7, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "ConstraintInformation.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

ConstraintInformation::ConstraintInformation() {
  // TODO Auto-generated constructor stub
}

ConstraintInformation::~ConstraintInformation() {
  // TODO Auto-generated destructor stub
	std::set<Theory::StringFormula_ptr> formulas_to_delete;
	for(auto &it : string_formulas) {
		if(it.second != nullptr) {
			formulas_to_delete.insert(it.second);
			it.second = nullptr;
		}
	}
	string_formulas.clear();

	for(auto &it : formulas_to_delete) {
		delete it;
	}
}

bool ConstraintInformation::is_component(const Visitable_ptr node) const {
  return (components_.find(node) not_eq components_.end());
}

void ConstraintInformation::add_component(const Visitable_ptr node) {
  components_.insert(node);
}

void ConstraintInformation::remove_component(const Visitable_ptr node) {
  components_.erase(node);
}

const std::set<Visitable_ptr> ConstraintInformation::get_components() const {
	return components_;
}

bool ConstraintInformation::has_arithmetic_constraint(const Visitable_ptr node) const {
  return (arithmetic_constraints_.find(node) not_eq arithmetic_constraints_.end());
}

void ConstraintInformation::add_arithmetic_constraint(const Visitable_ptr node) {
  arithmetic_constraints_.insert(node);
}

bool ConstraintInformation::has_string_constraint(const Visitable_ptr node) const {
  return (string_constraints_.find(node) not_eq string_constraints_.end());
}

void ConstraintInformation::add_string_constraint(const Visitable_ptr node) {
  string_constraints_.insert(node);
}

bool ConstraintInformation::has_mixed_constraint(const SMT::Visitable_ptr node) const {
  return (mixed_constraints_.find(node) not_eq mixed_constraints_.end());
}

void ConstraintInformation::add_mixed_constraint(const SMT::Visitable_ptr node) {
  mixed_constraints_.insert(node);
}

bool ConstraintInformation::var_has_formula(std::string var_name) {
	return string_formulas.find(var_name) != string_formulas.end();
}

Theory::StringFormula_ptr ConstraintInformation::get_var_formula(std::string var_name) {
	if(string_formulas.find(var_name) != string_formulas.end()) {
		return string_formulas[var_name];
	}
	return nullptr;
}

void ConstraintInformation::set_var_formula(std::string var_name,Theory::StringFormula_ptr var_formula) {
	string_formulas[var_name] = var_formula;
}

void ConstraintInformation::add_var_constraint(SMT::Variable_ptr variable, SMT::Term_ptr term_ptr) {
	var_constraints[variable].insert(term_ptr);
}

std::set<SMT::Term_ptr> ConstraintInformation::get_var_constraints(SMT::Variable_ptr variable) {
	return var_constraints[variable];
}

} /* namespace Solver */
} /* namespace Vlab */

