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

} /* namespace Solver */
} /* namespace Vlab */

