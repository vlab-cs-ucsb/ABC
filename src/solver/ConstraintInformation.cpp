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

bool ConstraintInformation::is_component(Visitable_ptr node) {
  auto entry = components_.find(node);
  return (entry not_eq components_.end());
}

void ConstraintInformation::add_component(Visitable_ptr node) {
  components_.insert(node);
}

void ConstraintInformation::remove_component(Visitable_ptr node) {
  components_.erase(node);
}

std::set<Visitable_ptr> ConstraintInformation::get_components(){
	return components_;
}


} /* namespace Solver */
} /* namespace Vlab */
