/*
 * EquivalenceClass.h
 *
 *  Created on: Jun 27, 2016
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved. 
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#ifndef SRC_SOLVER_EQUIVALENCECLASS_H_
#define SRC_SOLVER_EQUIVALENCECLASS_H_

#include <iostream>
#include <set>
#include <string>
#include <sstream>

#include "smt/ast.h"

namespace Vlab {
namespace Solver {

class EquivalenceClass;
using EquivalenceClass_ptr = EquivalenceClass*;

class EquivalenceClass {
 public:
  EquivalenceClass(SMT::Variable_ptr v1, SMT::Term_ptr term);
  EquivalenceClass(SMT::Variable_ptr v1, SMT::TermConstant_ptr term_constant);
  EquivalenceClass(SMT::Variable_ptr v1, SMT::Variable_ptr v2);
  virtual ~EquivalenceClass();

  EquivalenceClass(const EquivalenceClass&);
  EquivalenceClass_ptr clone() const;

  bool has_constant() const;
  std::string str() const;
  void add(SMT::Variable_ptr variable);
  void add(SMT::TermConstant_ptr constant);
  void add(SMT::Term_ptr unclassified_term);

  int get_number_of_variables();
  std::set<SMT::Variable_ptr>& get_variables();

  void merge(EquivalenceClass_ptr other);


  friend std::ostream& operator<<(std::ostream& os, const EquivalenceClass& equiv_class);
 protected:
  SMT::Variable::Type type_;

  /**
   * at least one variable is selected as a representative
   */
  SMT::Variable_ptr representative_variable_;

  /**
   * a representative term can be representative variable or a constant term or an unclassified term
   * It is used for substitution on AST.
   */
  SMT::Term_ptr representative_term_;

  std::string rep_string; // kept for debugging
  std::set<SMT::Variable_ptr> variables_;
  std::set<SMT::TermConstant_ptr> constants_;
  std::set<SMT::Term_ptr> unclassified_terms_;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_EQUIVALENCECLASS_H_ */
