/*
 * DependencySlicer.h
 *
 *  Created on: May 18, 2015
 *      Author: baki
 */

#ifndef SOLVER_DEPENDENCYSLICER_H_
#define SOLVER_DEPENDENCYSLICER_H_

#include <map>
#include <set>
#include <vector>
#include <cstdbool>
#include <iostream>
#include <iterator>
#include <string>
#include <utility>

#include <glog/logging.h>
#include <glog/vlog_is_on.h>

#include "../smt/typedefs.h"
#include "../smt/ast.h"
#include "../smt/Visitor.h"
#include "../utils/List.h"
#include "AstTraverser.h"
#include "ConstraintInformation.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {
class DependencySlicer : public AstTraverser {
 public:
  DependencySlicer(SMT::Script_ptr, SymbolTable_ptr, ConstraintInformation_ptr);
  virtual ~DependencySlicer();
  void start() override;
  void end() override;
  void setCallbacks();

  void visitAssert(SMT::Assert_ptr) override;
  void visitAnd(SMT::And_ptr) override;
  void visitOr(SMT::Or_ptr) override;
  void visitQualIdentifier(SMT::QualIdentifier_ptr) override;


 protected:
  void add_variable_current_term_mapping(SMT::Variable_ptr);
  void clear_mappings();
  std::vector<SMT::TermList_ptr> GetComponentsFor(SMT::TermList_ptr);

  SymbolTable_ptr symbol_table_;
  ConstraintInformation_ptr constraint_information_;
  SMT::Term_ptr current_term_;
  std::map<SMT::Term_ptr, std::set<SMT::Variable_ptr>> term_variable_map_;
  std::map<SMT::Variable_ptr, std::set<SMT::Term_ptr>> variable_term_map_;
 private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_DEPENDENCYSLICER_H_ */
