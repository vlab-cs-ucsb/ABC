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

#include "../smt/typedefs.h"
#include "solver/AstTraverser.h"
#include "solver/ConstraintInformation.h"
#include "solver/SymbolTable.h"

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
