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

#include "smt/typedefs.h"
#include "AstTraverser.h"
#include "Component.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {
class DependencySlicer : public AstTraverser {
 public:
  DependencySlicer(SMT::Script_ptr, SymbolTable_ptr);
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
  std::vector<Component_ptr> GetComponentsFor(SMT::TermList_ptr);

  int number_of_components_;
  SymbolTable_ptr symbol_table_;
  SMT::Term_ptr current_term_;
  std::map<SMT::Term_ptr, std::set<SMT::Variable_ptr>> term_variable_map_;
 private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_DEPENDENCYSLICER_H_ */
