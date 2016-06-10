//
// Created by will on 3/4/16.
//

#ifndef SRC_STRINGCONSTRAINTSOLVER_H
#define SRC_STRINGCONSTRAINTSOLVER_H

#include <map>

#include <glog/logging.h>

#include "theory/MultiTrackAutomaton.h"
#include "theory/StringAutomaton.h"
#include "StringRelationGenerator.h"
#include "AstTraverser.h"
#include "smt/ast.h"
#include "SymbolTable.h"
#include "Value.h"
#include "smt/typedefs.h"

namespace Vlab {
namespace Solver {

class StringConstraintSolver: public AstTraverser {
  typedef std::map<SMT::Term_ptr, Value_ptr> TermValueMap; // holds multitrack
public:
  StringConstraintSolver(SMT::Script_ptr, SymbolTable_ptr);
  virtual ~StringConstraintSolver();

  void start();
  void end();

  void setCallbacks();

  void visitScript(SMT::Script_ptr);
  void visitAssert(SMT::Assert_ptr);
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void visitConcat(SMT::Concat_ptr);
  void visitIn(SMT::In_ptr);
  void visitNotIn(SMT::NotIn_ptr);
  void visitLen(SMT::Len_ptr);
  void visitContains(SMT::Contains_ptr);
  void visitNotContains(SMT::NotContains_ptr);
  void visitBegins(SMT::Begins_ptr);
  void visitNotBegins(SMT::NotBegins_ptr);
  void visitEnds(SMT::Ends_ptr);
  void visitNotEnds(SMT::NotEnds_ptr);
  void visitIndexOf(SMT::IndexOf_ptr);
  void visitLastIndexOf(SMT::LastIndexOf_ptr);
  void visitCharAt(SMT::CharAt_ptr);
  void visitSubString(SMT::SubString_ptr);
  void visitToUpper(SMT::ToUpper_ptr);
  void visitToLower(SMT::ToLower_ptr);
  void visitTrim(SMT::Trim_ptr);
  void visitReplace(SMT::Replace_ptr);
  void visitCount(SMT::Count_ptr);
  void visitIte(SMT::Ite_ptr);
  void visitReConcat(SMT::ReConcat_ptr);
  void visitToRegex(SMT::ToRegex_ptr);

  Value_ptr get_term_value(SMT::Term_ptr term);
  bool set_term_value(SMT::Term_ptr term, Value_ptr value);
  bool update_term_value(SMT::Term_ptr term, Value_ptr Value);
  void clear_term_value(SMT::Term_ptr term);
  std::map<SMT::Term_ptr, SMT::Term_ptr>& get_term_value_index();
  TermValueMap& get_term_values();

  Value_ptr get_variable_value(SMT::Variable_ptr variable);
  bool update_variable_value(SMT::Variable_ptr variable, Value_ptr value);

  Value_ptr get_relational_value(SMT::Variable_ptr variable);

protected:

  SymbolTable_ptr symbol_table;
  StringRelationGenerator string_relation_generator;

  TermValueMap term_values;
  std::map<SMT::Term_ptr, SMT::Term_ptr> term_value_index;

private:
  static const int VLOG_LEVEL;

};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_STRINGCONSTRAINTSOLVER_H */
