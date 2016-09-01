/*
 * SyntacticProcessor.h
 *
 * - Applies De Morgan's Law and push negations down
 * - Does syntactic processing on input data types
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_SYNTACTICPROCESSOR_H_
#define SRC_SOLVER_SYNTACTICPROCESSOR_H_

#include <iterator>
#include <sstream>
#include <string>
#include <vector>

#include <glog/logging.h>

#include "../options/Solver.h"
#include "../smt/ast.h"
#include "../smt/Visitor.h"
#include "../smt/typedefs.h"
#include "AstTraverser.h"

namespace Vlab {
namespace Solver {

class SyntacticProcessor: AstTraverser {
public:
  SyntacticProcessor(SMT::Script_ptr script);
  virtual ~SyntacticProcessor();

  void start();
  void end();
  void setCallbacks();
  void convertAssertsToAnd();
  void visitAnd(SMT::And_ptr);
  void visitOr(SMT::Or_ptr);
  void visitNot(SMT::Not_ptr);
  void visitIndexOf(SMT::IndexOf_ptr);
  void visitLastIndexOf(SMT::LastIndexOf_ptr);

protected:
  bool CheckAndConvertToDnf(SMT::And_ptr);
  void check_and_convert_numeral_to_char(SMT::TermConstant_ptr);

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_SYNTACTICPROCESSOR_H_ */
