/*
 * SyntacticProcessor.h
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_SYNTACTICPROCESSOR_H_
#define SRC_SOLVER_SYNTACTICPROCESSOR_H_

#include <sstream>

#include "AstTraverser.h"
#include "smt/ast.h"

namespace Vlab {
namespace Solver {

class SyntacticProcessor {
public:
  SyntacticProcessor(SMT::Script_ptr script);
  virtual ~SyntacticProcessor();

  void start();
  void end();
  void convertAssertsToAnd();
  void pushNegations();

protected:
  SMT::Script_ptr root;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_SYNTACTICPROCESSOR_H_ */
