/*
 * SyntaxFixer.h
 *
 *  Created on: Sep 27, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_SYNTAXFIXER_H_
#define SRC_SOLVER_SYNTAXFIXER_H_

#include "smt/ast.h"
#include "PreOrderTraversal.h"
#include "PostOrderTraversal.h"

namespace Vlab {
namespace Solver {

class SyntaxFixer {
public:
  SyntaxFixer(SMT::Script_ptr script);
  virtual ~SyntaxFixer();

  void start();
  void end();
  void convertAssertsToAnd();
  void preProcessNegations();
  void convertToDNF();

protected:
  SMT::Script_ptr root;

private:
  static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SRC_SOLVER_SYNTAXFIXER_H_ */
