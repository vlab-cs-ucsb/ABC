/*
 * FormulaOptimizer.h
 *
 *  Created on: May 12, 2015
 *      Author: baki
 */

#ifndef SRC_SOLVER_FORMULAOPTIMIZER_H_
#define SRC_SOLVER_FORMULAOPTIMIZER_H_

#include <glog/logging.h>
#include "../smt/ast.h"
#include "SymbolTable.h"

namespace Vlab {
namespace SMT {

class FormulaOptimizer: public Visitor {
public:
	FormulaOptimizer();
	virtual ~FormulaOptimizer();
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SRC_SOLVER_FORMULAOPTIMIZER_H_ */
