/*
 * SVisitor.h
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#ifndef SOLVER_SVISITOR_H_
#define SOLVER_SVISITOR_H_

namespace Vlab {
namespace SMT {

class SVisitor {
public:
	virtual ~SVisitor() {}
	virtual void start() = 0;
	virtual void end() = 0;
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_SVISITOR_H_ */
