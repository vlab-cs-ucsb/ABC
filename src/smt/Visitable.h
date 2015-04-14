/*
 * Visitable.h
 *
 *  Created on: Apr 9, 2015
 *      Author: baki
 */

#ifndef SMT_VISITABLE_H_
#define SMT_VISITABLE_H_

#include <vector>

#include "typedefs.h"

namespace Vlab {
namespace SMT {

class Visitable {
public:
	virtual ~Visitable() {}

	virtual void accept(Visitor_ptr) = 0;
	virtual void visit_children(Visitor_ptr) = 0;

	template<class T>
	void deallocate_list(std::vector<T*> *v) {
		if (v == nullptr) return;
		for (auto& el : *v) {
			 delete (el);
			 el = nullptr;
		}
	}
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SMT_VISITABLE_H_ */
