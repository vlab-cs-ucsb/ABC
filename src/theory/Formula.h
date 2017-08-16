/*
 * Formula.h
 *
 *  Created on: Aug 14, 2017
 *      Author: will
 */

#ifndef SRC_THEORY_FORMULA_H_
#define SRC_THEORY_FORMULA_H_

#include <cmath>
#include <cstdlib>
#include <locale>
#include <map>
#include <sstream>
#include <string>
#include <vector>
#include <utility>

#include <glog/logging.h>

#include "../smt/ast.h"
#include "../utils/Math.h"

namespace Vlab {
namespace Theory {

class Formula;
using Formula_ptr = Formula*;

class Formula {
public:
	Formula();
	virtual ~Formula();

	Formula(const Formula&);
	virtual Formula_ptr clone() const = 0;
	virtual std::string str() const = 0;

	virtual Formula_ptr Intersect(Formula_ptr) = 0;
	virtual Formula_ptr Union(Formula_ptr) = 0;
	virtual Formula_ptr Complement() = 0;

	virtual void MergeVariables(Formula_ptr) = 0;
	int GetVariableIndex(std::string) const;
	int GetVariableCoefficient(std::string) const;
	void SetVariableCoefficient(std::string, int);
	std::string GetVariableAtIndex(const std::size_t index) const;
	int GetNumberOfVariables() const;
	std::map<std::string,int> GetVariableCoefficientMap() const;
	void SetVariableCoefficientMap(std::map<std::string, int>& coefficient_map);
	void AddVariable(std::string,int);
	void RemoveVariable(std::string);
	std::vector<int> GetCoefficients() const;
	void ResetCoefficients(int);

	virtual bool UpdateMixedConstraintRelations() = 0;
	virtual bool Simplify();

protected:
	std::map<std::string,int> variable_coefficient_map_;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_FORMULA_H_ */
