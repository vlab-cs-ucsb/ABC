/*
 * Formula.cpp
 *
 *  Created on: Aug 14, 2017
 *      Author: will
 */

#include "Formula.h"


namespace Vlab {
namespace Theory {

Formula::Formula() {
}

Formula::~Formula() {
}

Formula::Formula(const Formula& other) {
	this->variable_coefficient_map_ = other.variable_coefficient_map_;
}

int Formula::GetVariableIndex(std::string variable_name) const {
	auto it = variable_coefficient_map_.find(variable_name);
	if (it != variable_coefficient_map_.end()) {
		return std::distance(variable_coefficient_map_.begin(), it);
	}
	LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << str();
	return -1;
}

int Formula::GetVariableIndex(const std::size_t param_index) const {
  for (auto it = variable_coefficient_map_.begin(); it != variable_coefficient_map_.end(); ++it) {
    if (it->second == param_index) {
      return std::distance(variable_coefficient_map_.begin(), it);
    }
  }

  LOG(FATAL)<< "Formula does not have param: " << param_index << ", " << str();
  return -1;
}

int Formula::GetVariableCoefficient(std::string variable_name) const {
	auto it = variable_coefficient_map_.find(variable_name);
	if (it == variable_coefficient_map_.end()) {
		LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << str();
	}
	return it->second;
}

void Formula::SetVariableCoefficient(std::string variable_name, int coeff) {
	auto it = variable_coefficient_map_.find(variable_name);
	if (it == variable_coefficient_map_.end()) {
		LOG(FATAL)<< "Variable '" << variable_name << "' is not in formula: " << str();
	}
	it->second = coeff;
}

std::string Formula::GetVariableAtIndex(const std::size_t index) const {
	if (index >= variable_coefficient_map_.size()) {
		LOG(FATAL) << "Index out of range";
	}
	auto it = variable_coefficient_map_.begin();
	std::advance(it, index);
	return it->first;
}

int Formula::GetNumberOfVariables() const {
	return variable_coefficient_map_.size();
}

std::map<std::string,int> Formula::GetVariableCoefficientMap() const {
	return variable_coefficient_map_;
}

void Formula::SetVariableCoefficientMap(std::map<std::string, int>& coefficient_map) {
	variable_coefficient_map_ = coefficient_map;
}

void Formula::AddVariable(std::string name, int coefficient) {
	if (variable_coefficient_map_.find(name) != variable_coefficient_map_.end()) {
		LOG(FATAL)<< "Variable has already been added! : " << name;
	}
	variable_coefficient_map_[name] = coefficient;
}

void Formula::RemoveVariable(std::string var_name) {
	variable_coefficient_map_.erase(var_name);
}

std::vector<int> Formula::GetCoefficients() const {
	std::vector<int> coefficients;
	for (const auto& el : variable_coefficient_map_) {
		coefficients.push_back(el.second);
	}
	return coefficients;
}

void Formula::ResetCoefficients(int value) {
	for (auto& el : variable_coefficient_map_) {
		el.second = value;
	}
}

bool Formula::Simplify() {
	if (variable_coefficient_map_.size() == 0) {
		return true;
	}

	return true;
}

} /* namespace Theory */
} /* namespace Vlab */
