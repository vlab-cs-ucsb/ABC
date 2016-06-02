#include "Component.h"

#include <sstream>
#include <functional>
#include <algorithm>

#include "Ast2Dot.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

Component::Component()
  : is_solved_ { false },
    is_sat_ { false },
    id_ {0} {
}

Component::Component(SMT::Term_ptr term)
  : is_solved_ { false },
    is_sat_ { false },
    id_ {0} {
  terms_.push_back(term);
}

Component::Component(TermList terms)
  : is_solved_ { false },
    is_sat_ { false },
    id_ {0},
    terms_(terms) {
}

Component::~Component() {
}

void Component::add_term(SMT::Term_ptr term) {
  if (std::find(terms_.begin(), terms_.end(), term) == terms_.end()) {
    terms_.push_back(term);
  }
}

void Component::add_variable(SMT::Variable_ptr var) {
  if (std::find(variables_.begin(), variables_.end(), var) == variables_.end()) {
    variables_.push_back(var);
  }
}

TermList Component::get_terms() const {
  return terms_;
}

std::vector<SMT::Variable_ptr> Component::get_variables() const {
  return variables_;
}

int Component::get_size() const {
  return variables_.size();
}

void Component::set_id(int id) {
  id_ = id;
}

int Component::get_id() const {
  return id_;
}

bool Component::is_solved() const {
  return is_solved_;
}

void Component::set_solved(bool is_solved) {
  is_solved_ = is_solved;
}

bool Component::is_sat() const {
  return is_sat_;
}

void Component::set_sat(bool is_sat) {
  is_sat_ = is_sat;
}

std::string Component::ToString() {
  std::stringstream ss;
  for (auto& term : terms_) {
    ss << Ast2Dot::toString(term);
  }
  return ss.str();
}

std::string Component::Name() {
  std::stringstream ss;
  std::hash<std::string> hash_func;
  ss << 'C' << hash_func(ToString());
  return ss.str();
}

} /* namespace Solver */
} /* namespace Vlab */
