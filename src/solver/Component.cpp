#include "Component.h"

#include <sstream>
#include <functional>

#include "Ast2Dot.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

Component::Component()
    : is_solved_ { false },
      is_sat_ { false } {
}

Component::Component(SMT::Term_ptr term)
    : is_solved_ { false },
      is_sat_ { false } {
  terms_.push_back(term);
}

Component::Component(TermList terms)
    : is_solved_ { false },
      is_sat_ { false },
      terms_(terms) {
}

Component::~Component() {
}

void Component::add_term(SMT::Term_ptr term) {
  terms_.push_back(term);
}

TermList Component::get_terms() const {
  return terms_;
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
