
#ifndef SOLVER_COMPONENT_H_
#define SOLVER_COMPONENT_H_

#include <cstdbool>
#include <string>
#include <vector>

#include "smt/typedefs.h"

namespace Vlab {
namespace Solver {

class Component {
 public:
  Component();
  Component(SMT::Term_ptr);
  Component(SMT::TermList);
  virtual ~Component();
  void add_term(SMT::Term_ptr);
  std::vector<SMT::Term_ptr> get_terms() const;
  bool is_solved() const;
  void set_solved(bool is_solved);
  bool is_sat() const;
  void set_sat(bool is_sat);

  std::string ToString();
  std::string Name();

 protected:
  bool is_solved_;
  bool is_sat_;
  SMT::TermList terms_;
};

using Component_ptr = Component*;

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_COMPONENT_H_ */
