

#ifndef SOLVER_COMPONENT_H_
#define SOLVER_COMPONENT_H_


#include <glog/logging.h>
#include "smt/ast.h"
#include "options/Solver.h"
#include "Ast2Dot.h"



namespace Vlab {
namespace Solver {
class Component {
public:
  Component(std::vector<SMT::Term_ptr>); //Will take in a vector of and pointers
  virtual ~Component();
  std::vector<SMT::Term_ptr> getTerms();
  bool isSolved();
  void setSolved(bool);
  bool isSat();
  void setSat(bool);

  std::string toString(); 


private:
  std::vector<SMT::Term_ptr> terms;
  bool solved;
  bool sat;
  Ast2Dot dot;

};


} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_COMPONENT_H_ */
