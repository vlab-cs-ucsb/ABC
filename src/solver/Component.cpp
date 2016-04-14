#include "Component.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

Component::Component(std::vector<Term_ptr> terms): terms(terms), solved(false), sat(false){
}

Component::~Component() {
}

std::vector<Term_ptr> Component::getTerms(){
  return terms;
}

bool Component::isSolved(){
  return solved;
}

void Component::setSolved(bool solve){
  solved = solve; 
}

bool Component::isSat() {
  return sat; 
}

void Component::setSat(bool sat_) {
  sat =  sat_;
}

std::string Component::toString(){
  std::string s = "";
  dot = Ast2Dot::Ast2Dot();
  for (auto& term: terms){
    s=s+dot.toString(term);
  }
  return s;
}




} //Vlab
} //Solver