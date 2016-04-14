#include "DependencySlicer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
const int DependencySlicer::VLOG_LEVEL = 20;

DependencySlicer::DependencySlicer(Script_ptr script, SymbolTable_ptr symbol_table): AstTraverser(script), symbol_table(symbol_table), n_component(0) {
	setCallbacks();
	for (auto& pair : symbol_table->getVariables()) {
      ids[pair.second] = -1;
  } 
}

DependencySlicer::~DependencySlicer() {
}


void DependencySlicer::start() {
	DVLOG(VLOG_LEVEL) << "Starting the Dependency Slicer";
	term_phase = false;
	VariableCollector counter(root, symbol_table);
	counter.start();
	symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();
	end();
}

void DependencySlicer::end(){
  //Remap so the component id numbers go from 1 - number of components. 
	remap();
  components.resize(n_component);

  //Label the terms appropriately. 
  term_phase = true;
  VariableCollector counter(root, symbol_table);
  counter.start();
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();

  //Form the components!
  for (int i = 0; i < n_component; i++){
    Component* c = new Component(components[i]);
    symbol_table->updateComponents(c);
  }

	DVLOG(VLOG_LEVEL) << "Number of components:: " << n_component;
  for (auto& c: symbol_table->getComponents()){
    DVLOG(VLOG_LEVEL) << "Component:: " << c->toString();
  }
}

void DependencySlicer::remap(){
  //to be simplified 
  std::set<int> ids_end;
  for (auto& pair : symbol_table->getVariables()) {
    if (ids[pair.second] != -1){
      ids_end.insert(ids[pair.second]);
    }
  }
  std::map<int,int> remap;
  int i = 0;
  for (std::set<int>::iterator it = ids_end.begin(); it!= ids_end.end(); it++){
    remap[*it] = i;
    i++;
  }
  n_component = ids_end.size();
  for (auto& pair : symbol_table->getVariables()) {
    ids[pair.second] = remap[ids[pair.second]];
  }

}

void DependencySlicer::setCallbacks() {
  auto term_callback = [] (Term_ptr term) -> bool {
    return false;
  };

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  setCommandPreCallback(command_callback);
  setTermPreCallback(term_callback);
}

void DependencySlicer::visitOr(Or_ptr or_term) {
  for (auto& term : *(or_term->term_list)) {
    symbol_table->push_scope(term);
    visit(term);
    symbol_table->pop_scope();
  }
}

void DependencySlicer::visitAssert(Assert_ptr assert_term) {
  if ((Term::Type::OR not_eq assert_term->term->getType()) and
          (Term::Type::AND not_eq assert_term->term->getType())) {
    for (auto& pair : symbol_table->getVariables()) {
       ids[pair.second] = 0;
       if (term_phase) {
          if (std::find(components[0].begin(), components[0].end(), (Term_ptr)assert_term->term) == components[0].end()){
            components[0].push_back((Term_ptr)assert_term->term);
          }
       }
    }
  }
  else {
    visit(assert_term->term);
  }
}

void DependencySlicer::visitAnd(And_ptr and_term) {
  if (not term_phase) {
    std::set<int> to_merge; //components to merge 
    int merge_to; //component id to merge them to
    for (auto& term : *(and_term->term_list)) {
      merge_to = n_component; 
      symbol_table->push_scope(term);
      for (auto& pair : symbol_table->getVariables()) {
        if (symbol_table->get_local_count(pair.second) > 0) {
          //Variable present in this conjunct already has a component. Merge with this component. 
      	  if (ids[pair.second] != -1) {
            to_merge.insert(ids[pair.second]);
          }
          //Variable present already has a component and it's id is smaller than any seen so far. Merge components to this id. 
          if (ids[pair.second]!= -1 && ids[pair.second] < merge_to){
            merge_to = ids[pair.second];
          }
        }
      }
      //Go through variables and update their id. 
      for (auto& pair : symbol_table->getVariables()) {
        if (symbol_table->get_local_count(pair.second) > 0 || to_merge.find(ids[pair.second])!= to_merge.end()){
          ids[pair.second] = merge_to;
        }
      }
      if (merge_to == n_component){
        n_component++;
      }
      to_merge.clear();
      symbol_table->pop_scope();
    }
  }
  else { 
    //Add term to the appropriate component
    for (auto& term : *(and_term->term_list)) {
      symbol_table->push_scope(term);
      for (auto& pair : symbol_table->getVariables()) {
        if (symbol_table->get_local_count(pair.second) > 0){
          //Check if a duplicate
          if (std::find(components[ids[pair.second]].begin(), components[ids[pair.second]].end(), term) == components[ids[pair.second]].end()){
            components[ids[pair.second]].push_back(term);
          }
        }
      }
      symbol_table->pop_scope();
    }
  }
}

} //Vlab
} //Solver