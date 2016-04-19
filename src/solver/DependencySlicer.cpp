#include "DependencySlicer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
const int DependencySlicer::VLOG_LEVEL = 20;

DependencySlicer::DependencySlicer(Script_ptr script, SymbolTable_ptr symbol_table): AstTraverser(script), symbol_table(symbol_table) {
	setCallbacks();
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

  //Label the terms appropriately. 
  term_phase = true;
  VariableCollector counter(root, symbol_table);
  counter.start();
  symbol_table->push_scope(root);
  visitScript(root);
  symbol_table->pop_scope();

  //Form the components!
  for (auto& num : n_component){
    for (int i = 0; i < num.second; i++){
      Component* c = new Component(components[num.first][i]);
      symbol_table->updateComponents(c, num.first);
    }
  }
  for (auto& m: symbol_table->getComponentMap()){
    if (m.first != root){
      DVLOG(VLOG_LEVEL) << "Number of components for scope " << *((Term_ptr)m.first) << " is " << m.second.size();
    }
    else {
      DVLOG(VLOG_LEVEL) << "Number of components for scope root :: " << m.second.size();
    }
    for (auto& c : m.second){
      DVLOG(VLOG_LEVEL) << "Component:: " << c->toString();
    }
  }
}

void DependencySlicer::remap(){
  //to be simplified 
  for (auto& scope_ids : ids){
    std::set<int> ids_end;
    for (auto& pair : symbol_table->getVariables()) {
      if (scope_ids.second[pair.second] != -1){
        ids_end.insert(scope_ids.second[pair.second]);
      }
    }
    std::map<int,int> remap;
    int i = 0;
    for (std::set<int>::iterator it = ids_end.begin(); it!= ids_end.end(); it++){
      remap[*it] = i;
      i++;
    }
    n_component[scope_ids.first] = ids_end.size();
    components[scope_ids.first].resize(n_component[scope_ids.first]);
    for (auto& pair : symbol_table->getVariables()) {
      scope_ids.second[pair.second] = remap[scope_ids.second[pair.second]];
    }
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
    scope = term;
    if (not term_phase){
      n_component[scope] = 0;
      for (auto& pair: symbol_table->getVariables()){
        ids[scope][pair.second] = -1;
      }
    }
    visit(term);
    symbol_table->pop_scope();
  }
}

void DependencySlicer::visitAssert(Assert_ptr assert_term) {
  if (Term::Type::OR not_eq assert_term->term->getType()) {
    scope = root;
    if (not term_phase){
      n_component[scope] = 0;
      for (auto& pair: symbol_table->getVariables()){
        ids[scope][pair.second] = -1;
      }
    }
  }
  if ((Term::Type::OR not_eq assert_term->term->getType()) and
          (Term::Type::AND not_eq assert_term->term->getType())) {
    for (auto& pair : symbol_table->getVariables()) {
      ids[scope][pair.second] = 0;
    }
    if (term_phase) {
      if (std::find(components[scope][0].begin(), components[scope][0].end(), (Term_ptr)assert_term->term) == components[scope][0].end()){
        components[scope][0].push_back((Term_ptr)assert_term->term);
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
      merge_to = n_component[scope]; 
      symbol_table->push_scope(term);
      for (auto& pair : symbol_table->getVariables()) {
        if (symbol_table->get_local_count(pair.second) > 0) {
          //Variable present in this conjunct already has a component. Merge with this component. 
      	  if (ids[scope][pair.second] != -1) {
            to_merge.insert(ids[scope][pair.second]);
          }
          //Variable present already has a component and it's id is smaller than any seen so far. Merge components to this id. 
          if (ids[scope][pair.second]!= -1 && ids[scope][pair.second] < merge_to){
            merge_to = ids[scope][pair.second];
          }
        }
      }
      //Go through variables and update their id. 
      for (auto& pair : symbol_table->getVariables()) {
        if (symbol_table->get_local_count(pair.second) > 0 || to_merge.find(ids[scope][pair.second])!= to_merge.end()){
          ids[scope][pair.second] = merge_to;
        }
      }
      if (merge_to == n_component[scope]){
        n_component[scope]++;
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
          if (std::find(components[scope][ids[scope][pair.second]].begin(), components[scope][ids[scope][pair.second]].end(), term) == components[scope][ids[scope][pair.second]].end()){
            components[scope][ids[scope][pair.second]].push_back(term);
          }
        }
      }
      symbol_table->pop_scope();
    }
  }
}

} //Vlab
} //Solver