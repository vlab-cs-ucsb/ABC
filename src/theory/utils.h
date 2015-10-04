/*
 * utils.h
 *
 *  Created on: Aug 30, 2015
 *      Author: baki
 */

#ifndef SRC_THEORY_UTILS_H_
#define SRC_THEORY_UTILS_H_

#include <vector>
#include <map>
#include <set>

namespace Vlab {
namespace Theory {

class NodeOld {
public:
  NodeOld(int id) : stateID (id), flag(false),
    nextStates (nullptr), prevStates(nullptr) {

  }

  virtual ~NodeOld() {
    for (auto entry : exceptions) {
      entry.first->clear();
      delete entry.first;
    }
    delete nextStates;
    delete prevStates;
  }

  int getID() { return stateID; }

  void addNextState(int state) {
    nextStates->insert(state);
  }

  void addPrevState(int state) {
    prevStates->insert(state);
  }

  void setNextStates(std::set<int>* nexts) {
    this->nextStates = nexts;
  }

  void setPrevStates(std::set<int>* prevs) {
    this->prevStates = prevs;
  }

  std::set<std::vector<char>*> getExceptionsToState(int id) {
    std::set<std::vector<char>*> exceptions_to_state;
    for (auto entry : exceptions) {
      if (entry.second == id) {
        exceptions_to_state.insert(entry.first);
      }
    }
    return exceptions_to_state;
  }

  void addExceptionToState(std::vector<char>* exception, int id) {
    exceptions[exception] = id;
  }

  int getNumberOfExceptions() {
    return exceptions.size();
  }

  std::map<std::vector<char>*, int>& getExceptions() {
    return exceptions;
  }

  void setFlag(bool value) {
    this->flag = value;
  }

  bool getFlag() {
    return this->flag;
  }

private:
  int stateID;
  bool flag;
  std::map<std::vector<char>*, int> exceptions;
  std::set<int>* nextStates;
  std::set<int>* prevStates;

};

class GraphOld {
public:
  GraphOld() {
    graph = new std::map<int, NodeOld*>();
  }
  ~GraphOld() {
    for (auto& el : *graph) {
      delete el.second;
    }
    delete graph;
  }

  NodeOld* getNode(int n) {
    auto it = graph->find(n);
    return it->second;
  }

  void addNode(NodeOld* node) {
    (*graph)[node->getID()] = node;
  }

  std::map<int, NodeOld*>* getNodeMap() {
    return graph;
  }

  // TODO add function to find marked states

private:
  std::map<int, NodeOld*>* graph;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_UTILS_H_ */
