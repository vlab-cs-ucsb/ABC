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

class Node {
public:
  Node(int id) : stateID (id), flag(false),
    nextStates (nullptr), prevStates(nullptr) {

  }

  virtual ~Node() {
    for (auto& entry : exceptions) {
      delete entry.second;
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

  std::vector<char>* getExceptionToState(int id) {
    auto entry = exceptions.find(id);
    if (entry == exceptions.end()) {
      return nullptr;
    }
    return entry->second;
  }

  void addExceptionToState(int id, std::vector<char>* exception) {
    exceptions[id] = exception;
  }

  int getNumberOfExceptions() {
    return exceptions.size();
  }

  std::map<int, std::vector<char>*>& getExceptions() {
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
  std::map<int, std::vector<char>*> exceptions;
  std::set<int>* nextStates;
  std::set<int>* prevStates;

};

class GraphOld {
public:
  GraphOld() {
    graph = new std::map<int, Node*>();
  }
  ~GraphOld() {
    for (auto& el : *graph) {
      delete el.second;
    }
    delete graph;
  }

  Node* getNode(int n) {
    auto it = graph->find(n);
    return it->second;
  }

  void addNode(Node* node) {
    (*graph)[node->getID()] = node;
  }

  std::map<int, Node*>* getNodeMap() {
    return graph;
  }

  // TODO add function to find marked states

private:
  std::map<int, Node*>* graph;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_UTILS_H_ */
