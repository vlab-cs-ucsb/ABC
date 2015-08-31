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

namespace Vlab {
namespace Theory {

class Node {
public:
  Node(int id) : stateID (id) {

  }

  virtual ~Node() {
    for (auto& entry : exceptions) {
      delete entry.second;
    }
  }

  int getID() { return stateID; }

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

private:
  int stateID;
  std::map<int, std::vector<char>*> exceptions;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* SRC_THEORY_UTILS_H_ */
