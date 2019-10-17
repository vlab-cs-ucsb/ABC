//
// Created by will on 10/11/19.
//

#ifndef SOLVER_CACHEMANAGER_H
#define SOLVER_CACHEMANAGER_H

#include <redox.hpp>
#include <mona/dfa.h>
#include "../utils/Serialize.h"
#include <glog/logging.h>
#include "options/Solver.h"

namespace Vlab {
namespace Solver {

class CacheManager {
public:
  CacheManager();
  ~CacheManager();

  bool LoadDFA(std::string key, DFA*& dfa);
  bool StoreDFA(std::string key, DFA* dfa);


  template<typename F>
  void GetAsync(std::string key,F &lambda) {
    rdx_->command<std::string>({"GET", key},lambda);
  }
  bool Get(std::string key, std::string &result);



  template<typename F>
  void SetAsync(std::string key, std::string data, F &lambda) {
    rdx_->command<std::string>({"SET",key,data},lambda);
  }
  bool Set(std::string key, std::string data);

private:
  redox::Redox *rdx_;
};

using CacheManager_ptr = CacheManager*;

}
}


#endif //SOLVER_CACHEMANAGER_H
