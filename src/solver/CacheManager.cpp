//
// Created by will on 10/11/19.
//

#include "CacheManager.h"

#ifndef USE_CACHE
#  error "This source should only be built if USE_CACHE is on!"
#endif

namespace Vlab {
namespace Solver {

CacheManager::CacheManager() {
  LOG(INFO) << 10;
  if(Option::Solver::FULL_FORMULA_CACHING || Option::Solver::SUB_FORMULA_CACHING || Option::Solver::AUTOMATA_CACHING) {
    rdx_ = new redox::Redox(std::cout,redox::log::Level::Off);
    rdx_->noWait(true);
    LOG(INFO) << 11;
    if(!rdx_->connect("localhost", 6379)) {
      LOG(FATAL) << "Could not connect to redis server";
    }
    LOG(INFO) << 12;
  } else {
    LOG(INFO) << 13;
    rdx_ = nullptr;
  }
  LOG(INFO) << 14;
}

CacheManager::~CacheManager() {
  if(rdx_ != nullptr) {
    rdx_->disconnect();
    delete rdx_;
  }
}

bool CacheManager::LoadDFA(std::string key, DFA*& dfa) {
//  DFA_ptr result_dfa = nullptr;
  std::string cached_data;
  bool has_result = Get(key,cached_data);
  if (has_result) {
    std::stringstream is(cached_data);
    {
      cereal::BinaryInputArchive ar(is);
      Util::Serialize::load(ar, dfa);
    }
  }
  return has_result;
}

bool CacheManager::StoreDFA(std::string key, DFA* dfa) {
  std::stringstream os;
  {
    cereal::BinaryOutputArchive ar(os);
    Util::Serialize::save(ar, dfa);
  }
  rdx_->command<std::string>({"SET", key, os.str()});
  return true;
}

bool CacheManager::Get(std::string key, std::string &result) {
  auto &c = rdx_->commandSync<std::string>({"GET", key});
  bool has_result = false;
  if (c.ok()) {
    has_result = true;
    result = c.reply();
  }
  c.free();
  return has_result;
}

bool CacheManager::Set(std::string key, std::string data) {
  rdx_->command<std::string>({"SET", key, data});
}



}
}