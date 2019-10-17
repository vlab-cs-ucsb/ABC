//
// Created by will on 10/10/19.
//

#include "CachingConstraintSolver.h"

#ifndef USE_CACHE
#  error "This source should only be built if USE_CACHE is on!"
#endif

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int CachingConstraintSolver::VLOG_LEVEL = 11;

CachingConstraintSolver::CachingConstraintSolver(Script_ptr script, SymbolTable_ptr symbol_table,
                                   ConstraintInformation_ptr constraint_information,
                                   CacheManager_ptr cache_manager)
    : ConstraintSolver(script, symbol_table,constraint_information),
      cache_manager_(cache_manager) {


  num_hits_ = 0;
  num_misses_ = 0;
  auto start = std::chrono::steady_clock::now();
  auto end = std::chrono::steady_clock::now();
  diff = end-start;
  diff2 = end-start;

//  arithmetic_constraint_solver_.cache_manager_ = cache_manager_;
//  string_constraint_solver_.cache_manager_ = cache_manager_;
  Automaton::cache_manager_ = cache_manager_;
}

CachingConstraintSolver::~CachingConstraintSolver() {
  for(auto it = serializers_.begin(); it != serializers_.end(); it++) {
    std::thread &t = *it;
    t.join();
  }
}

void CachingConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "start";

  auto start = std::chrono::steady_clock::now();

  visit(root_);

  end();

  auto end = std::chrono::steady_clock::now();
  auto time2 = end-start;

//  LOG(INFO) << "solver.solve() time   : " << std::chrono::duration<long double, std::milli>(time2).count();

}

void CachingConstraintSolver::end() {
	for(auto &it : term_values_) {
		delete it.second;
		it.second = nullptr;
	}
	term_values_.clear();

//	if(symbol_table_->values_lock_) std::this_thread::yield();
	arithmetic_constraint_solver_.clear_term_values();
	string_constraint_solver_.clear_term_values();
}

void CachingConstraintSolver::visitScript(Script_ptr script) {
  symbol_table_->push_scope(script);
  Visitor::visit_children_of(script);
  symbol_table_->pop_scope();  // global scope, it is reachable via script pointer all the time
}


void CachingConstraintSolver::visitAssert(Assert_ptr assert_command) {

  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;

  std::string key, cached_data;
  bool has_cached_result = false;
  key = Ast2Dot::toString(assert_command);
  root_key_ = key;
//    LOG(INFO) << key;
//    std::cin.get();
//    auto cache_start = std::chrono::steady_clock::now();

//    auto &c = rdx_->commandSync<std::string>({"GET", key});
//    if (c.ok()) {
//      // has cached value
//      cached_data = c.reply();
//      has_cached_result = true;
//      num_hits_++;
//      hit_statistic_ = std::make_tuple<int, int>(1, 1);
//    } else {
//      num_misses_++;
//    }
  has_cached_result = cache_manager_->Get(key,cached_data);
//    c.free();

//    auto cache_end = std::chrono::steady_clock::now();
//    auto cache_time = cache_end-cache_start;
//    diff += cache_time;

  // if we have cached result, import it and go from there
  if (has_cached_result) {
    std::stringstream is(cached_data);

    // if formula was UNSAT, we store a single 0 in cache
    if (cached_data.size() == 1) {
//        LOG(INFO) << "UNSAT!";
//        std::cin.get();
      symbol_table_->update_satisfiability_result(false);
      return;
    }

    std::map<char, char> char_map;

    int num_string_to_read = 0;
    int num_int_to_read = 0;
    {
      cereal::BinaryInputArchive ar(is);
      ar(char_map);
      ar(num_string_to_read);
      ar(num_int_to_read);
    }

//      symbol_table_->SetCharacterMapping(char_map);

    arithmetic_constraint_solver_.collect_arithmetic_constraint_info();
    string_constraint_solver_.collect_string_constraint_info();

    // deserialize automata one by one until none left
    while (num_string_to_read-- > 0) {
      Theory::StringAutomaton_ptr import_auto = new Theory::StringAutomaton(nullptr, 0);
      {
        cereal::BinaryInputArchive ar(is);
        import_auto->load(ar);
      }

      std::string rep_var = import_auto->GetFormula()->GetVariableAtIndex(0);

      auto import_value = new Value(import_auto);
      symbol_table_->set_value(rep_var,import_value);
      delete import_value;
    }
    while (num_int_to_read-- > 0) {
      Theory::BinaryIntAutomaton_ptr import_auto = new Theory::BinaryIntAutomaton(nullptr, 0, true);
      {
        cereal::BinaryInputArchive ar(is);
        import_auto->load(ar);
      }

      std::string rep_var = import_auto->GetFormula()->GetVariableAtIndex(0);

      auto import_value = new Value(import_auto);
      symbol_table_->set_value(rep_var,import_value);
      delete import_value;
    }

    return;
  }

//  if(Option::Solver::FULL_FORMULA_CACHING) {
//      arithmetic_constraint_solver_.collect_arithmetic_constraint_info();
//      string_constraint_solver_.collect_string_constraint_info();
//  }

LOG(INFO) << "Before check_and_visit";
  check_and_visit(assert_command->term);


  Value_ptr result = getTermValue(assert_command->term);
  bool is_satisfiable = result->is_satisfiable();


  symbol_table_->update_satisfiability_result(is_satisfiable);
  if ((Term::Type::OR not_eq assert_command->term->type()) and (Term::Type::AND not_eq assert_command->term->type())) {

    if (is_satisfiable) {
      update_variables();
    }
  }
  clearTermValuesAndLocalLetVars();



  if(Option::Solver::FULL_FORMULA_CACHING and not Option::Solver::SUB_FORMULA_CACHING) {
    std::string temp = key;
    key = Ast2Dot::toString(assert_command);
    auto &value_map = symbol_table_->get_values_at_scope(symbol_table_->top_scope());
    std::stringstream os;

    // if not satisfiable, just store a single 0 in cache
    if (not symbol_table_->isSatisfiable()) {
      os << "0";
    } else {
      int num_string_to_write = 0;
      int num_int_to_write = 0;
      for (auto iter : value_map) {
        if (iter.second->getType() == Value::Type::STRING_AUTOMATON and
            iter.second->getStringAutomaton()->GetFormula()->GetType() != Theory::StringFormula::Type::NA) {
          if (iter.second->getStringAutomaton()->GetFormula()->GetNumberOfVariables() == 0) {
            continue;
          }
          auto equiv_class = symbol_table_->get_equivalence_class_of(iter.first);
          if(equiv_class != nullptr && equiv_class->has_constant()) {
            continue;
          }
          num_string_to_write++;
        } else if (iter.second->getType() ==
                   Value::Type::BINARYINT_AUTOMATON) {// and iter.second->getStringAutomaton()->GetFormula()->GetType() != Theory::StringFormula::Type::NA) {
          if (iter.second->getStringAutomaton()->GetFormula()->GetNumberOfVariables() == 0) {
            continue;
          }
          num_int_to_write++;
        }
      }

      {
        cereal::BinaryOutputArchive ar(os);
        ar(symbol_table_->GetCharacterMapping());
        ar(num_string_to_write);
        ar(num_int_to_write);
      }

      // write strings
      for (auto iter : value_map) {
        if (iter.second->getType() == Value::Type::STRING_AUTOMATON and
            iter.second->getStringAutomaton()->GetFormula()->GetType() != Theory::StringFormula::Type::NA) {
          auto export_auto = iter.second->getStringAutomaton();
          if (export_auto->GetFormula()->GetNumberOfVariables() == 0) {
            continue;
          }
          auto equiv_class = symbol_table_->get_equivalence_class_of(iter.first);
          if(equiv_class != nullptr && equiv_class->has_constant()) {
            continue;
          }

          {
            cereal::BinaryOutputArchive ar(os);
            export_auto->save(ar);
          }
        }
      }

      // write ints
      for (auto iter : value_map) {
        if (iter.second->getType() ==
            Value::Type::BINARYINT_AUTOMATON) {// and iter.second->getStringAutomaton()->GetFormula()->GetType() != Theory::StringFormula::Type::NA) {
          auto export_auto = iter.second->getBinaryIntAutomaton();
          if (export_auto->GetFormula()->GetNumberOfVariables() == 0) {
            continue;
          }

          {
            cereal::BinaryOutputArchive ar(os);
            export_auto->save(ar);
          }
        }
      }

    }
    // then send it to the cache
    cache_manager_->Set(key,os.str());
//    auto &c2 = rdx_->commandSync<std::string>({"SET", key, os.str()});
//    if (c2.ok()) {
//      c2.free();
//    } else {
//      LOG(FATAL) << "Failed to cache result: " << c2.status();
//    }
  }
}

void CachingConstraintSolver::visitAnd(And_ptr and_term) {
  DVLOG(VLOG_LEVEL) << "start visit and";



  std::map<int,std::string> term_keys;
  std::map<std::string,int> reverse_term_keys;

  bool is_satisfiable = true;
  bool is_component = constraint_information_->is_component(and_term);

  auto cache_start = std::chrono::steady_clock::now();
  auto cache_end = std::chrono::steady_clock::now();
//  auto cache_start2 = std::chrono::steady_clock::now();
//  auto cache_end2 = std::chrono::steady_clock::now();

  std::stack<Term_ptr> terms_to_solve;
  std::string key, cached_data;


  if(Option::Solver::SUB_FORMULA_CACHING) {

    auto m_data = std::make_shared<std::mutex>();
    auto alone = std::make_shared<std::atomic<bool>>(false);
    auto count = std::make_shared<std::atomic<int>>(0);
    std::atomic<bool> has_cached_result(false);
    has_cached_result = false;

    std::string success_key = "";

//    cache_start2 = std::chrono::steady_clock::now();

    auto got_reply = [&cached_data,&has_cached_result,&success_key,count,m_data,alone](redox::Command<std::string>& c) {
      if(c.ok()) {
        // if we have cahced data, we'll use it if we're the first one back from redis
        m_data->lock();
        if(has_cached_result == false) {
          cached_data = c.reply();
          if(cached_data.size() > 1) success_key = c.cmd().substr(4);

          //*alone = true;
          has_cached_result = true;
        }
        m_data->unlock();
      }
      m_data->lock();
      //if(not (*alone)) {
        (*count)++;
      //}
      m_data->unlock();
    };

    int num_sent = 0;
    int max = and_term->term_list->size();
    while (!has_cached_result && and_term->term_list->size() > 0) {

      key = Ast2Dot::toString(and_term);
      reverse_term_keys[key] = and_term->term_list->size();
      term_keys[and_term->term_list->size()] = key;
      cache_manager_->GetAsync(key,got_reply);
//      rdx_->command<std::string>({"GET", key},got_reply);
      num_sent++;

      terms_to_solve.push(and_term->term_list->back());
      and_term->term_list->pop_back();
    }

    while(*count < max && !has_cached_result) std::this_thread::yield();

    if (cached_data.size() == 1) {
      /*
      is_satisfiable = false;
      std::stringstream os;
      os << "0";
      key = term_keys[and_term->term_list->size()];
      for(int i = reverse_term_keys[key]; i < max; i++) {

      rdx_->command<std::string>({"SET",term_keys[i],os.str()});
      }
      */
      while(*count < num_sent) std::this_thread::yield();
      Value_ptr result = new Value(false);
      setTermValue(and_term, result);

      return;
    }
    if(has_cached_result) {

      int num_terms_cached = reverse_term_keys[success_key];

      while(and_term->term_list->size() < num_terms_cached) {
        and_term->term_list->push_back(terms_to_solve.top());
        terms_to_solve.pop();
      }
      num_hits_++;
      num_misses_ += max-num_terms_cached;
      hit_statistic_ = std::make_tuple(num_terms_cached,max);

    } else {
      num_misses_ += max;
    }

//    cache_end2 = std::chrono::steady_clock::now();
//    diff2 += cache_end2 - cache_start2;


    std::thread constraint_info_collector([this,and_term] {
      arithmetic_constraint_solver_.collect_arithmetic_constraint_info(and_term);
      string_constraint_solver_.collect_string_constraint_info(and_term);
    });



    // if we have cached result, import it and go from there
    if (has_cached_result) {


      // first check if key has only 0 in it. if so, formula unsat
      if (cached_data.size() == 1) {
        LOG(INFO) << "NOT SAT";
        Value_ptr result = new Value(false);
        setTermValue(and_term, result);
        return;
      }

      int num_string_to_read = 0;
      int num_int_to_read = 0;

      std::stringstream is(cached_data);
      std::map<char, char> char_mapping;
      {
        cereal::BinaryInputArchive ar(is);
        ar(char_mapping);
        ar(num_string_to_read);
        ar(num_int_to_read);
      }
//      symbol_table_->SetCharacterMapping(char_mapping);
      // deserialize automata one by one until none left

      std::vector<Theory::BinaryIntAutomaton_ptr> bin_autos_to_add;
      std::vector<Theory::StringAutomaton_ptr> str_autos_to_add;
      while (num_string_to_read > 0) {
        num_string_to_read--;
        Theory::StringAutomaton_ptr import_auto = new Theory::StringAutomaton(nullptr, 0);
        std::string var_name;
        {
          cereal::BinaryInputArchive ar(is);
          import_auto->load(ar);
        }

        str_autos_to_add.push_back(import_auto);

      }
      while (num_int_to_read-- > 0) {
        Theory::BinaryIntAutomaton_ptr import_auto = new Theory::BinaryIntAutomaton(nullptr, 0, not Vlab::Option::Solver::USE_SIGNED_INTEGERS);
        std::string var_name;
        {
          cereal::BinaryInputArchive ar(is);
          import_auto->load(ar);
        }
        // can't add autos till other read is done (data race on symbol table)
        bin_autos_to_add.push_back(import_auto);
      }

      // join the collector thread so we can set symbol table up
      constraint_info_collector.join();


      for(auto it : str_autos_to_add) {
        std::string rep_var = it->GetFormula()->GetVariableAtIndex(0);
        auto import_value = new Value(it);
        it = nullptr;
        symbol_table_->set_value(rep_var, import_value,false);
      }

      for(auto it : bin_autos_to_add) {

        std::string rep_var = it->GetFormula()->GetVariableAtIndex(0);
        auto import_value = new Value(it);
        it = nullptr;
        symbol_table_->set_value(rep_var, import_value,false);
      }
    } else {
      constraint_info_collector.join();
    }


    // at this point, we have the most updated values to start with
    // if terms_to_solve is empty, then we got the whole formula from the cache and we're done
    // otherwise, solve the rest and cache those values
//    Renamer renamer(root_, symbol_table_,
//                    symbol_table_->GetVariableMapping(),
//                    symbol_table_->GetCharacterMapping());
    while (not terms_to_solve.empty()) {


      // get the term to solve
      auto term = terms_to_solve.top();
      and_term->term_list->push_back(term);
      terms_to_solve.pop();

      // rename alphabet characters (from imported mapping, if any)
//      if (has_cached_result) {
//        renamer.start(term, false);
//      }

//      cache_start = std::chrono::steady_clock::now();

      if(dynamic_cast<Or_ptr>(term) == nullptr) {
        cache_start = std::chrono::steady_clock::now();
        arithmetic_constraint_solver_.collect_arithmetic_constraint_info(term);
        string_constraint_solver_.collect_string_constraint_info(term);


        cache_end = std::chrono::steady_clock::now();
        diff += cache_end - cache_start;

        // solve term using normal constraint solving algorithm
        if (is_component) {
          if (constraint_information_->has_arithmetic_constraint(term)) {
            arithmetic_constraint_solver_.start(term);
            is_satisfiable = arithmetic_constraint_solver_.get_term_value(term)->is_satisfiable();
            DVLOG(VLOG_LEVEL) << "Arithmetic formulae solved: " << *term << "@" << term;
          }
          if ((is_satisfiable or (!constraint_information_->has_arithmetic_constraint(term)))
              and constraint_information_->has_string_constraint(term)) {
            string_constraint_solver_.start(term);
            is_satisfiable = string_constraint_solver_.get_term_value(term)->is_satisfiable();
            DVLOG(VLOG_LEVEL) << "String formulae solved: " << *term << "@" << term;
          }

          DVLOG(VLOG_LEVEL) << "Multi-track solving done: " << *term << "@" << term;
        }

      }
      // solve non-relational terms
      is_satisfiable = check_and_visit(term) and is_satisfiable;
      if (not is_satisfiable) {
        clearTermValuesAndLocalLetVars();
        variable_path_table_.clear();
//        break;
      }
      if (dynamic_cast<Or_ptr>(term) == nullptr) {
        if (is_satisfiable) {
          is_satisfiable = update_variables();
          if (not is_satisfiable) {
//            break;
          }
        }
        clearTermValuesAndLocalLetVars();
      }
      // now we need to cache what we've got so far






      auto& value_map = symbol_table_->get_values_at_scope(symbol_table_->top_scope());
      auto tk = std::make_shared<std::map<int,std::string>>(term_keys.begin(),term_keys.end());
      auto revk = std::make_shared<std::map<std::string,int>>(reverse_term_keys.begin(),reverse_term_keys.end());

      symbol_table_->LockValues();
      bool is_done = terms_to_solve.empty();
      key = term_keys[and_term->term_list->size()];
      serializers_.push_back(std::thread([root_key_=root_key_,cache_manager_=cache_manager_,symbol_table_=symbol_table_, revk, tk, key, &value_map,is_done,is_satisfiable, max] {
        std::vector<Theory::BinaryIntAutomaton_ptr>* bin_stuff_to_store = new std::vector<Theory::BinaryIntAutomaton_ptr>();
        std::vector<Theory::StringAutomaton_ptr>* str_stuff_to_store = new std::vector<Theory::StringAutomaton_ptr>();



        // first serialize
        int num_string_to_write = 0;
        int num_int_to_write = 0;

        std::stringstream os;

        if(is_satisfiable) {
          for (auto iter : value_map) {
            if(iter.second == nullptr) {
              continue;
            }
            if (iter.second->getType() == Value::Type::STRING_AUTOMATON and
                iter.second->getStringAutomaton()->GetFormula()->GetType() != Theory::StringFormula::Type::NA) {
              if (iter.second->getStringAutomaton()->GetFormula()->GetNumberOfVariables() == 0) {
                continue;
              }
              //auto equiv_class = symbol_table_->get_equivalence_class_of(iter.first);
              //if(equiv_class != nullptr && equiv_class->has_constant()) {
              //  continue;
              //}
              num_string_to_write++;
              str_stuff_to_store->push_back(iter.second->getStringAutomaton()->clone());
            } else if (iter.second->getType() ==
                       Value::Type::BINARYINT_AUTOMATON) {// and iter.second->getStringAutomaton()->GetFormula()->GetType() != Theory::StringFormula::Type::NA) {
              if (iter.second->getBinaryIntAutomaton()->GetFormula()->GetNumberOfVariables() == 0) {
                continue;
              }
              num_int_to_write++;
              bin_stuff_to_store->push_back(iter.second->getBinaryIntAutomaton()->clone());
            }
          }




          {
            cereal::BinaryOutputArchive ar(os);
            ar(symbol_table_->GetCharacterMapping());
            ar(num_string_to_write);
            ar(num_int_to_write);
          }
          symbol_table_->UnlockValues();

          for(auto it : *str_stuff_to_store) {
            auto export_auto = it;

            {
              cereal::BinaryOutputArchive ar(os);
              export_auto->save(ar);
            }
            delete export_auto;
            export_auto = nullptr;
          }

          for(auto it : *bin_stuff_to_store) {
            auto export_auto = it;

            {
              cereal::BinaryOutputArchive ar(os);
              export_auto->save(ar);
            }
            delete export_auto;
            export_auto = nullptr;
          }
        } else {
          symbol_table_->UnlockValues();
          os << "0";
        }

        auto got_reply = [](redox::Command<std::string>& c) {
          if(!c.ok()) return;
          else return;
        };

        cache_manager_->SetAsync(key,os.str(),got_reply);
//        rdx_->command<std::string>({"SET",key,os.str()},got_reply);
        if(is_done || not is_satisfiable) {
          cache_manager_->SetAsync(root_key_,os.str(),got_reply);
//          rdx_->command<std::string>({"SET",root_key_,os.str()},got_reply);
          for(int i = (*revk)[key]; i < max; i++) {
            cache_manager_->SetAsync((*tk)[i],os.str(),got_reply);
//            rdx_->command<std::string>({"SET",(*tk)[i],os.str()},got_reply);
          }
        }

        delete str_stuff_to_store;
        delete bin_stuff_to_store;
        //delete revk;
        //delete tk;
      }));

      if(not is_satisfiable) {
        while(symbol_table_->values_lock_) std::this_thread::yield;
      }
    }
    while(symbol_table_->values_lock_) std::this_thread::yield;

    if (is_component and is_satisfiable) {
      if (constraint_information_->has_arithmetic_constraint(and_term)) {
        arithmetic_constraint_solver_.postVisitAnd(and_term);
        is_satisfiable = arithmetic_constraint_solver_.get_term_value(and_term)->is_satisfiable();
      }
      if (is_satisfiable and constraint_information_->has_string_constraint(and_term)) {
        string_constraint_solver_.postVisitAnd(and_term);
        is_satisfiable = string_constraint_solver_.get_term_value(and_term)->is_satisfiable();
      }
    }
    Value_ptr result = new Value(is_satisfiable);
    setTermValue(and_term, result);


  } else {
    bool is_satisfiable = true;
    bool is_component = constraint_information_->is_component(and_term);


    while(not and_term->term_list->empty()) {
      terms_to_solve.push(and_term->term_list->back());
      and_term->term_list->pop_back();
    }

    arithmetic_constraint_solver_.collect_arithmetic_constraint_info(and_term);
    string_constraint_solver_.collect_string_constraint_info(and_term);

    while(not terms_to_solve.empty()) {

      auto term = terms_to_solve.top();
      and_term->term_list->push_back(term);
      terms_to_solve.pop();


      if(dynamic_cast<Or_ptr>(term) == nullptr) {

        arithmetic_constraint_solver_.collect_arithmetic_constraint_info(term);
        string_constraint_solver_.collect_string_constraint_info(term);

        if (is_component) {
          if (constraint_information_->has_arithmetic_constraint(term)) {
            arithmetic_constraint_solver_.start(term);
            is_satisfiable = arithmetic_constraint_solver_.get_term_value(term)->is_satisfiable();
            DVLOG(VLOG_LEVEL) << "Arithmetic formulae solved: " << *term << "@" << term;
          }
          if ((is_satisfiable or (!constraint_information_->has_arithmetic_constraint(term)))
                and constraint_information_->has_string_constraint(term)) {
            string_constraint_solver_.start(term);
            is_satisfiable = string_constraint_solver_.get_term_value(term)->is_satisfiable();
            DVLOG(VLOG_LEVEL) << "String formulae solved: " << *term << "@" << term;
          }
        }
      }

      is_satisfiable = check_and_visit(term) and is_satisfiable;
      if(not is_satisfiable) {
        clearTermValuesAndLocalLetVars();
        variable_path_table_.clear();
        break;
      }

      if(dynamic_cast<Or_ptr>(term) == nullptr) {
        if(is_satisfiable) {
          is_satisfiable = update_variables();
          if(not is_satisfiable) {
            break;
          }
        }
        clearTermValuesAndLocalLetVars();
      }
    }

    DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;

    DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

    if (is_component and is_satisfiable) {
      if (constraint_information_->has_arithmetic_constraint(and_term)) {
        arithmetic_constraint_solver_.postVisitAnd(and_term);
        is_satisfiable = arithmetic_constraint_solver_.get_term_value(and_term)->is_satisfiable();
      }

      if (is_satisfiable and constraint_information_->has_string_constraint(and_term)) {
        string_constraint_solver_.postVisitAnd(and_term);
        is_satisfiable = string_constraint_solver_.get_term_value(and_term)->is_satisfiable();
      }
    }

    Value_ptr result = new Value(is_satisfiable);

    setTermValue(and_term, result);
  }

}

/**
 * 1) Solve arithmetic constraints
 * 2) Solve relational string constraints
 * 3) Solve single-track strings and mixed constraints
 */
void CachingConstraintSolver::visitOr(Or_ptr or_term) {
  std::string old_root_key = root_key_;
  root_key_ = Ast2Dot::toString(or_term);

  bool is_satisfiable = false;
  bool is_component = constraint_information_->is_component(or_term);


  if(true) {


    for (auto& term : *(or_term->term_list)) {

      string_constraint_solver_.push_generator(term);
      arithmetic_constraint_solver_.push_generator(term);

//      if(dynamic_cast<And_ptr>(term) == nullptr) {
//        LOG(FATAL) << "Should have an and term here!";
//      }

      symbol_table_->push_scope(term);
      bool is_scope_satisfiable = check_and_visit(term);
      if (dynamic_cast<And_ptr>(term) == nullptr) {

        if (is_scope_satisfiable) {
          update_variables();
        } else {
        	variable_path_table_.clear();
        }
        clearTermValuesAndLocalLetVars();
      }

      is_satisfiable = is_satisfiable or is_scope_satisfiable;
      symbol_table_->pop_scope();
    }

    string_constraint_solver_.pop_generators(or_term->term_list->size(),or_term);
    arithmetic_constraint_solver_.pop_generators(or_term->term_list->size(),or_term);

    if (constraint_information_->has_arithmetic_constraint(or_term)) {
      is_satisfiable = arithmetic_constraint_solver_.get_term_value(or_term)->is_satisfiable();
      DVLOG(VLOG_LEVEL) << "Arithmetic formulae solved: " << *or_term << "@" << or_term;
    }
    if ((is_satisfiable or !constraint_information_->has_arithmetic_constraint(or_term))
        and constraint_information_->has_string_constraint(or_term)) {
      is_satisfiable = string_constraint_solver_.get_term_value(or_term)->is_satisfiable();
      DVLOG(VLOG_LEVEL) << "String formulae solved: " << *or_term << "@" << or_term;
    }

    Value_ptr result = new Value(is_satisfiable);
    setTermValue(or_term, result);
    root_key_ = old_root_key;

    DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;

  } else {


    if (is_component && !Option::Solver::SUB_FORMULA_CACHING) {
      if (constraint_information_->has_arithmetic_constraint(or_term)) {
        arithmetic_constraint_solver_.start(or_term);
        is_satisfiable = arithmetic_constraint_solver_.get_term_value(or_term)->is_satisfiable();
        DVLOG(VLOG_LEVEL) << "Arithmetic formulae solved: " << *or_term << "@" << or_term;
      }
      if ((is_satisfiable or !constraint_information_->has_arithmetic_constraint(or_term))
          and constraint_information_->has_string_constraint(or_term)) {
        string_constraint_solver_.start(or_term);
        is_satisfiable = string_constraint_solver_.get_term_value(or_term)->is_satisfiable();
        DVLOG(VLOG_LEVEL) << "String formulae solved: " << *or_term << "@" << or_term;
      }

      DVLOG(VLOG_LEVEL) << "Multi-track solving done: " << *or_term << "@" << or_term;
    }

    DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;

    //if (constraint_information_->has_mixed_constraint(or_term)) {
    if (true) {
      for (auto &term : *(or_term->term_list)) {
        symbol_table_->push_scope(term);
        bool is_scope_satisfiable = check_and_visit(term);

        if (dynamic_cast<And_ptr>(term) == nullptr) {
          if (is_scope_satisfiable) {
            update_variables();
          } else {
            variable_path_table_.clear();
          }
          clearTermValuesAndLocalLetVars();
        }
        is_satisfiable = is_satisfiable or is_scope_satisfiable;
        symbol_table_->pop_scope();
      }
    }


    if (is_component and is_satisfiable) {
      if (constraint_information_->has_arithmetic_constraint(or_term)) {
        arithmetic_constraint_solver_.postVisitOr(or_term);
        is_satisfiable = arithmetic_constraint_solver_.get_term_value(or_term)->is_satisfiable();
      }

      if (is_satisfiable and constraint_information_->has_string_constraint(or_term)) {
        string_constraint_solver_.postVisitOr(or_term);
        is_satisfiable = string_constraint_solver_.get_term_value(or_term)->is_satisfiable();
      }
    }


    Value_ptr result = new Value(is_satisfiable);
    setTermValue(or_term, result);
    root_key_ = old_root_key;

    DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;
  }
}

}
}