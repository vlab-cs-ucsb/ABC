/*
 ============================================================================
 Name        : main.cpp
 Author      : baki
 Version     :
 Copyright   : Copyright 2015 The ABC Authors. All rights reserved. Use of this source code is governed license that can be found in the COPYING file.
 Description : An example usage of ABC string constraint solver and model counter
 ============================================================================
 */

#define NDEBUG

#include <iostream>
#include <string>
#include <sstream>
#include <cstdlib>
#include <vector>
#include <chrono>
#include <ratio>

#include <glog/logging.h>
#include <Driver.h>

static const std::string get_default_output_dir();
static const std::string get_default_log_dir();

int main(const int argc, const char **argv) {

  std::istream* in = &std::cin;
  std::ifstream* file = nullptr;
  std::string file_name;

  std::string output_root = get_default_output_dir();
  std::string log_root = get_default_log_dir();
  FLAGS_log_dir = log_root;
  FLAGS_v = 30;
  FLAGS_logtostderr = 1;

  bool model_count_only = false;
  bool enable_lia_engine = true;
  bool use_natural_numbers = false;
  bool model_count = false;
  bool enable_relational_string_automata = true;
  bool force_dnf_formula = false;
  bool experiment_mode = false;
  bool enable_implications = true;
  bool enable_dependency = true;
  bool enable_sorting = true;
  bool enable_equivalence = true;

  std::string bound_string = "50";
  for (int i = 1; i < argc; ++i) {
    if (argv[i] == std::string("-c")) {
      model_count_only = true;
    } else if (argv[i] == std::string("-b")) {
      bound_string = argv[i + 1];
      model_count = true;
      ++i;
    } else if (argv[i] == std::string("-f")) {
      file_name = argv[i + 1];
      file = new std::ifstream(file_name);
      in = file;
      ++i;
    } else if (argv[i] == std::string("-v")) {
      FLAGS_v = std::stoi(argv[i + 1]);
      ++i;
    } else if (argv[i] == std::string("-u")) {
      enable_lia_engine = false;
    } else if (argv[i] == std::string("-p")) {
      enable_lia_engine = true;
    } else if (argv[i] == std::string("-n")) {
      use_natural_numbers = true;
    } else if (argv[i] == std::string("-d")) {
      force_dnf_formula = true;
    } else if (argv[i] == std::string("-r")) {
      enable_relational_string_automata = true;
    } else if (argv[i] == std::string("-s")) {
      enable_relational_string_automata = false;
    } else if (argv[i] == std::string("-e")) {
      experiment_mode = true;
    } else if (argv[i] == std::string("--enable-implications")) {
      enable_implications = true;
    } else if (argv[i] == std::string("--disable-implications")) {
      enable_implications = false;
    } else if (argv[i] == std::string("--disable-dependency")) {
      enable_dependency = false;
    } else if (argv[i] == std::string("--disable-sorting")) {
      enable_sorting = false;
    } else if (argv[i] == std::string("--disable-equivalence")) {
      enable_equivalence = false;
    } else {
    }
  }


  google::InitGoogleLogging(argv[0]);

  /* log test start */
//  DLOG(INFO)<< "debug log start";
//  LOG(INFO)<< "production log";
//  DVLOG(1) << "vlog log";

  if (VLOG_IS_ON(1)) {
    //std::cout << "yaaay" << std::endl;
  }
  /* log test end */

  if (not in->good()) {
    LOG(FATAL) << "Cannot find input: ";
  }

  /**
   * allow multiple counts
   * example option: -b 10,25,50,100
   */
  int bound = 0;
  std::vector<int> bounds;
  std::stringstream ss;
  for (auto c : bound_string) {
    if (c == ',') {
      ss >> bound;
      bounds.push_back(bound);
      ss.str("");
      ss.clear();
    } else {
      ss << c;
    }
  }

  if (ss.str() != "") {
    ss >> bound;
    bounds.push_back(bound);
  }

  if (bounds.size() == 1) {
    bound = bounds.front();
  }

  Vlab::Driver driver;
  driver.setOption(Vlab::Option::Name::LIA_ENGINE_ENABLED, enable_lia_engine);
  driver.setOption(Vlab::Option::Name::MODEL_COUNTER_ENABLED, true);
  driver.setOption(Vlab::Option::Name::OUTPUT_PATH, output_root);
  driver.setOption(Vlab::Option::Name::SCRIPT_PATH, std::string("./lib/mathematica"));
  driver.setOption(Vlab::Option::Name::LIA_NATURAL_NUMBERS_ONLY, use_natural_numbers);
  driver.setOption(Vlab::Option::Name::ENABLE_RELATIONAL_STRING_AUTOMATA, enable_relational_string_automata);
  driver.setOption(Vlab::Option::Name::FORCE_DNF_FORMULA, force_dnf_formula);
  driver.setOption(Vlab::Option::Name::ENABLE_IMPLICATIONS, enable_implications);
  driver.setOption(Vlab::Option::Name::ENABLE_DEPENDENCY, enable_dependency);
  driver.setOption(Vlab::Option::Name::ENABLE_SORTING, enable_sorting);
  driver.setOption(Vlab::Option::Name::ENABLE_EQUIVALENCE, enable_equivalence);

  Vlab::Util::RegularExpression::DEFAULT = 0x000e;

  driver.test();
  driver.parse(in);
  if (VLOG_IS_ON(30)) {
    driver.ast2dot(output_root + "/parser_out.dot");
  }

  auto start = std::chrono::steady_clock::now();
  driver.initializeSolver();

  if (VLOG_IS_ON(30)) {
    driver.ast2dot(output_root + "/optimized.dot");
  }

  driver.solve();
  auto end = std::chrono::steady_clock::now();
  auto solving_time = end - start;
  LOG(INFO) << "";
  LOG(INFO) << "Done solving";
  LOG(INFO) << "";
  if (driver.isSatisfiable()) {
    if (VLOG_IS_ON(30)) {
      unsigned index = 0;

      for (auto& variable_entry : driver.getSatisfyingVariables()) {

        if (variable_entry.second == nullptr) {
          // part of multitrack/binaryint
          continue;
        }

        std::stringstream ss;
        ss << output_root << "/result_";


        switch (variable_entry.second->getType()) {
        case Vlab::Solver::Value::Type::INT_AUTOMATON: {
          LOG(INFO) << "---Int variable---";
          LOG(INFO) << variable_entry.first->getName() << " : " << variable_entry.second->getASatisfyingExample();
          ss << "int_" << variable_entry.first->getName() << ".dot";
          break;
        }
        case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
          LOG(INFO) << "---String variable---";
          LOG(INFO) << variable_entry.first->getName() << " : \"" << variable_entry.second->getASatisfyingExample() << "\"";
          ss << "string_" << variable_entry.first->getName() << ".dot";
          if (model_count) {
            LOG(INFO) << "var: " << variable_entry.first->getName() << " count          : " << driver.Count(variable_entry.first->getName(), bound, true);
//              LOG(INFO) << "symbolic count : " << driver.SymbolicCount(variable_entry.first->getName(), bound);
          }
          break;
        }
        case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
          std::map<std::string, int> values = variable_entry.second->getBinaryIntAutomaton()->getAnAcceptingIntForEachVar();
          ss << "binaryint" << ".dot";
          LOG(INFO) << "---Binary int variables---";
          for (auto& entry : values) {
            LOG(INFO) << entry.first << " : " << entry.second;
          }

          if (model_count) {
            LOG(INFO) << "count          : " << driver.Count(variable_entry.first->getName(), bound, false);
//              LOG(INFO) << "symbolic count : " << driver.SymbolicCount(bound, false);
          }

          break;
        }
        case Vlab::Solver::Value::Type::MULTITRACK_AUTOMATON: {
          ss << "relationalstring" << ".dot";
          LOG(INFO) << "";
          LOG(INFO) << *variable_entry.first;
          Vlab::Theory::StringRelation_ptr rel = variable_entry.second->getMultiTrackAutomaton()->getRelation();
          if (rel == nullptr) {
            LOG(FATAL) << "Cannot get multitrack values, no relation";
          }
          if (model_count) {
            LOG(INFO) << "count          : " << driver.Count(variable_entry.first->getName(), bound, true);
          }
          break;
        }
        default:
          break;
        }
        std::string out_file = ss.str();
        std::ofstream outfile(out_file.c_str());
        if (!outfile.good()) {
          std::cout << "cannot open file: " << file_name << std::endl;
          exit(2);
        }
        driver.printResult(variable_entry.second, outfile);
      }
    }

    LOG(INFO) << "report is_sat: SAT time: " << std::chrono::duration <long double, std::milli> (solving_time).count() << " ms";
    if (experiment_mode) {
      auto query_variable = driver.get_smc_query_variable();
      LOG(INFO) << "report var: " << query_variable->getName();
      for (auto b : bounds) {
        start = std::chrono::steady_clock::now();
        auto count_result = driver.Count(query_variable->getName(), b, true);
        end = std::chrono::steady_clock::now();
        auto count_time = end - start;
        LOG(INFO) << "report bound: " << b << " count: " << count_result  << " time: " << std::chrono::duration <long double, std::milli> (count_time).count() << " ms";
      }
    }
  } else {
    LOG(INFO) << "report is_sat: UNSAT time: " << std::chrono::duration <long double, std::milli> (solving_time).count() << " ms";
    if (model_count) {
      LOG(INFO) << "report count: 0 time: 0";
    }
  }
  LOG(INFO) << "done.";
  if (file != nullptr)
    delete file;
  return 0;
}

//static const std::string get_env_value(const char name[]) {
//  const char* env;
//  env = getenv(name);
//  if (env != NULL && env[0] != '\0') {
//    return std::string(env);
//  }
//  return "";
//}

static const std::string get_default_output_dir() {
  const char* env;
  env = getenv("ABC_OUTPUT_DIR");
  if (env != NULL && env[0] != '\0') {
    return std::string(env);
  }
  int r = std::system("mkdir -p ./output");
  return "./output";
}

static const std::string get_default_log_dir() {
  const char* env;
  env = getenv("ABC_LOG_DIR");
  if (env != NULL && env[0] != '\0') {
    return std::string(env);
  }
  int r = std::system("mkdir -p ./log");
  return "./log";
}