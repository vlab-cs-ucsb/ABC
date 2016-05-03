/*
 ============================================================================
 Name        : main.cpp
 Author      : baki
 Version     :
 Copyright   : Copyright 2015 The ABC Authors. All rights reserved. Use of this source code is governed license that can be found in the COPYING file.
 Description : An example usage of ABC string constraint solver and model counter
 ============================================================================
 */

#include <iostream>
#include <string>
#include <cstdlib>

//#define NDEBUG

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
    } else {

    }
  }

  google::InitGoogleLogging(argv[0]);

  /* log test start */
  DLOG(INFO)<< "debug log start";
  LOG(INFO)<< "production log";
  DVLOG(1) << "vlog log";

  if (VLOG_IS_ON(1)) {
    //std::cout << "yaaay" << std::endl;
  }
  /* log test end */

  if (not in->good()) {
    LOG(FATAL)<< "Cannot find input: ";
  }

  int bound = std::stoi(bound_string);

  Vlab::Driver driver;
  driver.setOption(Vlab::Option::Name::LIA_ENGINE_ENABLED, enable_lia_engine);
  driver.setOption(Vlab::Option::Name::MODEL_COUNTER_ENABLED, true);
  driver.setOption(Vlab::Option::Name::OUTPUT_PATH, output_root);
  driver.setOption(Vlab::Option::Name::SCRIPT_PATH, std::string("./lib/mathematica"));
  driver.setOption(Vlab::Option::Name::LIA_NATURAL_NUMBERS_ONLY, use_natural_numbers);

  driver.test();
  driver.parse(in);
  if (VLOG_IS_ON(30)) {
    driver.ast2dot(output_root + "/parser_out.dot");
  }

  driver.initializeSolver();

  if (VLOG_IS_ON(30)) {
    driver.ast2dot(output_root + "/optimized.dot");
  }

  driver.solve();

  if (driver.isSatisfiable()) {
    LOG(INFO)<< "SAT";
    if (VLOG_IS_ON(30)) {
      unsigned index = 0;
      for(auto& variable_entry : driver.getSatisfyingVariables()) {
        std::stringstream ss;
        ss << output_root << "/result_" << index++ << ".dot";
        std::string out_file = ss.str();
        driver.inspectResult(variable_entry.second, out_file);
//        std::string save_result = output_root + "/" + file_name.substr(file_name.find_last_of('/') + 2) + ".dot";
//        std::ofstream outfile(save_result.c_str());
//        if (!outfile.good()) {
//          std::cout << "cannot open file: " << save_result << std::endl;
//          exit(2);
//        }
//        driver.printResult(variable_entry.second, outfile);
        switch (variable_entry.second->getType()) {
          case Vlab::Solver::Value::Type::INT_AUTOMATON: {
            LOG(INFO) << variable_entry.first->getName() << " : " << variable_entry.second->getASatisfyingExample();
            break;
          }
          case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
            LOG(INFO) << variable_entry.first->getName() << " : \"" << variable_entry.second->getASatisfyingExample() << "\"";
            if (model_count) {
              LOG(INFO) << "count          : " << driver.Count(variable_entry.first->getName(), bound, false);
//              LOG(INFO) << "symbolic count : " << driver.SymbolicCount(variable_entry.first->getName(), bound);
            }
            break;
          }
          case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
            std::map<std::string, int> values = variable_entry.second->getBinaryIntAutomaton()->getAnAcceptingIntForEachVar();
            for (auto& entry : values) {
              LOG(INFO) << entry.first << " : " << entry.second;
            }

            if (model_count) {
              LOG(INFO) << "count          : " << driver.Count(bound, false);
//              LOG(INFO) << "symbolic count : " << driver.SymbolicCount(bound, false);
            }
            break;
          }
          default:
          break;
        }
      }
    }
  } else {
    LOG(INFO) << "UNSAT";
    if (model_count) {
      LOG(INFO) << "count          : " << 0;
    }
  }
  LOG(INFO)<< "done.";
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

