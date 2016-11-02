/*
 ============================================================================
 Name        : main.cpp
 Author      : baki
 Version     :
 Copyright   : Copyright 2015 The ABC Authors. All rights reserved. Use of this source code is governed license that can be found in the COPYING file.
 Description : An example usage of ABC string constraint solver and model counter
 ============================================================================
 */

#include <chrono>
#include <cstdlib>
#include <iostream>
#include <iomanip>
#include <map>
#include <ratio>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

#include <glog/logging.h>
#include <glog/vlog_is_on.h>

#include "Driver.h"
#include "solver/options/Solver.h"
#include "smt/ast.h"
#include "solver/Value.h"
#include "theory/BinaryIntAutomaton.h"
#include "theory/MultiTrackAutomaton.h"
#include "theory/StringRelation.h"
#include "utils/RegularExpression.h"

//static const std::string get_default_output_dir();
//static const std::string get_default_log_dir();

int main(const int argc, const char **argv) {

  std::istream* in = &std::cin;
  std::ifstream* file = nullptr;
  std::string file_name;

//  std::string output_root = get_default_output_dir();
//  std::string log_root = get_default_log_dir();

  std::string output_root {"./output"};
  std::string log_root {"./log"};

  FLAGS_log_dir = log_root;
  FLAGS_v = 30;
  FLAGS_logtostderr = 1;

  Vlab::Driver driver;
//  driver.set_option(Vlab::Option::Name::LIA_ENGINE_ENABLED, enable_lia_engine);
//  driver.set_option(Vlab::Option::Name::MODEL_COUNTER_ENABLED, true);
//  driver.set_option(Vlab::Option::Name::OUTPUT_PATH, output_root);
//  driver.set_option(Vlab::Option::Name::SCRIPT_PATH, std::string("./lib/mathematica"));
//  driver.set_option(Vlab::Option::Name::LIA_NATURAL_NUMBERS_ONLY, use_natural_numbers);
//  driver.set_option(Vlab::Option::Name::ENABLE_RELATIONAL_STRING_AUTOMATA, enable_relational_string_automata);
//  driver.set_option(Vlab::Option::Name::FORCE_DNF_FORMULA, force_dnf_formula);
//  driver.set_option(Vlab::Option::Name::ENABLE_IMPLICATIONS, enable_implications);
//  driver.set_option(Vlab::Option::Name::ENABLE_DEPENDENCY, enable_dependency);
//  driver.set_option(Vlab::Option::Name::ENABLE_SORTING, enable_sorting);
//  driver.set_option(Vlab::Option::Name::ENABLE_EQUIVALENCE, enable_equivalence);

  Vlab::Util::RegularExpression::DEFAULT = 0x000e;

  bool experiment_mode = false;
  std::string bound_string {""};
  std::string count_variable {""};
  for (int i = 1; i < argc; ++i) {
    if (argv[i] == std::string("-i") or argv[i] == std::string("--input-file")) {
      file_name = argv[i + 1];
      file = new std::ifstream(file_name);
      in = file;
      ++i;
    } else if (argv[i] == std::string("--use-unsinged")) {
      driver.set_option(Vlab::Option::Name::USE_UNSIGNED_INTEGERS);
    } else if (argv[i] == std::string("--use-signed")) {
      driver.set_option(Vlab::Option::Name::USE_SIGNED_INTEGERS);
    } else if (argv[i] == std::string("--use-multitrack")) {
      driver.set_option(Vlab::Option::Name::USE_MULTITRACK_AUTO);
    } else if (argv[i] == std::string("--use-singletrack")) {
      driver.set_option(Vlab::Option::Name::USE_SINGLETRACK_AUTO);
    } else if (argv[i] == std::string("--enable-equivalence")) {
      driver.set_option(Vlab::Option::Name::ENABLE_EQUIVALENCE_CLASSES);
    } else if (argv[i] == std::string("--disable-equivalence")) {
      driver.set_option(Vlab::Option::Name::DISABLE_EQUIVALENCE_CLASSES);
    } else if (argv[i] == std::string("--enable-dependency")) {
      driver.set_option(Vlab::Option::Name::ENABLE_DEPENDENCY_ANALYSIS);
    } else if (argv[i] == std::string("--disable-dependency")) {
      driver.set_option(Vlab::Option::Name::DISABLE_DEPENDENCY_ANALYSIS);
    } else if (argv[i] == std::string("--enable-implication")) {
      driver.set_option(Vlab::Option::Name::ENABLE_IMPLICATIONS);
    } else if (argv[i] == std::string("--disable-implication")) {
      driver.set_option(Vlab::Option::Name::DISABLE_IMPLICATIONS);
    }else if (argv[i] == std::string("--enable-sorting")) {
      driver.set_option(Vlab::Option::Name::ENABLE_SORTING_HEURISTICS);
    } else if (argv[i] == std::string("--disable-sorting")) {
      driver.set_option(Vlab::Option::Name::DISABLE_SORTING_HEURISTICS);
    } else if (argv[i] == std::string("-b") or argv[i] == std::string("--bound")) {
      bound_string = argv[i + 1];
      ++i;
    } else if (argv[i] == std::string("-bs") or argv[i] == std::string("--bound-str")) {
      bound_string = argv[i + 1];
      ++i;
    } else if (argv[i] == std::string("-bi") or argv[i] == std::string("--bound-int")) {
      bound_string = argv[i + 1];
      ++i;
    } else if (argv[i] == std::string("--count-variable")) {
      count_variable = argv[i + 1];
      ++i;
    } else if (argv[i] == std::string("--output-dir")) {
      output_root = argv[i + 1];
      ++i;
    } else if (argv[i] == std::string("--log-dir")) {
      FLAGS_log_dir = argv[i + 1];
      FLAGS_logtostderr = 0;
      ++i;
    } else if (argv[i] == std::string("-v")) {
      FLAGS_v = std::stoi(argv[i + 1]);
      ++i;
    } else if (argv[i] == std::string("-e")) {
      experiment_mode = true;
    } else if (argv[i] == std::string("-h") or argv[i] == std::string("--help")) {
      int col = 28;
      std::cout << std::left;
      std::cout << std::setw(col) << "-h or --help" << ": lists available options" << std::endl;
      std::cout << std::setw(col) << "-i or --input-file <path>" << ": path to input constraint file" << std::endl;
      std::cout << std::setw(col) << "-bs or --bound-str <values>" << ": model count string length bound e.g., -bs 10 or a set of bounds e.g., -bs \"4,8,16\"" << std::endl;
      std::cout << std::setw(col) << "-bi or --bound-int <values>" << ": model count integer bit length bound e.g., -bs 10 or a set of bounds e.g., -bi \"4,8,16\"" << std::endl;
      std::cout << std::setw(col) << "--count-variable <name>" << ": model counts projected variable instead of tuples e.g., --count-variable x" << std::endl;
      std::cout << std::setw(col) << "--use-unsigned" << ": allows only positive integers" << std::endl;
      std::cout << std::setw(col) << "--use-signed" << ": allows positive and negative integers" << std::endl;
      std::cout << std::setw(col) << "--use-multitrack" << ": uses multitrack automata for strings" << std::endl;
      std::cout << std::setw(col) << "--use-singletrack" << ": uses singletrack automata for strings" << std::endl;
      std::cout << std::setw(col) << "--enable-equivalence" << ": enables equivalence class generation" << std::endl;
      std::cout << std::setw(col) << "--disable-equivalence" << ": disables equivalence class generation" << std::endl;
      std::cout << std::setw(col) << "--enable-dependency" << ": enables dependency analysis" << std::endl;
      std::cout << std::setw(col) << "--disable-dependency" << ": disables dependency analysis" << std::endl;
      std::cout << std::setw(col) << "--enable-implication" << ": enables adding implications for string constraints" << std::endl;
      std::cout << std::setw(col) << "--disable-implication" << ": disables adding implications for string constraints" << std::endl;
      std::cout << std::setw(col) << "--enable-sorting" << ": enables sorting heuristics for string constraints" << std::endl;
      std::cout << std::setw(col) << "--disable-sorting" << ": disables sorting heuristics for string constraints" << std::endl;
      std::cout << std::setw(col) << "--output-dir <dir>" << ": used for debugging outputs" << std::endl;
      std::cout << std::setw(col) << "--log-dir <dir>" << ": redirect logs from stderr to files and saves in the directory specified." << std::endl;
      std::cout << std::setw(col) << "--v <value>" << ": sets verbose logging level, unless you build ABC with configure --disable-debug" << std::endl;

      std::exit(0);
    } else {
    }
  }


  google::InitGoogleLogging(argv[0]);

  /* log test start */
//  DLOG(INFO)<< "debug log start";
//  LOG(INFO)<< "production log";
//  DVLOG(1) << "vlog log";

//  if (VLOG_IS_ON(1)) {
    //std::cout << "yaaay" << std::endl;
//  }
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

  driver.test();
  driver.parse(in);

#ifndef NDEBUG
  if (VLOG_IS_ON(30)) {
    driver.ast2dot(output_root + "/parser_out.dot");
  }
#endif

  auto start = std::chrono::steady_clock::now();
  driver.initializeSolver();

#ifndef NDEBUG
  if (VLOG_IS_ON(30)) {
    driver.ast2dot(output_root + "/optimized.dot");
  }
#endif

  driver.solve();
  auto end = std::chrono::steady_clock::now();
  auto solving_time = end - start;
  LOG(INFO) << "Done solving";

  if (driver.isSatisfiable()) {
    if (VLOG_IS_ON(30)) {
//      unsigned index = 0;
//      for (auto& variable_entry : driver.getSatisfyingVariables()) {
//        if (variable_entry.second == nullptr) {
//          // part of multitrack/binaryint
//          continue;
//        }
//        std::stringstream ss;
//        ss << output_root << "/result_";
//
//        bool print_auto = true;
//        switch (variable_entry.second->getType()) {
//        case Vlab::Solver::Value::Type::INT_AUTOMATON: {
//          LOG(INFO) << "---Int variable---";
//          LOG(INFO) << variable_entry.first->getName() << " : " << variable_entry.second->getASatisfyingExample();
//          ss << "int_" << index++ << variable_entry.first->getName() << ".dot";
//          break;
//        }
//        case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
//          LOG(INFO) << "---String variable---";
//          LOG(INFO) << variable_entry.first->getName() << " : \"" << variable_entry.second->getASatisfyingExample() << "\"";
//          ss << "string_" << index++  << variable_entry.first->getName() << ".dot";
//          if (model_count) {
//            LOG(INFO) << "var: " << variable_entry.first->getName() << " count          : " << driver.CountVariable(variable_entry.first->getName(), bound);
////              LOG(INFO) << "symbolic count : " << driver.SymbolicCount(variable_entry.first->getName(), bound);
//          }
//          break;
//        }
//        case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
//          std::map<std::string, int> values = variable_entry.second->getBinaryIntAutomaton()->GetAnAcceptingIntForEachVar();
//          ss << "binaryint" << index++  << ".dot";
//          LOG(INFO) << "---Binary int variables---";
//          for (auto& entry : values) {
//            LOG(INFO) << entry.first << " : " << entry.second;
//          }
//
//          if (model_count) {
//            LOG(INFO) << "count          : " << driver.CountVariable(variable_entry.first->getName(), bound);
////              LOG(INFO) << "symbolic count : " << driver.SymbolicCount(bound, false);
//          }
//          break;
//        }
//        case Vlab::Solver::Value::Type::MULTITRACK_AUTOMATON: {
//          ss << "relationalstring" << index++  << ".dot";
//          LOG(INFO) << "";
//          LOG(INFO) << *variable_entry.first;
//          Vlab::Theory::StringRelation_ptr rel = variable_entry.second->getMultiTrackAutomaton()->getRelation();
//          if (rel == nullptr) {
//            LOG(FATAL) << "Cannot get multitrack values, no relation";
//          }
//          if (model_count) {
//            LOG(INFO) << "count          : " << driver.CountVariable(variable_entry.first->getName(), bound);
//          }
//          break;
//        }
//        case Vlab::Solver::Value::Type::INT_CONSTANT: {
//          LOG(INFO) << "---Int variable---";
//          LOG(INFO) << variable_entry.first->getName() << " : " << variable_entry.second->getASatisfyingExample();
//          print_auto = false;
//        }
//        break;
//        default:
//          print_auto = false;
//          break;
//        }
//
//        if (print_auto) {
//          std::string out_file = ss.str();
//          std::ofstream outfile(out_file.c_str());
//          if (!outfile.good()) {
//            std::cout << "cannot open file: " << file_name << std::endl;
//            exit(2);
//          }
//          driver.printResult(variable_entry.second, outfile);
//        }
//      }
    }

    LOG(INFO)<< "report is_sat: SAT time: " << std::chrono::duration <long double, std::milli> (solving_time).count() << " ms";
    auto query_variable = driver.get_smc_query_variable();
    // if query_variable, report that count
    // otherwise, count up binary int
    if(query_variable != nullptr) {
      LOG(INFO) << "report var: " << query_variable->getName();
      for (auto b : bounds) {
        start = std::chrono::steady_clock::now();
        auto count_result = driver.CountVariable(query_variable->getName(), b);
        end = std::chrono::steady_clock::now();
        auto count_time = end - start;
        LOG(INFO) << "report bound: " << b << " count: " << count_result << " time: "
                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
      }

//      auto mc = driver.GetModelCounterForVariable(query_variable->getName());
//      for (auto b : bounds) {
//        start = std::chrono::steady_clock::now();
//        auto count = mc.CountStrs(b);
//        end = std::chrono::steady_clock::now();
//        auto count_time = end - start;
//        LOG(INFO) << "mc report bound: " << b << " count: " << count << " time: "
//                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
//      }
//
//      std::stringstream os;
//
//      {
//        cereal::BinaryOutputArchive ar(os);
//        mc.save(ar);
//      }
//
//      std::cout << os.str() << std::endl;
//
//      std::stringstream is (os.str());
//
//      Vlab::Solver::ModelCounter mc2;
//      {
//        cereal::BinaryInputArchive ar(is);
//        mc2.load(ar);
//      }
//
//      for (auto b : bounds) {
//        start = std::chrono::steady_clock::now();
//        auto count = mc.CountStrs(b);
//        end = std::chrono::steady_clock::now();
//        auto count_time = end - start;
//        LOG(INFO) << "mc2 report bound: " << b << " count: " << count << " time: "
//                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
//      }
    } else {
      LOG(INFO) << "No query variable found. Counting Binary Integers instead.";
      auto sat_vars = driver.getSatisfyingVariables();

      for (auto b : bounds) {
        start = std::chrono::steady_clock::now();
        auto count = driver.Count(bound, false);
        end = std::chrono::steady_clock::now();
        auto count_time = end - start;
        LOG(INFO) << "report bound: " << b << " count: " << count << " time: "
                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
      }
    }
  } else {
    LOG(INFO) << "report is_sat: UNSAT time: " << std::chrono::duration <long double, std::milli> (solving_time).count() << " ms";
    LOG(INFO) << "report count: 0 time: 0";
  }

  LOG(INFO) << "done.";
  if (file != nullptr) {
    delete file;
  }
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

//static const std::string get_default_output_dir() {
//  const char* env;
//  env = getenv("ABC_OUTPUT_DIR");
//  if (env != NULL && env[0] != '\0') {
//    return std::string(env);
//  }
//  int r = std::system("mkdir -p ./output");
//  return "./output";
//}
//
//static const std::string get_default_log_dir() {
//  const char* env;
//  env = getenv("ABC_LOG_DIR");
//  if (env != NULL && env[0] != '\0') {
//    return std::string(env);
//  }
//  int r = std::system("mkdir -p ./log");
//  return "./log";
//}
