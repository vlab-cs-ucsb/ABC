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
#include <random>

#ifdef HAVE_EXP_FS
  #include <experimental/filesystem>
#endif

#include <glog/logging.h>
#include <glog/vlog_is_on.h>



#include "interface/Driver.h"
#include "solver/options/Solver.h"
#include "smt/ast.h"
#include "solver/Value.h"
#include "theory/BinaryIntAutomaton.h"
#include "theory/StringAutomaton.h"
#include "utils/RegularExpression.h"

//static const std::string get_default_output_dir();
//static const std::string get_default_log_dir();

std::vector<unsigned long> parse_count_bounds(std::string);
std::vector<std::string> parse_count_vars(std::string);

int main(const int argc, const char **argv) {
  google::InstallFailureSignalHandler();

  std::istream* in = &std::cin;
  std::ifstream* file = nullptr;
  std::string file_name = "";
  std::string dir_name = "";
//  std::string output_root = get_default_output_dir();
//  std::string log_root = get_default_log_dir();

  std::string output_root = "";//{"./output"};
  std::string log_root {"./log"};

  FLAGS_log_dir = log_root;
  FLAGS_v = 30;
  FLAGS_logtostderr = 1;

  Vlab::Driver driver;
  driver.set_option(Vlab::Option::Name::REGEX_FLAG, 0x000f);

  bool experiment_mode = false;
  std::vector<unsigned long> str_bounds;
  std::vector<unsigned long> int_bounds;
  std::vector<std::string> count_variables;
  std::string count_variable = "";
  unsigned long num_models = 0;
  std::string re_var = "";
  std::string re_var_file = "";

  std::vector<std::string> model_variables;
  unsigned long num_random_models = 0;
  std::string random_models_file = "";
  int minrange = 0, maxrange = 0;

  std::string regex_compare_variable = "";
  std::string regex_compare_file = "";
  std::string regex_print_variable = "";

  bool count_tuple = false;
  bool count_tuple_variables = false;
  int alpha = 0;
  int omega = 0;
  std::vector<std::string> count_tuple_variable_names;
  for (int i = 1; i < argc; ++i) {
    if (argv[i] == std::string("-i") or argv[i] == std::string("--input-file")) {
      file_name = argv[i + 1];
      ++i;
    } else if (argv[i] == std::string("--use-unsigned")) {
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
    } else if (argv[i] == std::string("--enable-implications")) {
      driver.set_option(Vlab::Option::Name::ENABLE_IMPLICATIONS);
    } else if (argv[i] == std::string("--disable-implications")) {
      driver.set_option(Vlab::Option::Name::DISABLE_IMPLICATIONS);
    } else if (argv[i] == std::string("--limit-len-implications")) {
      driver.set_option(Vlab::Option::Name::LIMIT_LEN_IMPLICATIONS);
    } else if (argv[i] == std::string("--enable-sorting")) {
      driver.set_option(Vlab::Option::Name::ENABLE_SORTING_HEURISTICS);
    } else if (argv[i] == std::string("--disable-sorting")) {
      driver.set_option(Vlab::Option::Name::DISABLE_SORTING_HEURISTICS);
    } else if (argv[i] == std::string("--force-dnf-formula")) {
    	driver.set_option(Vlab::Option::Name::FORCE_DNF_FORMULA);
    } else if (argv[i] == std::string("--count-bound-exact")) {
      driver.set_option(Vlab::Option::Name::COUNT_BOUND_EXACT);
    } else if (argv[i] == std::string("--precise")) {
      driver.set_option(Vlab::Option::Name::USE_SINGLE_AUTO);
    } else if (argv[i] == std::string("--regex-split")) {
      driver.set_option(Vlab::Option::Name::USE_REGEX_SPLITTER);
    } else if (argv[i] == std::string("--prefix-shorten")) {
      driver.set_option(Vlab::Option::Name::USE_PREFIX_SHORTENER);      
    } else if (argv[i] == std::string("--count-tuple")) {
      count_tuple = true;
    } else if (argv[i] == std::string("--count-tuple-variables")) {
      count_tuple_variables = true;
      std::string count_vars {argv[i+1]};
      count_tuple_variable_names = parse_count_vars(count_vars);
    } else if (argv[i] == std::string("--concat-collapse")) {
      driver.set_option(Vlab::Option::Name::CONCAT_COLLAPSE_HEURISTIC);
    } else if (argv[i] == std::string("--dfa-to-re")) {
      std::string var {argv[i+1]};
      re_var = var;            
      re_var_file = std::string({argv[i+2]});
      alpha = std::stoi(argv[i+3]);
      omega = std::stoi(argv[i+4]);
      driver.set_option(Vlab::Option::Name::DFA_TO_RE);
      i += 4;
    } else if (argv[i] == std::string("-bs") or argv[i] == std::string("--bound-str")) {
      std::string bounds_str {argv[i + 1]};
      str_bounds = parse_count_bounds(bounds_str);
      ++i;
    } else if (argv[i] == std::string("-bi") or argv[i] == std::string("--bound-int")) {
      std::string bounds_str {argv[i + 1]};
      int_bounds = parse_count_bounds(bounds_str);
      ++i;
    } else if (argv[i] == std::string("-bv") or argv[i] == std::string("--bound-var")) {
      std::string bounds_str {argv[i + 1]};
      str_bounds = parse_count_bounds(bounds_str);
      int_bounds = str_bounds;
      ++i;
    } else if (argv[i] == std::string("--get-models")) {
    	num_models = std::stoi(argv[i+1]);
    	++i;
    } else if (argv[i] == std::string("--get-num-random-models")) {
      num_random_models = std::stoul(argv[i+1]);
      minrange = std::stoi(argv[i+2]);
      maxrange = std::stoi(argv[i+3]);
      std::string model_vars {argv[i+4]};
      random_models_file = std::string({argv[i+5]});
      model_variables = parse_count_vars(model_vars);
      driver.set_option(Vlab::Option::Name::GET_NUM_RANDOM_MODELS);
      i += 5;
    } else if (argv[i] == std::string("--compare-regex")) {
      regex_compare_variable = std::string({argv[i+1]});
      regex_compare_file = std::string({argv[i+2]});
      driver.set_option(Vlab::Option::Name::COMPARE_REGEX_VARIABLE);
      i += 2;
    } else if (argv[i] == std::string("--print-regex")) {
      regex_print_variable = std::string({argv[i+1]});
      driver.set_option(Vlab::Option::Name::PRINT_REGEX);
      i += 1;
    } else if (argv[i] == std::string("--count-variable")) {
      std::string count_vars {argv[i+1]};
      count_variables = parse_count_vars(count_vars);
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
      std::cout << std::setw(col) << "-bv or --bound-var <values>" << ": model count integer bit length bound e.g., -b 10 or a set of bounds e.g., -b \"4,8,16\"" << std::endl;
      std::cout << std::setw(col) << "--count-variable <name>" << ": model counts projected variable instead of tuples e.g., --count-variable x" << std::endl;
      std::cout << std::setw(col) << "--count-bound-exact" << ": model counts solutions of length exactly equal to given bound" << std::endl;
      std::cout << std::setw(col) << "--use-unsigned" << ": allows only positive integers" << std::endl;
      std::cout << std::setw(col) << "--use-signed" << ": allows positive and negative integers" << std::endl;
      std::cout << std::setw(col) << "--use-multitrack" << ": uses multitrack automata for strings" << std::endl;
      std::cout << std::setw(col) << "--use-singletrack" << ": uses singletrack automata for strings" << std::endl;
      std::cout << std::setw(col) << "--enable-equivalence" << ": enables equivalence class generation" << std::endl;
      std::cout << std::setw(col) << "--disable-equivalence" << ": disables equivalence class generation" << std::endl;
      std::cout << std::setw(col) << "--enable-dependency" << ": enables dependency analysis" << std::endl;
      std::cout << std::setw(col) << "--disable-dependency" << ": disables dependency analysis" << std::endl;
      std::cout << std::setw(col) << "--enable-implications" << ": enables adding implications for string constraints" << std::endl;
      std::cout << std::setw(col) << "--disable-implications" << ": disables adding implications for string constraints" << std::endl;
      std::cout << std::setw(col) << "--limit-len-implications" << ": disables length implications for word equations" << std::endl;
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

  file = new std::ifstream(file_name);
  in = file;
  if (not in->good()) {
    LOG(FATAL) << "Cannot find input: ";
  }

  driver.Parse(in);

#ifndef NDEBUG
  if (VLOG_IS_ON(30) and not output_root.empty()) {
    driver.ast2dot(output_root + "/parser_out.dot");
  }
#endif

  auto start = std::chrono::steady_clock::now();
  driver.InitializeSolver();

#ifndef NDEBUG
  if (VLOG_IS_ON(30) and not output_root.empty()) {
    driver.ast2dot(output_root + "/optimized.dot");
  }
#endif

  if(driver.symbol_table_->has_count_variable() and count_variable.empty()) {
    count_variables.push_back(driver.symbol_table_->get_count_variable()->getName());
  }

  driver.Solve();
  auto end = std::chrono::steady_clock::now();
  auto solving_time = end - start;

  std::cout << (driver.is_sat() ? "sat" : "unsat") << std::endl;

  if (driver.is_sat()) {
    LOG(INFO)<< "report is_sat: sat time: " << std::chrono::duration <long double, std::milli> (solving_time).count() << " ms";
    
    if(count_variables.empty()) count_variables.push_back("");


    if (count_tuple) {
      for (auto b : str_bounds) {
        start = std::chrono::steady_clock::now();
        auto count = driver.CountStrs(b);
        end = std::chrono::steady_clock::now();
        auto count_time = end - start;
        LOG(INFO) << "report (TUPLE) bound: " << b << " count: " << count << " time: "
                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
      }

      for (auto b : int_bounds) {
        start = std::chrono::steady_clock::now();
        auto count = driver.CountInts(b);
        end = std::chrono::steady_clock::now();
        auto count_time = end - start;
        LOG(INFO) << "report (TUPLE) bound: " << b << " count: " << count << " time: "
                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
      }
    }

    if (count_tuple_variables) {
      for (auto b : str_bounds) {
        start = std::chrono::steady_clock::now();
        auto count = driver.CountStrs(b,count_tuple_variable_names);
        end = std::chrono::steady_clock::now();
        auto count_time = end - start;
        LOG(INFO) << "report (TUPLE) bound: " << b << " count: " << count << " time: "
                  << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
      }

      // for (auto b : int_bounds) {
      //   start = std::chrono::steady_clock::now();
      //   auto count = driver.CountInts(b,count_tuple_variable_names);
      //   end = std::chrono::steady_clock::now();
      //   auto count_time = end - start;
      //   LOG(INFO) << "report (TUPLE) bound: " << b << " count: " << count << " time: "
      //             << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
      // }
      return 0;
    }
    

    for(auto count_var : count_variables) {
      count_variable = count_var;
      if (not count_variable.empty()) {
        LOG(INFO) << "report var: " << count_variable;
        for (auto b : int_bounds) {
          start = std::chrono::steady_clock::now();
          auto count_result = driver.CountVariable(count_variable, b);
          end = std::chrono::steady_clock::now();
          auto count_time = end - start;
          LOG(INFO) << "report bound: " << b << " count: " << count_result << " time: "
                    << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
        }
        for (auto b : str_bounds) {
          start = std::chrono::steady_clock::now();
          auto count_result = driver.CountVariable(count_variable, b);
          end = std::chrono::steady_clock::now();
          auto count_time = end - start;
          LOG(INFO) << "report bound: " << b << " count: " << count_result << " time: "
                    << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";

        }
      } else if (not count_tuple) {
        if (int_bounds.size() == 1 and str_bounds.size() == 1 and int_bounds[0] == str_bounds[0]) {
          
          auto b = int_bounds[0];
          start = std::chrono::steady_clock::now();
          auto count = driver.Count(b, b);
          end = std::chrono::steady_clock::now();
          auto count_time = end - start;
          LOG(INFO) << "report bound: " << b << " count: " << count << " time: "
                    << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
        } else {
          
          for (auto b : int_bounds) {
            start = std::chrono::steady_clock::now();
            auto count = driver.CountInts(b);
            end = std::chrono::steady_clock::now();
            auto count_time = end - start;
            LOG(INFO) << "report bound (integer): " << b << " count: " << count << " time: "
                      << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
          }
          for (auto b : str_bounds) {
            start = std::chrono::steady_clock::now();
            auto count = driver.CountStrs(b);
            end = std::chrono::steady_clock::now();
            auto count_time = end - start;
            LOG(INFO) << "report bound (string): " << b << " count: " << count << " time: "
                      << std::chrono::duration<long double, std::milli>(count_time).count() << " ms";
          }
        }


      }
    }

    // regex from dfa stuff
    if(Vlab::Option::Solver::DFA_TO_RE) {
      std::vector<std::string> re_from_dfa = driver.GetSimpleRegexes(re_var,1,alpha,omega);
      
      std::ofstream of;
      of.open(re_var_file.c_str(), std::ofstream::out | std::ofstream::trunc);
      
      if(not of) {
        LOG(FATAL) << "DFA-TO-RE: Could not write to file; file name = " << file_name;
      }

      for(auto it : re_from_dfa) {
        of << it;
        of << '\n';
      }
      of.close();

    }

    // get random models stuff
    if(Vlab::Option::Solver::GET_NUM_RANDOM_MODELS) {
      if(num_random_models <= 0 || model_variables.size() != 1) {
        LOG(FATAL) << "Number of random models should be greater than zero and should a variable to get models from" << std::endl
                   << "usage: --get-num-random-models <NUM_MODELS> <VARIABLE_NAME> <OUTFILE_NAME>";
      }

      std::vector<std::string> random_models = driver.GetNumRandomModels(model_variables,num_random_models, minrange, maxrange);

      std::ofstream of;
      of.open(random_models_file.c_str(), std::ofstream::out | std::ofstream::trunc);
      
      if(not of) {
        LOG(FATAL) << "GET-NUM-RANDOM-MODELS: Could not write to file; file name = " << random_models_file;
      }

      for(auto it : random_models) {
        of << it;
        of << '\n';
      }
      of.close();
    }
    
    if(Vlab::Option::Solver::COMPARE_REGEX_VARIABLE) {
      auto regex_file = new std::ifstream(regex_compare_file);
      if (not regex_file->good()) {
        LOG(FATAL) << "COMPARE-REGEX: Cannot find input: " << regex_compare_file;
      }

      std::string line;
      std::getline(*regex_file, line);

      auto results = driver.MeasureDistance(regex_compare_variable, line, str_bounds[0]);
      LOG(INFO) << "report baseline_regex: " << results[0];
      LOG(INFO) << "report synthesized_regex: " << results[1];
      LOG(INFO) << "report baseline_not_synthesized:" << results[2];
      LOG(INFO) << "report not_baseline_synthesized:" << results[3];
      LOG(INFO) << "report jaccard index numerator: " << results[4];
      LOG(INFO) << "report jaccard index denominator: " << results[5];

      auto qual_results = driver.CompareRegexes(regex_compare_variable, line);
      for(auto q : qual_results) {
        LOG(INFO) << q;
      }

      delete regex_file;
    }

    if(Vlab::Option::Solver::PRINT_REGEX) {
      auto result = driver.PrintRegex(regex_print_variable);
      LOG(INFO) << result;
    }

  } else {
    LOG(INFO) << "report is_sat: unsat time: " << std::chrono::duration <long double, std::milli> (solving_time).count() << " ms";
    LOG(INFO) << "report count: 0 time: 0";
  }

  LOG(INFO) << "done.";

  if (file != nullptr) {
    delete file;
  }

  return 0;
}

std::vector<unsigned long> parse_count_bounds(std::string bounds_str) {
  std::vector<unsigned long> bounds;
  std::stringstream ss(bounds_str);
  std::string tok;
  while (getline(ss, tok, ',')) {
    bounds.push_back(std::stoul(tok));
  }
  return bounds;
}

std::vector<std::string> parse_count_vars(std::string count_vars) {
  std::vector<std::string> vars;
  std::stringstream ss(count_vars);
  std::string tok;
  while (getline(ss, tok, ',')) {
    vars.push_back(tok);
  }
  return vars;
}