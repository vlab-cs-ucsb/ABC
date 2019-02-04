/*
 * Driver.h
 *
 *  Created on: Nov 17, 2014
 *      Author: baki
 */

#ifndef SRC_DRIVER_H_
#define SRC_DRIVER_H_

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <map>
#include <sstream>
#include <string>
#include <utility>
#include <chrono>
#include <vector>
#include <tuple>

#include <glog/logging.h>

#include <redox.hpp>
#include "boost/multiprecision/cpp_int.hpp"
#include "Eigen/SparseCore"
#include "cereal/archives/binary.hpp"
#include "parser/location.hh"
#include "parser/parser.hpp"
#include "parser/Scanner.h"
#include "smt/ast.h"
#include "smt/typedefs.h"
#include "solver/Ast2Dot.h"
#include "solver/ConstraintInformation.h"
#include "solver/ConstraintSolver.h"
#include "solver/ConstraintSorter.h"
#include "solver/DependencySlicer.h"
#include "solver/EquivalenceGenerator.h"
#include "solver/FormulaOptimizer.h"
#include "solver/ImplicationRunner.h"
#include "solver/Initializer.h"
#include "solver/ModelCounter.h"
#include "solver/options/Solver.h"
#include "solver/Renamer.h"
#include "solver/SymbolTable.h"
#include "solver/SyntacticOptimizer.h"
#include "solver/SyntacticProcessor.h"
#include "solver/Value.h"
#include "theory/ArithmeticFormula.h"
#include "theory/BinaryIntAutomaton.h"
#include "theory/IntAutomaton.h"
#include "theory/options/Theory.h"
#include "theory/StringAutomaton.h"
#include "theory/StringFormula.h"
#include "theory/Formula.h"
#include "theory/SymbolicCounter.h"
#include "utils/Serialize.h"

namespace Vlab {
namespace SMT {
class location;
} /* namespace SMT */
} /* namespace Vlab */

namespace Vlab {

class Driver {
public:

  std::chrono::duration<double> diff;
  std::chrono::duration<double> diff2;
  Driver();
  ~Driver();

  void InitializeLogger(int log_level);
  // Error handling.
  void error(const Vlab::SMT::location& l, const std::string& m);
  void error(const std::string& m);
  int Parse(std::istream* in = &std::cin);
  void ast2dot(std::string file_name);
  void ast2dot(std::ostream* out);
//	void collectStatistics();
  void InitializeSolver();
  void Solve();
  bool is_sat();

  void GetModels(const unsigned long bound,const unsigned long num_models);

  Theory::BigInteger CountVariable(const std::string var_name, const unsigned long bound);
  Theory::BigInteger CountInts(const unsigned long bound);
  Theory::BigInteger CountStrs(const unsigned long bound);
  Theory::BigInteger Count(const unsigned long int_bound, const unsigned long str_bound);

  Solver::ModelCounter& GetModelCounterForVariable(const std::string var_name, bool project = true);
  Solver::ModelCounter& GetModelCounter();

  void printResult(Solver::Value_ptr value, std::ostream& out);
  void inspectResult(Solver::Value_ptr value, std::string file_name);
  std::map<SMT::Variable_ptr, Solver::Value_ptr> getSatisfyingVariables() const;
  std::map<std::string, std::string> getSatisfyingExamples();
  std::map<std::string, std::string> getSatisfyingExamplesRandom();
  std::map<std::string, std::string> getSatisfyingExamplesRandomBounded(const int bound);
  std::string getMutatedModel(std::string var_name, std::string model);

  void reset();
//	void solveAst();

  void set_option(const Option::Name option);
  void set_option(const Option::Name option, const int value);
  void set_option(const Option::Name option, const std::string value);

  void loadID(std::string id);
	std::string getCurrentID();
	void destroyID(std::string id);
	void saveStateAndBranch();

  void test();

  SMT::Script_ptr script_;
  Solver::SymbolTable_ptr symbol_table_;
  Solver::ConstraintInformation_ptr constraint_information_;

  int trace_parsing_ = 0;
  int trace_scanning_ = 0;
  std::string file_;

  void print_statistics();

protected:
  void SetModelCounterForVariable(const std::string var_name, bool project = true);
  void SetModelCounter();


  bool is_model_counter_cached_;
  Solver::ModelCounter model_counter_;
  /**
   * Keeps projected model counters for a variable
   */
  std::map<SMT::Variable_ptr, Solver::ModelCounter> variable_model_counter_;

  std::map<std::string, Solver::SymbolTable_ptr> incremental_states_;
  std::string current_id_;
  /**
   * Keeps automata for variables (string vars are projected)
   */
  std::map<std::string, Solver::Value_ptr> cached_values_;

  /**
   * Keeps bounded projected automata for variables
   */
  std::map<std::string, Solver::Value_ptr> cached_bounded_values_;
  redox::Redox *rdx_;

  int total_hits_;
  int total_misses_;
  std::vector<std::tuple<int,int>> hit_statistics_;

  ;

private:
  static bool IS_LOGGING_INITIALIZED;

};


}

#endif /* SRC_DRIVER_H_ */
