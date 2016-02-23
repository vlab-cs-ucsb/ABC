/*
 * Driver.h
 *
 *  Created on: Nov 17, 2014
 *      Author: baki
 */

#ifndef SRC_DRIVER_H_
#define SRC_DRIVER_H_

#include <string>
#include <map>
#include <fstream>
#include <memory>
#include <boost/multiprecision/cpp_int.hpp>

#include <glog/logging.h>
#include "options/Solver.h"
#include "options/Theory.h"
#include "solver/Ast2Dot.h"
#include "parser/Scanner.h"
#include "parser/parser.hpp"
#include "solver/ConstraintSolver.h"
#include "solver/SymbolTable.h"
#include "solver/Initializer.h"
#include "solver/SyntacticOptimizer.h"
#include "solver/VariableOptimizer.h"
#include "solver/FormulaOptimizer.h"
#include "solver/ConstraintSorter.h"
#include "solver/SyntacticProcessor.h"

namespace Vlab {

class Driver {
public:
  Driver();
  ~Driver();

  void initializeABC(int log_level);
  // Error handling.
  void error(const Vlab::SMT::location& l, const std::string& m);
  void error(const std::string& m);
  int parse(std::istream* in = &std::cin);
  void ast2dot(std::string file_name);
  void ast2dot(std::ostream* out);
//	void collectStatistics();
  void initializeSolver();
  void solve();
  bool isSatisfiable();
  boost::multiprecision::cpp_int Count(std::string var_name, double bound, bool count_less_than_or_equal_to_bound = true);
  boost::multiprecision::cpp_int Count(int bound, bool count_less_than_or_equal_to_bound = true);
  std::string SymbolicCount(std::string var_name, double bound, bool count_less_than_or_equal_to_bound = true);
  std::string SymbolicCount(int bound, bool count_less_than_or_equal_to_bound = true);

  void printResult(Solver::Value_ptr value, std::ostream& out);
  void inspectResult(Solver::Value_ptr value, std::string file_name);
  std::map<SMT::Variable_ptr, Solver::Value_ptr> getSatisfyingVariables();
  std::map<std::string, std::string> getSatisfyingExamples();
  void reset();
//	void solveAst();

  void setOption(Option::Name option, bool value);
  void setOption(Option::Name option, std::string value);

  void test();

  SMT::Script_ptr script;
  Solver::SymbolTable_ptr symbol_table;

  int trace_parsing = 0;
  int trace_scanning = 0;
  std::string file;

private:
  static bool IS_LOGGING_INITIALIZED;

};

}

#endif /* SRC_DRIVER_H_ */
