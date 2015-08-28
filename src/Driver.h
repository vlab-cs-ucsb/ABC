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

#include <glog/logging.h>
#include "solver/Ast2Dot.h"
//#include "Statistics.h"
#include "solver/SymbolTable.h"
#include "solver/Initializer.h"
#include "solver/SyntacticOptimizer.h"
#include "solver/VariableOptimizer.h"
#include "solver/FormulaOptimizer.h"
#include "solver/ConstraintSorter.h"
#include "solver/PostImageComputer.h"
#include "Scanner.h"

namespace Vlab {

class Driver {
public:
  Driver();
  ~Driver();

  void initializeABC();
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
  void printResult(std::ostream& out);
  void printResult(std::string file_name);
  void reset();
//	void solveAst();

  void test();

  SMT::Script_ptr script;
  Solver::SymbolTable_ptr symbol_table;

  int trace_parsing = 0;
  int trace_scanning = 0;
  std::string file;

//	static const Log::Level TAG;
//	static PerfInfo* perfInfo;

};

}

#endif /* SRC_DRIVER_H_ */
