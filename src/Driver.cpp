/*
 * Driver.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: baki
 */

#include "Driver.h"

namespace Vlab {

//const Log::Level Driver::TAG = Log::DRIVER;
//PerfInfo* Driver::perfInfo;

Driver::Driver()
        : script(nullptr), symbol_table(nullptr) {
}

Driver::~Driver() {
  delete script;
}

void Driver::error(const std::string& m) {
  std::cerr << m << std::endl;
}

int Driver::parse(std::istream* in) {
  SMT::Scanner scanner(in);
  //	scanner.set_debug(trace_scanning);
  SMT::Parser parser(script, scanner);
  //	parser.set_debug_level (trace_parsing);
  int res = parser.parse();
  CHECK_EQ(0, res);
  return res;
}

void Driver::ast2dot(std::ostream* out) {

  Solver::Ast2Dot ast2dot(out);
  ast2dot.start(script);
}
void Driver::ast2dot(std::string file_name) {
  std::ofstream outfile(file_name.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file_name << std::endl;
    exit(2);
  }
  ast2dot(&outfile);
  outfile.close();
}

//void Driver::collectStatistics() {
//	SMT::Statistics::perfInfo = perfInfo;
//	SMT::Statistics statistics;
//	statistics.start(script, symbol_table);
//}

void Driver::initializeSolver() {

  symbol_table = new Solver::SymbolTable();
  Solver::Initializer initializer(script, symbol_table);
  initializer.start();

  Solver::SyntacticOptimizer syntactic_optimizer(script, symbol_table);
  syntactic_optimizer.start();

  Solver::VariableOptimizer variable_optimizer(script, symbol_table);
  variable_optimizer.start();

  Solver::FormulaOptimizer formula_optimizer(script, symbol_table);
  formula_optimizer.start();

  //	SMT::LengthConstraintReductor len_reductor;
  //	len_reductor.start(script, symbol_table);

  Solver::ConstraintSorter constraint_sorter(script, symbol_table);
  constraint_sorter.start();
}

void Driver::solve() {
  Solver::PostImageComputer post_image_computer(script, symbol_table);
  post_image_computer.start();

  // TODO iterate to handle over-approximation
}

void Driver::printResult() {
  symbol_table->push_scope(script);
  SMT::Variable_ptr variable = symbol_table->getSymbolicVariable();
  Solver::Value_ptr result = symbol_table->getValue(variable);
  LOG(INFO) << "Symbolic variable: " << *result;
  result->getStringAutomaton()->toDotAscii();
}

void Driver::test() {
//  Theory::StringAutomaton_ptr any_string = Theory::StringAutomaton::makeAnyString();
//  Theory::StringAutomaton_ptr complement = nullptr;
//  any_string->toDotAscii(1);
//  complement = any_string->complement();
//  complement->toDotAscii(1);

//  Theory::StringAutomaton_ptr make_string = Theory::StringAutomaton::makeString("baki");
//  make_string->complement()->toDotAscii();
//
//  Theory::StringAutomaton_ptr char_range = Theory::StringAutomaton::makeCharRange('e', 'm');
//  char_range->toDotAscii(1);
//
//  Theory::StringAutomaton_ptr dot_auto = Theory::StringAutomaton::makeAnyChar();
//  dot_auto->toDotAscii(1);

//  Theory::StringAutomaton_ptr empty_string = Theory::StringAutomaton::makeEmptyString();

//  Theory::StringAutomaton_ptr result = make_string->union_(any_string);
//  result->toDotAscii();

//  Theory::StringAutomaton_ptr regex_auto = Theory::StringAutomaton::makeRegexAuto("/#/");
//  regex_auto->toDotAscii();
//
//  std::exit(0);
}

void Driver::error(const Vlab::SMT::location& l, const std::string& m) {
  LOG(FATAL)<<"error: " << l << " : " << m;
}

//void Driver::solveAst() {
//	int i = 0;
//	SMT::PostImageComputer solver(symbol_table);
//	solver.visit(script);
//
//	for (i = i + 1; i < 1 and symbol_table->is_all_assertions_valid(); i++) {
//		std::cout << "additional iteration: " << i << std::endl;
//		symbol_table->pop_scope();
//		SMT::PostImageComputer solver(symbol_table);
//		solver.visit(script);
//	}
//}0--7

}
