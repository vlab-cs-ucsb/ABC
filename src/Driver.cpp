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
	: script (nullptr), symbol_table (nullptr) {
}

Driver::~Driver() {
	delete script;
}

void Driver::error (const std::string& m) {
  std::cerr << m << std::endl;
}

int Driver::parse (std::istream* in) {
	SMT::Scanner scanner(in);
//	scanner.set_debug(trace_scanning);
	SMT::Parser parser (script, scanner);
//	parser.set_debug_level (trace_parsing);
	int res = parser.parse ();
	CHECK_EQ(0, res);
	return res;
}

void Driver::ast2dot(std::ostream* out) {

	Solver::Ast2Dot ast2dot(out);
	ast2dot.start(script);
}
void Driver::ast2dot(std::string file_name) {
	std::ofstream outfile(file_name.c_str());
	if ( !outfile.good() ) { std::cout << "cannot open file: " << file_name << std::endl; exit(2); }
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

}

void Driver::error(const Vlab::SMT::location& l, const std::string& m) {
	LOG(FATAL) << "error: " << l << " : " << m;
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
