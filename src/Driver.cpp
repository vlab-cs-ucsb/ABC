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
  delete symbol_table;
  delete script;
}

// TODO parameterize flags later on
void Driver::initializeABC() {
//  FLAGS_log_dir = log_root;
  FLAGS_v = 19;
  FLAGS_logtostderr = 1;
  google::InitGoogleLogging("ABC.Java.Driver");
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

  Solver::SyntacticProcessor syntactic_processor(script);
  syntactic_processor.start();

  Solver::SyntacticOptimizer syntactic_optimizer(script, symbol_table);
  syntactic_optimizer.start();

  Solver::VariableOptimizer variable_optimizer(script, symbol_table);
  variable_optimizer.start();

  Solver::FormulaOptimizer formula_optimizer(script, symbol_table);
  formula_optimizer.start();

//  SMT::LengthConstraintReductor len_reductor;
//  len_reductor.start(script, symbol_table);

  Solver::ConstraintSorter constraint_sorter(script, symbol_table);
  constraint_sorter.start();
}

void Driver::solve() {
  ast2dot("./output/test.dot");
  Solver::PostImageComputer post_image_computer(script, symbol_table);
  post_image_computer.start();

  // TODO iterate to handle over-approximation
}

bool Driver::isSatisfiable() {
  return symbol_table->isSatisfiable();
}


void Driver::printResult(std::string file_name) {
  std::ofstream outfile(file_name.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file_name << std::endl;
    exit(2);
  }
  printResult(outfile);
}

void Driver::printResult(std::ostream& out) {
  symbol_table->push_scope(script);
  SMT::Variable_ptr variable = symbol_table->getSymbolicVariable();
  Solver::Value_ptr result = symbol_table->getValue(variable);
  result->getStringAutomaton()->toDotAscii(false, out);
}

void Driver::reset() {
  delete symbol_table;
  delete script;
  script = nullptr;
  symbol_table = nullptr;
  LOG(INFO) << "Driver reseted.";
}

void Driver::test() {
  return;
//  Theory::StringAutomaton_ptr str_auto_1 = Theory::StringAutomaton::makePhi();
//  Theory::StringAutomaton_ptr str_auto_2 = Theory::StringAutomaton::makeRegexAuto("(b|a)(k|i)*");
//  Theory::StringAutomaton_ptr str_auto_3 = nullptr;

//  str_auto_3 = str_auto_1->concat(str_auto_2);
//  str_auto_3->inspectAuto();

//  str_auto_3 = str_auto_2->concat(str_auto_1);
//  std::cout << "concat ok" << std::endl;
//  str_auto_3->inspectAuto();



//  non_accepting_auto->inspectAuto(true);

//  Theory::StringAutomaton_ptr any_string = Theory::StringAutomaton::makeAnyString();
//  Theory::StringAutomaton_ptr complement = nullptr;
  //any_string->toDotAscii(1);
//  complement = any_string->complement();
  //complement->toDotAscii(1);

//  Theory::StringAutomaton_ptr a1 = Theory::StringAutomaton::makeString("Hi,");
  //make_string->complement()->toDotAscii();

//  Theory::StringAutomaton_ptr a2 = Theory::StringAutomaton::makeString("World");

//  Theory::StringAutomaton_ptr a3 = Theory::StringAutomaton::makeString("Hello,World");
//  Theory::StringAutomaton_ptr a4 = Theory::StringAutomaton::makeString("Lucas");
//  Theory::StringAutomaton_ptr a5 = Theory::StringAutomaton::makeString("Hello,Lucas");
//  Theory::StringAutomaton_ptr a6 = Theory::StringAutomaton::makeString("Hello");

//  Theory::StringAutomaton_ptr char_range = Theory::StringAutomaton::makeCharRange('3', '3');
  //char_range->toDotAscii(1);

//  Theory::StringAutomaton_ptr char_range_closure  = char_range->kleeneClosure();

//  Theory::StringAutomaton_ptr dot_auto = Theory::StringAutomaton::makeAnyChar();
  //dot_auto->toDotAscii(1);

//  Theory::StringAutomaton_ptr empty_string = Theory::StringAutomaton::makeEmptyString();

//  Theory::StringAutomaton_ptr result = a1->union_(any_string);
  //result->toDotAscii();

//  Theory::StringAutomaton_ptr prefs = a1->prefixes();
  //prefs->toDotAscii();

  //Theory::StringAutomaton_ptr length_auto = Theory::StringAutomaton::makeLengthRange(5,-1);
  //length_auto->toDotAscii(1);

//  Theory::StringAutomaton_ptr length_auto = Theory::StringAutomaton::makeLengthRange(0,4);
  //length_auto->toDotAscii();

  //Theory::StringAutomaton_ptr test_auto = a6->union_(a5->union_(a4->union_(a3->union_(a1->concatenate(char_range_closure)->concatenate(a2)))));
//  Theory::StringAutomaton_ptr test_auto = a5->union_(a4->union_(a3->union_(a1->concatenate(char_range)->concatenate(a2))));


  //Theory::StringAutomaton_ptr result_auto = test_auto->charAt(5);
//  Theory::StringAutomaton_ptr result_auto = test_auto->suffixesFromIndex(12);
  //Theory::StringAutomaton_ptr result_auto = test_auto->prefixesUntilIndex(20);
//  result_auto->toDotAscii();

  //Theory::StringAutomaton_ptr regex_auto = Theory::StringAutomaton::makeRegexAuto("/#/");
  //regex_auto->toDotAscii();

  //Theory::BoolAutomaton_ptr true_auto = Theory::BoolAutomaton::makeTrue();
  //true_auto->toDot();
  //Theory::BoolAutomaton_ptr false_auto = Theory::BoolAutomaton::makeFalse();
  //false_auto->toDot();
  std::exit(0);
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
