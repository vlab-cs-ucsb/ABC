/*
 * Driver.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: baki
 */

#include "Driver.h"

namespace Vlab {

//const Log::Level Driver::TAG = Log::DRIVER;
bool Driver::IS_LOGGING_INITIALIZED = false;

Driver::Driver()
        : script(nullptr), symbol_table(nullptr) {
}

Driver::~Driver() {
  delete symbol_table;
  delete script;
}

void Driver::initializeABC(int log_level) {
//  FLAGS_log_dir = log_root;
  if (!IS_LOGGING_INITIALIZED) {
    FLAGS_v = log_level;
    FLAGS_logtostderr = 1;
    google::InitGoogleLogging("ABC.Java.Driver");
    IS_LOGGING_INITIALIZED = true;
  }
}

void Driver::error(const std::string& m) {
  LOG(ERROR) << m;
}

int Driver::parse(std::istream* in) {
  SMT::Scanner scanner(in);
  //	scanner.set_debug(trace_scanning);
  SMT::Parser parser(script, scanner);
  //	parser.set_debug_level (trace_parsing);
  int res = parser.parse();
  CHECK_EQ(0, res)<< "Syntax error";
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

  Solver::ConstraintSorter constraint_sorter(script, symbol_table);
  constraint_sorter.start();
}

void Driver::solve() {
  Solver::ConstraintSolver constraint_solver(script, symbol_table);
  constraint_solver.start();

  // TODO iterate to handle over-approximation
}

bool Driver::isSatisfiable() {
  return symbol_table->isSatisfiable();
}

std::string Driver::count(std::string var_name, double bound, bool count_less_than_or_equal_to_bound) {
  std::string result;
  symbol_table->unionValuesOfVariables(script);
  symbol_table->push_scope(script);
  Vlab::Solver::Value_ptr var_value = symbol_table->getValue(var_name);
  symbol_table->pop_scope();
  switch (var_value->getType()) {
    case Vlab::Solver::Value::Type::STRING_AUTOMATON:
      result = var_value->getStringAutomaton()->count(bound, count_less_than_or_equal_to_bound);
      break;
    case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON:
      result = var_value->getBinaryIntAutomaton()->count(bound, count_less_than_or_equal_to_bound);
    default:
      break;
  }

  return result;
}

/**
 * Binary Integer Automaton Count
 */
std::string Driver::count(int bound, bool count_less_than_or_equal_to_bound) {
  std::string var_name(Solver::SymbolTable::ARITHMETIC);
  return count(var_name, bound, count_less_than_or_equal_to_bound);
}


void Driver::inspectResult(Solver::Value_ptr value, std::string file_name) {
  std::ofstream outfile(file_name.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file_name << std::endl;
    exit(2);
  }
  printResult(value, outfile);

  std::string dot_cmd("xdot " + file_name + " &");
  int r = std::system(dot_cmd.c_str());

  LOG(INFO) << "result rendered? " << r << " : " << dot_cmd;
}

void Driver::printResult(Solver::Value_ptr value, std::ostream& out) {
  switch (value->getType()) {
    case Solver::Value::Type::STRING_AUTOMATON:
      value->getStringAutomaton()->toDotAscii(false, out);
      break;
    case Solver::Value::Type::INT_AUTOMATON:
      value->getIntAutomaton()->toDotAscii(false, out);
      break;
    case Solver::Value::Type::BINARYINT_AUTOMATON:
      value->getBinaryIntAutomaton()->toDot(out);
      break;
    default:
      break;
  }
}

std::map<SMT::Variable_ptr, Solver::Value_ptr> Driver::getSatisfyingVariables() {
  symbol_table->unionValuesOfVariables(script);
  return symbol_table->getValuesAtScope(script);
}

std::map<std::string, std::string> Driver::getSatisfyingExamples() {
  std::map<std::string, std::string> results;
  for(auto& variable_entry : getSatisfyingVariables()) {
    if (Solver::Value::Type::BINARYINT_AUTOMATON == variable_entry.second->getType()) {
      std::map<std::string, int> values = variable_entry.second->getBinaryIntAutomaton()->getAnAcceptingIntForEachVar();
      for (auto& entry : values) {
        results[entry.first] = std::to_string(entry.second);
      }
    } else {
      results[variable_entry.first->getName()] = variable_entry.second->getASatisfyingExample();
    }
  }
  return results;
}

void Driver::reset() {
  delete symbol_table;
  delete script;
  script = nullptr;
  symbol_table = nullptr;
  LOG(INFO) << "Driver reseted.";
}

void Driver::setOption(Option::Name option, bool value) {
  switch (option) {
    case Option::Name::LIA_ENGINE_ENABLED:
      Option::Solver::LIA_ENGINE_ENABLED = value;
      break;
    case Option::Name::MODEL_COUNTER_ENABLED:
      Option::Solver::MODEL_COUNTER_ENABLED = value;
      break;
    default:
      LOG(ERROR) << "option not recognized: " << static_cast<int>(option) << " -> " << value;
      break;
  }
}

void Driver::setOption(Option::Name option, std::string value) {
  switch (option) {
    case Option::Name::OUTPUT_PATH:
      Option::Solver::OUTPUT_PATH = value;
      Option::Theory::TMP_PATH = value;
      break;
    case Option::Name::SCRIPT_PATH:
      Option::Solver::SCRIPT_PATH = value;
      Option::Theory::SCRIPT_PATH = value;
      break;
    default:
      LOG(ERROR) << "option not recognized: " << static_cast<int>(option) << " -> " << value;
      break;
  }
}

void Driver::test() {
  return;
//  std::map<std::string ,int> eq_1 = {{"x", 0}, {"z", 1}, {"y", 2}};
//  std::vector<int> coeff = {1, 2, 3};
//
//  Theory::ArithmeticFormula formula_2(eq_1, coeff);
//  formula_2.setType(Theory::ArithmeticFormula::Type::EQ);
//  Theory::BinaryIntAutomaton_ptr test_auto = Theory::BinaryIntAutomaton::makeAutomaton(&formula_2);
//
//  test_auto->inspectAuto();
//  test_auto->inspectBDD();

//    Theory::IntAutomaton_ptr int_auto_1 = Theory::IntAutomaton::makeInt(78);
//    std::cout << "int: " << int_auto_1->getAnAcceptingInt() << std::endl;
//    delete int_auto_1;

//  Theory::StringAutomaton_ptr str_auto_1 = Theory::StringAutomaton::makeRegexAuto("a*");
//  str_auto_1->inspectAuto();
//  std::ofstream outfile("./output/testcase.dot");
//  str_auto_1->toDot(outfile, false);
//  Theory::StringAutomaton_ptr str_auto_2 = Theory::StringAutomaton::makeString("b");
//  Theory::StringAutomaton_ptr result = str_auto_1->subStringLastOf(str_auto_2);
//  result->inspectAuto();
//  std::cout << "example: \"" << str_auto_2->getAnAcceptingString() << "\"" << std::endl;
//  Theory::StringAutomaton_ptr str_auto_3 = nullptr;

//  str_auto_2->inspectAuto();
//
//  std::cout << "example: " << str_auto_2->getAnAcceptingString() << std::endl;
//
//  int_auto_1 = str_auto_2->length();
//  std::cout << "int: " << int_auto_1->getAnAcceptingInt() << std::endl;
//  delete int_auto_1;

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
