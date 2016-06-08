/*
 * Driver.cpp
 *
 *  Created on: Nov 17, 2014
 *      Author: baki
 */

#include "Driver.h"

#include <boost/multiprecision/detail/default_ops.hpp>
#include <boost/multiprecision/detail/et_ops.hpp>
#include <boost/multiprecision/detail/number_base.hpp>
#include <boost/multiprecision/number.hpp>
#include <glog/logging.h>
#include <cstdlib>
#include <fstream>
#include <utility>

#include "options/Theory.h"
#include "parser/location.hh"
#include "parser/parser.hpp"
#include "parser/Scanner.h"
#include "smt/ast.h"
#include "solver/Ast2Dot.h"
#include "solver/ConstraintSolver.h"
#include "solver/ConstraintSorter.h"
#include "solver/DependencySlicer.h"
#include "solver/Initializer.h"
#include "solver/SyntacticOptimizer.h"
#include "solver/SyntacticProcessor.h"
#include "theory/BinaryIntAutomaton.h"
#include "theory/IntAutomaton.h"
#include "theory/StringAutomaton.h"

namespace Vlab {

//const Log::Level Driver::TAG = Log::DRIVER;
bool Driver::IS_LOGGING_INITIALIZED = false;

Driver::Driver()
    : script_ (nullptr),
      symbol_table_ (nullptr),
      constraint_information_ (nullptr) {
}

Driver::~Driver() {
  delete symbol_table_;
  delete script_;
  delete constraint_information_;
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
  LOG(ERROR)<< m;
}

int Driver::parse(std::istream* in) {
  SMT::Scanner scanner(in);
  //	scanner.set_debug(trace_scanning);
  SMT::Parser parser(script_, scanner);
  //	parser.set_debug_level (trace_parsing);
  int res = parser.parse();
  CHECK_EQ(0, res)<< "Syntax error";
  return res;
}

void Driver::ast2dot(std::ostream* out) {

  Solver::Ast2Dot ast2dot(out);
  ast2dot.start(script_);
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

  symbol_table_ = new Solver::SymbolTable();
  constraint_information_ = new Solver::ConstraintInformation();

  Solver::Initializer initializer(script_, symbol_table_);
  initializer.start();

  Solver::SyntacticProcessor syntactic_processor(script_);
  syntactic_processor.start();

  //Dependency Checker calls to cache!

  //Solver::DependencyChecker checker(symbol_table);
  //checker.start();

  Solver::SyntacticOptimizer syntactic_optimizer(script_, symbol_table_);
  syntactic_optimizer.start();

  Solver::DependencySlicer dependency_slicer(script_, symbol_table_, constraint_information_);
  dependency_slicer.start();

//  Solver::VariableOptimizer variable_optimizer(script, symbol_table);
//  variable_optimizer.start();
//
//  Solver::FormulaOptimizer formula_optimizer(script, symbol_table);
//  formula_optimizer.start();
//
  Solver::ConstraintSorter constraint_sorter(script_, symbol_table_);
  constraint_sorter.start();
}

void Driver::solve() {

  Solver::ConstraintSolver constraint_solver(script_, symbol_table_, constraint_information_);
  constraint_solver.start();

  for (auto& pair : symbol_table_->getVariables()) {
    DVLOG(0) << *pair.second;
  }
  // TODO iterate to handle over-approximation
}

bool Driver::isSatisfiable() {
  return symbol_table_->isSatisfiable();
}

boost::multiprecision::cpp_int Driver::Count(std::string var_name, const double bound, bool count_less_than_or_equal_to_bound) {
  symbol_table_->unionValuesOfVariables(script_);
  symbol_table_->push_scope(script_);
  Vlab::Solver::Value_ptr var_value = symbol_table_->getValue(var_name);
  symbol_table_->pop_scope();
  boost::multiprecision::cpp_int result;
  switch (var_value->getType()) {
    case Vlab::Solver::Value::Type::STRING_AUTOMATON:
      result = var_value->getStringAutomaton()->Count(bound, count_less_than_or_equal_to_bound);
      break;
    case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
      auto binary_auto = var_value->getBinaryIntAutomaton();
      result = binary_auto->Count(bound, count_less_than_or_equal_to_bound);
      int number_of_int_variables = symbol_table_->get_num_of_variables(SMT::Variable::Type::INT);
      int number_of_substituted_int_variables = symbol_table_->get_num_of_substituted_variables(script_, SMT::Variable::Type::INT);
      int number_of_untracked_int_variables = number_of_int_variables - number_of_substituted_int_variables
          - binary_auto->getNumberOfVariables();
      if (number_of_untracked_int_variables > 0) {
        int exponent = bound;
        if (Option::Solver::LIA_NATURAL_NUMBERS_ONLY) {
          --exponent;
        }
        result = result
            * boost::multiprecision::pow(boost::multiprecision::cpp_int(2),
                                         (number_of_untracked_int_variables * static_cast<int>(exponent)));
      }
      break;
    }
    default:
      break;
  }

  return result;
}

/**
 * Binary Integer Automaton Count
 */
boost::multiprecision::cpp_int Driver::Count(const int bound, bool count_less_than_or_equal_to_bound) {
  std::string var_name(Solver::SymbolTable::ARITHMETIC);
  return Count(var_name, bound, count_less_than_or_equal_to_bound);
}

boost::multiprecision::cpp_int Driver::SymbolicCount(std::string var_name, const double bound, bool count_less_than_or_equal_to_bound) {
  boost::multiprecision::cpp_int result;
  symbol_table_->unionValuesOfVariables(script_);
  symbol_table_->push_scope(script_);
  Vlab::Solver::Value_ptr var_value = symbol_table_->getValue(var_name);
  symbol_table_->pop_scope();
  switch (var_value->getType()) {
    case Vlab::Solver::Value::Type::STRING_AUTOMATON:
      result = var_value->getStringAutomaton()->SymbolicCount(bound, count_less_than_or_equal_to_bound);
      break;
    case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
      auto binary_auto = var_value->getBinaryIntAutomaton();
      result = binary_auto->SymbolicCount(bound, count_less_than_or_equal_to_bound);
      int number_of_int_variables = symbol_table_->get_num_of_variables(SMT::Variable::Type::INT);
      int number_of_substituted_int_variables = symbol_table_->get_num_of_substituted_variables(script_, SMT::Variable::Type::INT);
      int number_of_untracked_int_variables = number_of_int_variables - number_of_substituted_int_variables
          - binary_auto->getNumberOfVariables();
      if (number_of_untracked_int_variables > 0) {
        int exponent = bound;
        if (Option::Solver::LIA_NATURAL_NUMBERS_ONLY) {
          --exponent;
        }
        result = result
            * boost::multiprecision::pow(boost::multiprecision::cpp_int(2),
                                         (number_of_untracked_int_variables * static_cast<int>(exponent)));
      }
      break;
    }
    default:
      break;
  }

  return result;
}

boost::multiprecision::cpp_int Driver::SymbolicCount(const int bound, bool count_less_than_or_equal_to_bound) {
  std::string var_name(Solver::SymbolTable::ARITHMETIC);
  return SymbolicCount(var_name, bound, count_less_than_or_equal_to_bound);
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

  LOG(INFO)<< "result rendered? " << r << " : " << dot_cmd;
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
      value->getBinaryIntAutomaton()->toDot(out, false);
      break;
    default:
      break;
  }
}

std::map<SMT::Variable_ptr, Solver::Value_ptr> Driver::getSatisfyingVariables() {
  symbol_table_->unionValuesOfVariables(script_);
  return symbol_table_->getValuesAtScope(script_);
}

std::map<std::string, std::string> Driver::getSatisfyingExamples() {
  std::map<std::string, std::string> results;
  for (auto& variable_entry : getSatisfyingVariables()) {
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
  delete symbol_table_;
  delete script_;
  script_ = nullptr;
  symbol_table_ = nullptr;
//  LOG(INFO) << "Driver reseted.";
}

void Driver::setOption(Option::Name option, bool value) {
  switch (option) {
    case Option::Name::MODEL_COUNTER_ENABLED:
      Option::Solver::MODEL_COUNTER_ENABLED = value;
      break;
    case Option::Name::LIA_ENGINE_ENABLED:
      Option::Solver::LIA_ENGINE_ENABLED = value;
      break;
    case Option::Name::LIA_NATURAL_NUMBERS_ONLY:
      Option::Solver::LIA_NATURAL_NUMBERS_ONLY = value;
      break;
    default:
      LOG(ERROR)<< "option not recognized: " << static_cast<int>(option) << " -> " << value;
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
      LOG(ERROR)<< "option not recognized: " << static_cast<int>(option) << " -> " << value;
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

//  Theory::StringAutomaton_ptr str_auto_1 = Theory::StringAutomaton::makeRegexAuto("(ab[c-d]|fe)");
//  str_auto_1->inspectAuto();
//  str_auto_1->inspectBDD();
//  str_auto_1->Count(5);
//  str_auto_1->Count(5,false);

//  Theory::IntAutomaton_ptr int_auto = str_auto_1->parseToIntAutomaton();
//  int_auto->inspectAuto();
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
