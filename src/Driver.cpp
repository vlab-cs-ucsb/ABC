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
    : script_(nullptr),
      symbol_table_(nullptr),
      constraint_information_(nullptr),
      is_model_counter_cached_ { false } {
}

Driver::~Driver() {
  delete symbol_table_;
  delete script_;
  delete constraint_information_;
}

void Driver::InitializeLogger(int log_level) {
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

int Driver::Parse(std::istream* in) {
  SMT::Scanner scanner(in);
  //  scanner.set_debug(trace_scanning);
  SMT::Parser parser(script_, scanner);
  //  parser.set_debug_level (trace_parsing);
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

void Driver::InitializeSolver() {

  symbol_table_ = new Solver::SymbolTable();
  constraint_information_ = new Solver::ConstraintInformation();

  Solver::Initializer initializer(script_, symbol_table_);
  initializer.start();

  std::string output_root {"./output"};
  //ast2dot(output_root + "/post_initializer.dot");
  //std::cin.get();

  Solver::SyntacticProcessor syntactic_processor(script_);
  syntactic_processor.start();

  //ast2dot(output_root + "/post_syntactic_processor.dot");
  //std::cin.get();

  Solver::SyntacticOptimizer syntactic_optimizer(script_, symbol_table_);
  syntactic_optimizer.start();

  //ast2dot(output_root + "/post_syntactic_optimizer.dot");
  //std::cin.get();

  //int count = 0;
  if (Option::Solver::ENABLE_EQUIVALENCE_CLASSES) {
    Solver::EquivalenceGenerator equivalence_generator(script_, symbol_table_);
    do {
      equivalence_generator.start();
      //std::string filename = output_root + "/post_equivalence_" + std::to_string(count) + ".dot";
      //ast2dot(filename);
      //count++;
      //std::cin.get();
    } while (equivalence_generator.has_constant_substitution());
  }

  //ast2dot(output_root + "/post_equivalence.dot");

  Solver::DependencySlicer dependency_slicer(script_, symbol_table_, constraint_information_);
	dependency_slicer.start();

	//ast2dot(output_root + "/post_dependency_slicer.dot");

  if (Option::Solver::ENABLE_IMPLICATIONS) {
    Solver::ImplicationRunner implication_runner(script_, symbol_table_, constraint_information_);
    implication_runner.start();
    //ast2dot(output_root + "/post_implication_runner.dot");
  }

  Solver::FormulaOptimizer formula_optimizer(script_, symbol_table_);
  formula_optimizer.start();

  //ast2dot(output_root + "/post_formula_optimizer.dot");
	//std::cin.get();

  if (Option::Solver::ENABLE_SORTING_HEURISTICS) {
    Solver::ConstraintSorter constraint_sorter(script_, symbol_table_);
    constraint_sorter.start();
  }
}

void Driver::Solve() {
//  TODO move arithmetic formula generation and string relation generation here to guide constraint solving better
//
//  Solver::ArithmeticFormulaGenerator arithmetic_formula_generator(script_, symbol_table_, constraint_information_);
//  arithmetic_formula_generator.start();

  Solver::ConstraintSolver constraint_solver(script_, symbol_table_, constraint_information_);
  constraint_solver.start();
}

bool Driver::is_sat() {
  return symbol_table_->isSatisfiable();
}

Theory::BigInteger Driver::CountVariable(const std::string var_name, const unsigned long bound) {
  return GetModelCounterForVariable(var_name).Count(bound, bound);
}

Theory::BigInteger Driver::CountInts(const unsigned long bound) {
  return GetModelCounter().CountInts(bound);
}

Theory::BigInteger Driver::CountStrs(const unsigned long bound) {
  return GetModelCounter().CountStrs(bound);
}

Theory::BigInteger Driver::Count(const unsigned long int_bound, const unsigned long str_bound) {
  return CountInts(int_bound) * CountStrs(str_bound);
}

Solver::ModelCounter& Driver::GetModelCounterForVariable(const std::string var_name) {
  auto variable = symbol_table_->get_variable(var_name);
  auto representative_variable = symbol_table_->get_representative_variable_of_at_scope(script_, variable);

  auto it = variable_model_counter_.find(representative_variable);
  if (it == variable_model_counter_.end()) {
    SetModelCounterForVariable(var_name);
    it = variable_model_counter_.find(representative_variable);
  }
  return it->second;
}

Solver::ModelCounter& Driver::GetModelCounter() {
  if (not is_model_counter_cached_) {
    SetModelCounter();
  }
  return model_counter_;
}

void Driver::SetModelCounterForVariable(const std::string var_name) {
  auto variable = symbol_table_->get_variable(var_name);
  auto representative_variable = symbol_table_->get_representative_variable_of_at_scope(script_, variable);

  //auto var_value = symbol_table_->get_projected_value_at_scope(script_, representative_variable);
  auto var_value = symbol_table_->get_value_at_scope(script_, representative_variable);

  // test get_models
  auto models = var_value->getStringAutomaton()->GetModelsWithinBound(100,-1);

  auto& mc = variable_model_counter_[representative_variable];
  mc.set_use_sign_integers(Option::Solver::USE_SIGNED_INTEGERS);
  mc.set_count_bound_exact(Option::Solver::COUNT_BOUND_EXACT);
  if (var_value == nullptr) {
    if (SMT::Variable::Type::INT == representative_variable->getType()) {
      mc.set_num_of_unconstraint_int_vars(1);
    } else if (SMT::Variable::Type::STRING == representative_variable->getType()) {
      mc.set_num_of_unconstraint_str_vars(1);
    }
  } else {
    switch (var_value->getType()) {
      case Vlab::Solver::Value::Type::STRING_AUTOMATON:
        mc.add_symbolic_counter(var_value->getStringAutomaton()->GetSymbolicCounter());
        break;
      case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON:
        mc.add_symbolic_counter(var_value->getBinaryIntAutomaton()->GetSymbolicCounter());
        break;
      case Vlab::Solver::Value::Type::INT_AUTOMATON:
        mc.add_symbolic_counter(var_value->getIntAutomaton()->GetSymbolicCounter());
        break;
      case Vlab::Solver::Value::Type::INT_CONSTANT:
        mc.add_constant(var_value->getIntConstant());
        break;
      default:
        LOG(FATAL)<< "add unhandled type: " << static_cast<int>(var_value->getType());
        break;
      }
    }
  }

  /**
   * TODO add string part as well
   */
void Driver::SetModelCounter() {
  model_counter_.set_use_sign_integers(Option::Solver::USE_SIGNED_INTEGERS);
  int num_bin_var = 0;
  for (const auto &variable_entry : getSatisfyingVariables()) {
    if (variable_entry.second == nullptr) {
      continue;
    }
    switch (variable_entry.second->getType()) {
      case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
        auto binary_auto = variable_entry.second->getBinaryIntAutomaton();
        auto formula = binary_auto->GetFormula();
        for (auto& el : formula->GetVariableCoefficientMap()) {
          if (symbol_table_->get_variable_unsafe(el.first) != nullptr) {
            ++num_bin_var;
          }
        }
        model_counter_.add_symbolic_counter(binary_auto->GetSymbolicCounter());
      }
        break;
      case Vlab::Solver::Value::Type::INT_CONSTANT: {
        model_counter_.add_constant(variable_entry.second->getIntConstant());
      }
        break;
      case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
				auto string_auto = variable_entry.second->getStringAutomaton();
				model_counter_.add_symbolic_counter(string_auto->GetSymbolicCounter());
      }
      	break;
      case Vlab::Solver::Value::Type::INT_AUTOMATON: {
        auto int_auto = variable_entry.second->getIntAutomaton();
        model_counter_.add_symbolic_counter(int_auto->GetSymbolicCounter());
      }
        break;
      default:
        break;
    }
  }
  std::cin.get();

  int number_of_int_variables = symbol_table_->get_num_of_variables(SMT::Variable::Type::INT);
  int number_of_substituted_int_variables = symbol_table_->get_num_of_substituted_variables(script_,
                                                                                            SMT::Variable::Type::INT);
  int number_of_untracked_int_variables = number_of_int_variables - number_of_substituted_int_variables - num_bin_var;
  model_counter_.set_num_of_unconstraint_int_vars(number_of_untracked_int_variables);
  is_model_counter_cached_ = true;
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
      value->getBinaryIntAutomaton()->ToDot(out, false);
      break;
    default:
      break;
  }
}

std::map<SMT::Variable_ptr, Solver::Value_ptr> Driver::getSatisfyingVariables() const {
  return symbol_table_->get_values_at_scope(script_);
}

std::map<std::string, std::string> Driver::getSatisfyingExamples() {
  std::map<std::string, std::string> results;
  for (auto& variable_entry : getSatisfyingVariables()) {
    if (Solver::Value::Type::BINARYINT_AUTOMATON == variable_entry.second->getType()) {
      std::map<std::string, int> values = variable_entry.second->getBinaryIntAutomaton()->GetAnAcceptingIntForEachVar();
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

void Driver::set_option(const Option::Name option) {
  switch (option) {
    case Option::Name::USE_SIGNED_INTEGERS:
      Option::Solver::USE_SIGNED_INTEGERS = true;
      break;
    case Option::Name::USE_UNSIGNED_INTEGERS:
      Option::Solver::USE_SIGNED_INTEGERS = false;
      break;
    case Option::Name::USE_MULTITRACK_AUTO:
      Option::Solver::USE_MULTITRACK_AUTO = true;
      break;
    case Option::Name::USE_SINGLETRACK_AUTO:
      Option::Solver::USE_MULTITRACK_AUTO = false;
      break;
    case Option::Name::ENABLE_EQUIVALENCE_CLASSES:
      Option::Solver::ENABLE_EQUIVALENCE_CLASSES = true;
      break;
    case Option::Name::DISABLE_EQUIVALENCE_CLASSES:
      Option::Solver::ENABLE_EQUIVALENCE_CLASSES = false;
      break;
    case Option::Name::ENABLE_DEPENDENCY_ANALYSIS:
      Option::Solver::ENABLE_DEPENDENCY_ANALYSIS = true;
      break;
    case Option::Name::DISABLE_DEPENDENCY_ANALYSIS:
      Option::Solver::ENABLE_DEPENDENCY_ANALYSIS = false;
      break;
    case Option::Name::ENABLE_IMPLICATIONS:
      Option::Solver::ENABLE_IMPLICATIONS = true;
      break;
    case Option::Name::DISABLE_IMPLICATIONS:
      Option::Solver::ENABLE_IMPLICATIONS = false;
      break;
    case Option::Name::LIMIT_LEN_IMPLICATIONS:
      Option::Solver::ENABLE_LEN_IMPLICATIONS = false;
      break;
    case Option::Name::ENABLE_SORTING_HEURISTICS:
      Option::Solver::ENABLE_SORTING_HEURISTICS = true;
      break;
    case Option::Name::DISABLE_SORTING_HEURISTICS:
      Option::Solver::ENABLE_SORTING_HEURISTICS = false;
      break;
    case Option::Name::FORCE_DNF_FORMULA:
    	Option::Solver::FORCE_DNF_FORMULA = true;
    	break;
    case Option::Name::COUNT_BOUND_EXACT:
    	Option::Solver::COUNT_BOUND_EXACT = true;
    	break;
    default:
      LOG(ERROR)<< "option is not recognized: " << static_cast<int>(option);
      break;
    }
  }

void Driver::set_option(const Option::Name option, const int value) {
  switch (option) {
    case Option::Name::REGEX_FLAG:
      Util::RegularExpression::DEFAULT = value;
      break;
    default:
      LOG(ERROR)<< "option is not recognized: " << static_cast<int>(option) << " -> " << value;
      break;
    }
}

void Driver::set_option(const Option::Name option, const std::string value) {
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
      LOG(ERROR)<< "option is not recognized: " << static_cast<int>(option) << " -> " << value;
      break;
    }
}

void Driver::test() {
  return;
//  LOG(INFO) << "DRIVER TEST METHOD";
//  using namespace Theory;
//
//  Theory::BigInteger m ("4");
//  std::cout << m << std::endl;
//
//  std::stringstream os;
//
//  {
//    cereal::BinaryOutputArchive ar(os);
//    Util::Program::save(ar, m);
//  }
//
//  std::cout << os.str() << std::endl;
//
//  std::stringstream is (os.str());
//
//  Theory::BigInteger n;
//  std::cout << n << std::endl;
//  {
//    cereal::BinaryInputArchive ar(is);
//    Util::Program::load(ar, n);
//  }
//  std::cout << n << std::endl;

//  Eigen::SparseMatrix<BigInteger> mm(5,5);
//  Eigen::SparseMatrix<BigInteger> nn;
//
//  Eigen::Triplet<BigInteger> in1(2,3, BigInteger("12345679876543212345678998876655443212345678"));
//  Eigen::Triplet<BigInteger> in2(3,2, BigInteger(5));
//  std::vector<Eigen::Triplet<BigInteger>> tt;
//  tt.push_back(in1);
//  tt.push_back(in2);
//  mm.setFromTriplets(tt.begin(), tt.end());
//  std::cout << mm << std::endl;
//
//
//  std::stringstream oss;
//  {
//    cereal::BinaryOutputArchive ar(oss);
//    Util::Program::save(ar, mm);
//  }
//
//  std::cout << oss.str() << std::endl;
//
//  std::stringstream iss (oss.str());
//
////  std::cout << nn << std::endl;
//  {
//    cereal::BinaryInputArchive ar(iss);
//    Util::Program::load(ar, nn);
//  }
//  std::cout << nn << std::endl;

//  std::cout << "multiply" << std::endl;
//  Eigen::SparseMatrix<BigInteger> result(5,5);
//  result = test * test;
//  std::cout << result << std::endl;
//
//  auto f1 = new ArithmeticFormula();
//  f1->set_type(ArithmeticFormula::Type::EQ);
//  f1->add_variable("x", 1);
//  f1->add_variable("y", 0);
//  f1->set_constant(0);
////
//  auto t1 = BinaryIntAutomaton::MakeAutomaton(f1, false);
//  t1->inspectAuto();

//  SemilinearSet_ptr s1 = new SemilinearSet();
//  s1->set_cycle_head(0);
//  s1->add_periodic_constant(0);
//  s1->set_period(1);
////  s1->add_constant(0);
//  std::cout << *s1 << std::endl;
//  t1 = BinaryIntAutomaton::MakeAutomaton(s1, "x", f1, true);


//  t1->Count(4);
//
//  auto t2 = BinaryIntAutomaton::MakeAnyInt(f1->clone(), true);
//  t2->Count(4);
//
//  auto t2 = BinaryIntAutomaton::MakeAutomaton(f1, false);
//  t2->Count(10, false);
//
//  auto t3 = BinaryIntAutomaton::MakeAutomaton(f1, false);
//  t3->Count(5, false);
//
//  auto t4 = BinaryIntAutomaton::MakeAutomaton(f1, false);
//  t4->Count(20, false);
//
//  auto t5 = BinaryIntAutomaton::MakeAutomaton(f1, false);
//  t5->Count(2, false);
//  t5->Count(10, false);
//  t5->Count(5, false);
//  t5->Count(20, false);
//
//  auto f2 = new ArithmeticFormula();
//  f2->set_type(ArithmeticFormula::Type::EQ);
//  f2->set_constant(0);
//  f2->add_variable("x", 1);
//  f2->add_variable("y", 0);
//
//  auto t2 = BinaryIntAutomaton::MakeAutomaton(f2, false);
//  t2->inspectAuto();
//
//  auto t3 = t1->Union(t2);
//  t3->inspectAuto();
//  for (auto& el : t3->GetAnAcceptingIntForEachVar()) {
//    std::cout << el.first << " : " << el.second << std::endl;
//  }

//    int indices[4] = {0,1,2,3};
//    Theory::StringAutomaton_ptr test = Theory::StringAutomaton::makeAnyString(4, indices);
//    test->inspectAuto(true, true);
//    test->inspectBDD();

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

//  Theory::StringAutomaton_ptr str_auto_1 = Theory::StringAutomaton::makeRegexAuto("ad");
//  auto result = str_auto_1->getAnAcceptingString();
//  for (auto c : result) {
//    std::cout << c << std::endl;
//  }
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

//  StringAutomaton_ptr any_string = Theory::StringAutomaton::makeAnyString();
//  StringAutomaton_ptr regex_auto = StringAutomaton::makeRegexAuto("(..)*");
//  IntAutomaton_ptr len_auto = regex_auto->length();
//
//  StringAutomaton_ptr char_at_auto = any_string->CharAt(len_auto);
//  char_at_auto->inspectAuto(false, true);



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
//  int i = 0;
//  SMT::PostImageComputer solver(symbol_table);
//  solver.visit(script);
//
//  for (i = i + 1; i < 1 and symbol_table->is_all_assertions_valid(); i++) {
//    std::cout << "additional iteration: " << i << std::endl;
//    symbol_table->pop_scope();
//    SMT::PostImageComputer solver(symbol_table);
//    solver.visit(script);
//  }
//}0--7

}
