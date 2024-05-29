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
  bound_decrease_ = 0;
}

Driver::~Driver() {
  delete symbol_table_;
  delete script_;
  delete constraint_information_;
  Theory::Automaton::CleanUp();
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
  SMT::Parser parser(script_, scanner);
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

  Solver::SyntacticProcessor syntactic_processor(script_);
  syntactic_processor.start();

  // last parameter is if we try to optimized ite terms 
  Solver::SyntacticOptimizer syntactic_optimizer(script_, symbol_table_, not Option::Solver::ENABLE_EQUIVALENCE_CLASSES);
  syntactic_optimizer.start();

  int count = 0;
  if (Option::Solver::ENABLE_EQUIVALENCE_CLASSES) {
    Solver::EquivalenceGenerator equivalence_generator(script_, symbol_table_);
    do {
      equivalence_generator.start();
    } while (equivalence_generator.has_constant_substitution());

    // optimize ite now that equivalences have been propagated
    
    Solver::SyntacticOptimizer syntactic_optimizer2(script_, symbol_table_, true);
    syntactic_optimizer2.start();

    Solver::EquivalenceGenerator equivalence_generator2(script_, symbol_table_);
    do {
      equivalence_generator2.start();
    } while (equivalence_generator2.has_constant_substitution());

    Solver::SyntacticProcessor syntactic_processor2(script_);
    syntactic_processor2.start();
  } else {

  }

  Solver::DependencySlicer dependency_slicer(script_, symbol_table_, constraint_information_);
	dependency_slicer.start();

  if (Option::Solver::ENABLE_IMPLICATIONS) {
    Solver::ImplicationRunner implication_runner(script_, symbol_table_, constraint_information_);
    implication_runner.start();
  }

  Solver::FormulaOptimizer formula_optimizer(script_, symbol_table_);
  formula_optimizer.start();

  if (Option::Solver::ENABLE_SORTING_HEURISTICS) {
    Solver::ConstraintSorter constraint_sorter(script_, symbol_table_);
    constraint_sorter.start();
  }

}

void Driver::Solve() {
  Solver::ConstraintSolver constraint_solver(script_, symbol_table_, constraint_information_);
  constraint_solver.start();
  is_model_counter_cached_ = false;
  model_counter_ = Solver::ModelCounter();
}

bool Driver::is_sat() {
  return symbol_table_->isSatisfiable();
}

/*
 * TODO: Fix issue when bound is small and counting a single variable, tuple count to returns 0 but projected count is nonzero
 */
Theory::BigInteger Driver::CountVariable(const std::string var_name, const unsigned long bound) {
  Theory::BigInteger projected_count, tuple_count;
  tuple_count = GetModelCounterForVariable(var_name,false).Count(bound, bound);
  projected_count = GetModelCounterForVariable(var_name,true).Count(bound, bound);
  return (projected_count < tuple_count) ? projected_count : tuple_count;
  // return GetModelCounterForVariable(var_name,true).Count(bound, bound);
}

Theory::BigInteger Driver::CountInts(const unsigned long bound) {
  return GetModelCounter().CountInts(bound);
}

Theory::BigInteger Driver::CountInts(const unsigned long bound, std::vector<std::string> count_tuple_variables) {
  LOG(FATAL) << "Not yet implemented";
  return GetModelCounter().CountInts(bound);
}

Theory::BigInteger Driver::CountStrs(const unsigned long bound) {
  return GetModelCounter().CountStrs(bound);
}

Theory::BigInteger Driver::CountStrs(const unsigned long bound, std::vector<std::string> count_tuple_variables) {
  Theory::BigInteger projected_count, tuple_count;

  if(count_tuple_variables.size() == 0) {
    return CountStrs(bound);
  } else if(count_tuple_variables.size() == 1) {
    return CountVariable(count_tuple_variables[0],bound);
  }

  std::string v1 = count_tuple_variables[0];
  std::string v2 = count_tuple_variables[1];
  

  auto variable = symbol_table_->get_variable(v1);
  auto representative_variable = symbol_table_->get_representative_variable_of_at_scope(script_, variable);
  Solver::Value_ptr var_value = symbol_table_->get_value_at_scope(script_,representative_variable);

  auto str_auto = var_value->getStringAutomaton()->clone();
  auto f = str_auto->GetFormula();

  Theory::StringAutomaton_ptr temp_auto = nullptr;
  for(auto it : f->GetVariableCoefficientMap()) {
    if(it.first != v1 and it.first != v2) {
      temp_auto = str_auto->ProjectAwayVariable(it.first);
      delete str_auto;
      str_auto = temp_auto;
    }
  }

  // for(auto it : str_auto->GetFormula()->GetVariableCoefficientMap()) {
  //   LOG(INFO) << it.first;
  // }

  // std::cin.get();

  Solver::ModelCounter mc;
  mc.add_symbolic_counter(str_auto->GetSymbolicCounter());
  return mc.Count(bound,bound);

}

Theory::BigInteger Driver::Count(const unsigned long int_bound, const unsigned long str_bound) {
  return CountInts(int_bound) * CountStrs(str_bound);
}

Solver::ModelCounter& Driver::GetModelCounterForVariable(const std::string var_name, bool project) {
  auto variable = symbol_table_->get_variable(var_name);
  auto representative_variable = symbol_table_->get_representative_variable_of_at_scope(script_, variable);

//  auto it = variable_model_counter_.find(representative_variable);
//  if (it == variable_model_counter_.end()) {
    SetModelCounterForVariable(var_name,project);
    auto it = variable_model_counter_.find(representative_variable);
  //}
  return it->second;
}

Solver::ModelCounter& Driver::GetModelCounter() {
  if (not is_model_counter_cached_) {
    SetModelCounter();
  }
  return model_counter_;
}

int Driver::GetNumIntVariables() {
  auto variables = symbol_table_->get_variables();
  int count = 0;

  for(auto it : variables) {
    if(SMT::Variable::Type::INT == it.second->getType()) {
      count++;
    }
  }

  return count;
}

int Driver::GetNumStrVariables() {
  auto variables = symbol_table_->get_variables();
  int count = 0;

  for(auto it : variables) {
    if(SMT::Variable::Type::STRING == it.second->getType()) {
      count++;
    }
  }

  return count;
}

void Driver::SetModelCounterForVariable(const std::string var_name, bool project) {
  auto variable = symbol_table_->get_variable(var_name);
  auto representative_variable = symbol_table_->get_representative_variable_of_at_scope(script_, variable);
  Solver::Value_ptr var_value = nullptr;

  if(project) {
  	var_value = symbol_table_->get_projected_value_at_scope(script_, representative_variable);
  } else {
  	var_value = symbol_table_->get_value_at_scope(script_, representative_variable);
  }

  // test get_models
  //auto models = var_value->getStringAutomaton()->GetModelsWithinBound(100,-1);
//  auto models = var_value->getBinaryIntAutomaton()->GetModelsWithinBound(100,-1);
  if(variable_model_counter_.find(representative_variable) != variable_model_counter_.end()) {
  	variable_model_counter_.erase(representative_variable);
  }

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
  int num_str_var = 0;

  for (const auto &variable_entry : getSatisfyingVariables()) {
    // LOG(INFO) << *variable_entry.first;
    if (variable_entry.second == nullptr || symbol_table_->is_sorted_variable(variable_entry.first)) {
      continue;
    }

    
    // LOG(INFO) << "    IS VALID";
    
    switch (variable_entry.second->getType()) {
      case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
        auto binary_auto = variable_entry.second->getBinaryIntAutomaton();
        auto formula = binary_auto->GetFormula();
        bool has_actual_var = false;
        
        std::vector<std::string> vars_to_project;

        // LOG(INFO) << "VARIABLE: " << variable_entry.first;
        for (auto& el : formula->GetVariableCoefficientMap()) {
          // LOG(INFO) << "  has " << el.first << " at track " << formula->GetVariableIndex(el.first);
          if (symbol_table_->get_variable_unsafe(el.first) != nullptr) {
            ++num_bin_var;
            has_actual_var = true;
          } else {
            vars_to_project.push_back(el.first);
          }
        }

        // LOG(INFO) << "FOR VARIABLE: " << variable_entry.first;

        // binary_auto->inspectAuto(false,true);


        for(auto var : vars_to_project) {
          // LOG(INFO) << "  projecting away " << var;
          auto tmp = binary_auto;
          tmp = binary_auto->ProjectAwayVariable(var);
          delete binary_auto;
          binary_auto = tmp;
        }

        variable_entry.second->setData(binary_auto);
        // binary_auto->inspectAuto(false,true);

        // LOG(INFO) << binary_auto->Count(50);

        // LOG(INFO) << " IS EMPTY ? " << binary_auto->IsEmptyLanguage();

        if(has_actual_var) {
          // LOG(INFO) << "HAS ACTUAL VAR";
          model_counter_.add_symbolic_counter(binary_auto->GetSymbolicCounter());
          // LOG(INFO) << "countints = " << model_counter_.CountInts(5000);
        } else {
          // LOG(INFO) << "NO ACTUAL VAR";
        }
      }
        break;
      case Vlab::Solver::Value::Type::INT_CONSTANT: {
        model_counter_.add_constant(variable_entry.second->getIntConstant());
      }
        break;
      case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
				auto string_auto = variable_entry.second->getStringAutomaton();
        auto formula = string_auto->GetFormula()->clone();

        // string_auto->inspectAuto(false,false);

        for (auto& el : formula->GetVariableCoefficientMap()) {
          if (symbol_table_->get_variable_unsafe(el.first) != nullptr) {
            auto v = symbol_table_->get_variable(el.first);
            if(symbol_table_->is_sorted_variable(v)) {

              string_auto = string_auto->ProjectAwayVariable(el.first);
            }
            ++num_str_var;
          }
        }

        // string_auto->inspectAuto(false,false);


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

  int number_of_int_variables = symbol_table_->get_num_of_variables(SMT::Variable::Type::INT);
  int number_of_substituted_int_variables = symbol_table_->get_num_of_substituted_variables(script_,
                                                                                            SMT::Variable::Type::INT);
  int number_of_untracked_int_variables = number_of_int_variables - number_of_substituted_int_variables - num_bin_var;
  model_counter_.set_num_of_unconstraint_int_vars(number_of_untracked_int_variables);

  int number_of_str_variables = symbol_table_->get_num_of_variables(SMT::Variable::Type::STRING);
  int number_of_substituted_str_variables = symbol_table_->get_num_of_substituted_variables(script_,
                                                                                            SMT::Variable::Type::STRING);
  int number_of_untracked_str_variables = number_of_str_variables - number_of_substituted_str_variables - num_str_var;
  model_counter_.set_num_of_unconstraint_str_vars(number_of_untracked_str_variables);

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
    } else if(Solver::Value::Type::STRING_AUTOMATON == variable_entry.second->getType()) {
    	auto string_auto = variable_entry.second->getStringAutomaton();
    	auto string_formula = string_auto->GetFormula();
    	for(auto it : string_formula->GetVariableCoefficientMap()) {
    		auto single_string_auto = string_auto->GetAutomatonForVariable(it.first);
    		results[it.first] = single_string_auto->GetAnAcceptingString();
    		delete single_string_auto;
    	}

    	
    } else {
      results[variable_entry.first->getName()] = variable_entry.second->getASatisfyingExample();
    }
  }
  return results;
}

std::map<std::string, std::string> Driver::getSatisfyingExamplesRandom() {
  std::map<std::string, std::string> results;


  // check to see if we've cached automata/projected-automata for variables first
  // otherwise get from symbol table
  // SHOULD ONLY BE EMPTY RIGHT AFTER SOLVING, ONLY STRING AUTOMATA
  if(not cached_values_.empty()) {
  	for(auto it : cached_values_) {
  		results[it.first] = cached_values_[it.first]->getStringAutomaton()->GetAnAcceptingStringRandom();
  	}
  } else {
		for (auto& variable_entry : getSatisfyingVariables()) {
			if(Solver::Value::Type::STRING_AUTOMATON == variable_entry.second->getType()) {
				auto string_auto = variable_entry.second->getStringAutomaton();
				auto string_formula = string_auto->GetFormula();
				for(auto it : string_formula->GetVariableCoefficientMap()) {
					auto single_string_auto = string_auto->GetAutomatonForVariable(it.first);
					results[it.first] = single_string_auto->GetAnAcceptingStringRandom();
					cached_values_[it.first] = new Solver::Value(single_string_auto);
				}
			}
		}
  }
  return results;
}

std::map<std::string, std::string> Driver::getSatisfyingExamplesRandomBounded(const int bound) {
  std::map<std::string, std::string> results;

  // check to see if we've cached automata/projected-automata for variables first
  // otherwise get from symbol table
  // SHOULD ONLY BE EMPTY RIGHT AFTER SOLVING, ONLY STRING AUTOMATA
  if(not cached_bounded_values_.empty()) {
  	for(auto it : cached_bounded_values_) {
  		results[it.first] = cached_bounded_values_[it.first]->getStringAutomaton()->GetAnAcceptingStringRandom();
  	}
  } else {
		for (auto& variable_entry : getSatisfyingVariables()) {
			if(Solver::Value::Type::STRING_AUTOMATON == variable_entry.second->getType()) {
				auto string_auto = variable_entry.second->getStringAutomaton();
				auto string_formula = string_auto->GetFormula();
				for(auto it : string_formula->GetVariableCoefficientMap()) {
					auto single_string_auto = string_auto->GetAutomatonForVariable(it.first);
          auto length_auto = Theory::StringAutomaton::MakeAnyStringLengthLessThanOrEqualTo(bound);
					auto single_string_auto_bounded = single_string_auto->Intersect(length_auto);
          delete length_auto;
					delete single_string_auto;
          if(single_string_auto_bounded->IsEmptyLanguage()) {
            delete single_string_auto_bounded;
            single_string_auto_bounded = nullptr;
            continue;
          }
					results[it.first] = single_string_auto_bounded->GetAnAcceptingStringRandom();
					cached_bounded_values_[it.first] = new Solver::Value(single_string_auto_bounded);
				}
			}
		}
  }
  return results;
}

void Driver::reset() {
	for(auto &iter : cached_values_) {
		delete iter.second;
		iter.second = nullptr;
	}
	cached_values_.clear();

	for(auto &iter : cached_bounded_values_) {
		delete iter.second;
		iter.second = nullptr;
	}
	cached_bounded_values_.clear();

  delete symbol_table_;
  delete script_;
  script_ = nullptr;
  symbol_table_ = nullptr;
//  LOG(INFO) << "Driver reseted.";
}

std::vector<std::string> Driver::GetSimpleRegexes(std::string re_var, int num_regexes, int alpha, int omega) {
  auto var = symbol_table_->get_variable(re_var);
  auto var_val = symbol_table_->get_value_at_scope(script_,var);
  auto var_val_auto = var_val->getStringAutomaton();

  // var_val_auto->inspectAuto(false,false);

  Util::RegularExpression_ptr regex = var_val_auto->DFAToRE();
  std::vector<std::string> regex_strings;


  //LOG(INFO) << "original:";
  //LOG(INFO) << regex->str();
  
  regex->simplify(alpha,omega,0);

  //LOG(INFO) << "simplified:";
  //LOG(INFO) << regex->str();

  regex_strings = regex->enumerate();
  for(int i = 0; i < regex_strings.size(); i++) {
    std::replace(regex_strings[i].begin(),regex_strings[i].end(),'`','?');
    std::replace(regex_strings[i].begin(),regex_strings[i].end(),'~','*');
  }

  // regex->set_escape(false);
  // regex_strings.push_back(regex->str());
  // regex->set_escape(true);

  return regex_strings;
}

// NOTICE: RESTRICTS OUTPUT TO PRINTABLE ASCII
std::vector<std::string> Driver::GetNumRandomModels(std::vector<std::string> model_variables, unsigned long num_random_models, int min, int max) {
  std::vector<std::string> random_models;
  auto var = symbol_table_->get_variable(model_variables[0]);
  auto var_val = symbol_table_->get_value_at_scope(script_,var);
  auto var_val_auto = var_val->getStringAutomaton();

  auto projected_var_val_auto = var_val_auto->GetAutomatonForVariable(model_variables[0]);
  auto regex_auto = Theory::StringAutomaton::MakeRegexAuto("[ -~]{"+std::to_string(min)+","+std::to_string(max)+"}");
  auto restricted_auto = projected_var_val_auto->Intersect(regex_auto);

  delete regex_auto;
  delete projected_var_val_auto;
  

  if(not restricted_auto->IsEmptyLanguage()) {
    for(unsigned long i = 0; i < num_random_models; i++) {
      std::string random_model = restricted_auto->GetAnAcceptingStringRandom();
      random_models.push_back(random_model);
    }
  }

  delete restricted_auto;
  return random_models;
}

// Measure distance between the dfa for the regex, and the dfa for the variable
// ONLY PRINTABLE ASCII CHARACTERS AT THE MOMENT
std::vector<Theory::BigInteger> Driver::MeasureDistance(std::string var_name, std::string var_regex, int bound) {
  auto var = symbol_table_->get_variable(var_name);
  auto var_val = symbol_table_->get_value_at_scope(script_,var);
  auto var_val_auto = var_val->getStringAutomaton();

  auto projected_var_val_auto = var_val_auto->GetAutomatonForVariable(var_name);
  auto regex_auto = Theory::StringAutomaton::MakeRegexAuto(var_regex);

  auto printable_ascii_auto = Theory::StringAutomaton::MakeRegexAuto("[ -~]*");
  auto tmp = projected_var_val_auto->Intersect(printable_ascii_auto);
  delete projected_var_val_auto;
  projected_var_val_auto = tmp;
  tmp = regex_auto->Intersect(printable_ascii_auto);
  delete regex_auto;
  regex_auto = tmp;
  delete printable_ascii_auto;

  auto comp_projected_var_val_auto = projected_var_val_auto->Complement();
  auto comp_regex_auto = regex_auto->Complement();

  auto r1_not_r2 = projected_var_val_auto->Intersect(comp_regex_auto);
  auto not_r1_r2 = comp_projected_var_val_auto->Intersect(regex_auto);


  Solver::ModelCounter mc1,mc2,mc3,mc4;
  mc1.add_symbolic_counter(projected_var_val_auto->GetSymbolicCounter());
  mc2.add_symbolic_counter(regex_auto->GetSymbolicCounter());
  mc3.add_symbolic_counter(r1_not_r2->GetSymbolicCounter());
  mc4.add_symbolic_counter(not_r1_r2->GetSymbolicCounter());

  std::vector<Theory::BigInteger> results;
  results.push_back(mc1.Count(bound,bound));
  results.push_back(mc2.Count(bound,bound));
  results.push_back(mc3.Count(bound,bound));
  results.push_back(mc4.Count(bound,bound));

  delete projected_var_val_auto;
  delete regex_auto;
  delete comp_projected_var_val_auto;
  delete comp_regex_auto;
  delete r1_not_r2;
  delete not_r1_r2;

  return results;
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
    case Option::Name::USE_SINGLE_AUTO:
    	Option::Solver::USE_SINGLE_AUTO = true;
    	break;
    case Option::Name::USE_REGEX_SPLITTER:
    	Option::Solver::USE_REGEX_SPLITTER = true;
    	break;
    case Option::Name::USE_PREFIX_SHORTENER:
    	Option::Solver::USE_PREFIX_SHORTENER = true;
    	break;
    case Option::Name::CONCAT_COLLAPSE_HEURISTIC:
      Option::Solver::CONCAT_COLLAPSE_HEURISTIC = true;
      break;
    case Option::Name::DFA_TO_RE:
      Option::Solver::DFA_TO_RE = true;
      break;
    case Option::Name::GET_NUM_RANDOM_MODELS:
      Option::Solver::GET_NUM_RANDOM_MODELS = true;
      break;
    case Option::Name::COMPARE_REGEX_VARIABLE:
      Option::Solver::COMPARE_REGEX_VARIABLE = true;
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
  //make_string->Complement()->toDotAscii();

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

//  Theory::StringAutomaton_ptr result = a1->Union(any_string);
  //result->toDotAscii();

//  Theory::StringAutomaton_ptr prefs = a1->prefixes();
  //prefs->toDotAscii();

  //Theory::StringAutomaton_ptr length_auto = Theory::StringAutomaton::makeLengthRange(5,-1);
  //length_auto->toDotAscii(1);

//  Theory::StringAutomaton_ptr length_auto = Theory::StringAutomaton::makeLengthRange(0,4);
  //length_auto->toDotAscii();

  //Theory::StringAutomaton_ptr test_auto = a6->union_(a5->union_(a4->Union(a3->Union(a1->concatenate(char_range_closure)->concatenate(a2)))));
//  Theory::StringAutomaton_ptr test_auto = a5->union_(a4->Union(a3->Union(a1->concatenate(char_range)->concatenate(a2))));

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
