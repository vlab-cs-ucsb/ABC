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
      is_model_counter_cached_ { false },
			current_id_ {""} {
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


	if(current_id_.empty()) {
		symbol_table_ = new Solver::SymbolTable();
		current_id_ = symbol_table_->get_var_name_for_node(script_,Vlab::SMT::TVariable::Type::NONE);
		incremental_states_[current_id_] = symbol_table_;
		symbol_table_->push_scope(script_);
	} else {
		symbol_table_ = incremental_states_[current_id_];
	}

  constraint_information_ = new Solver::ConstraintInformation();

  Solver::Initializer initializer(script_, symbol_table_);
  initializer.start();

  std::string output_root {"./output"};

  Solver::SyntacticProcessor syntactic_processor(script_);
  syntactic_processor.start();

  Solver::SyntacticOptimizer syntactic_optimizer(script_, symbol_table_);
  syntactic_optimizer.start();

  if (Option::Solver::ENABLE_EQUIVALENCE_CLASSES) {
    Solver::EquivalenceGenerator equivalence_generator(script_, symbol_table_);
    do {
      equivalence_generator.start();
    } while (equivalence_generator.has_constant_substitution());
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

void Driver::GetModels(const unsigned long bound,const unsigned long num_models) {

	LOG(FATAL) << "IMPLEMENT ME";

	//LOG(INFO) << "Numver of satisfying variables: " << getSatisfyingVariables().size();
	std::map<std::string,std::vector<std::string>> variable_values;
	std::map<SMT::Variable_ptr,Solver::Value_ptr> var_vals;

	std::string var_name("var_8");
	auto v8 = symbol_table_->get_variable(var_name);
	auto v8_rep = symbol_table_->get_representative_variable_of_at_scope(script_, v8);
	auto v8_all_solutions = symbol_table_->get_projected_value_at_scope(script_,v8_rep);

	auto v8_n_solutions = v8_all_solutions->getStringAutomaton()->GetModelsWithinBound(num_models,-1);
	LOG(INFO) << 0;
	Theory::StringAutomaton_ptr union_auto = nullptr, t1_auto = nullptr, t2_auto = nullptr;
	for(int i = 0; i < v8_n_solutions["var_8"].size(); i++) {
		t1_auto = Theory::StringAutomaton::MakeString(v8_n_solutions["var_8"][i]);
		if(union_auto == nullptr) {
			union_auto = t1_auto;
		} else {
			t2_auto = union_auto->Union(t1_auto);
			delete union_auto;
			delete t1_auto;
			union_auto = t2_auto;
		}
	}

	var_name = "var_7";
	auto v7_var = symbol_table_->get_variable(var_name);
	auto v7_rep = symbol_table_->get_representative_variable_of_at_scope(script_,v7_var);
	auto v7_all_solutions_val = symbol_table_->get_projected_value_at_scope(script_,v7_rep);

	var_name = "var_6";
	auto v6_var = symbol_table_->get_variable(var_name);
	auto v6_rep = symbol_table_->get_representative_variable_of_at_scope(script_,v6_var);
	auto v6_all_solutions_val = symbol_table_->get_projected_value_at_scope(script_,v6_rep);

	Theory::StringAutomaton_ptr prefix_suffix_auto = Theory::StringAutomaton::MakePrefixSuffix(0,1,2,3);
	auto prefix_multi = new Theory::StringAutomaton(v6_all_solutions_val->getStringAutomaton()->getDFA(),1,3,8);
	auto temp_dfa = Theory::StringAutomaton::PrependLambda(v7_all_solutions_val->getStringAutomaton()->getDFA(),8);
	auto suffix_multi = new Theory::StringAutomaton(temp_dfa,2,3,9);
	dfaFree(temp_dfa);

	auto intersect_multi = prefix_suffix_auto->Intersect(prefix_multi);
	delete prefix_suffix_auto;
	delete prefix_multi;
	prefix_suffix_auto = intersect_multi;

	intersect_multi = prefix_suffix_auto->Intersect(suffix_multi);
	delete prefix_suffix_auto;
	delete suffix_multi;

	auto v8_multi = new Theory::StringAutomaton(union_auto->getDFA(),0,3,8);
	auto v8_v7_v6_auto = intersect_multi->Intersect(v8_multi);
	delete intersect_multi;
	delete v8_multi;


	auto v8_v7_v6_solutions = v8_v7_v6_auto->GetModelsWithinBound(num_models,-1);
	for(int k = 0; k < v8_v7_v6_solutions["var_8"].size();k++) {
		LOG(INFO) << "v8=" << v8_v7_v6_solutions["var_8"][k];
		LOG(INFO) << "v6=" << v8_v7_v6_solutions["var_6"][k];
		LOG(INFO) << "v7=" << v8_v7_v6_solutions["var_7"][k];
		std::cin.get();
	}


//	temp_multi = MakePrefixSuffix(0,1,2,3);
//	prefix_multi = new StringAutomaton(prefix_dfa,1,3,var);
//	temp_dfa = PrependLambda(suffix_dfa,var);
//	suffix_multi = new StringAutomaton(temp_dfa,2,3,VAR_PER_TRACK);
//	dfaFree(temp_dfa);
//	intersect_multi = temp_multi->Intersect(prefix_multi);
//	delete temp_multi;
//	delete prefix_multi;
//	temp_multi = intersect_multi;
//	intersect_multi = temp_multi->Intersect(suffix_multi);
//	delete temp_multi;
//	delete suffix_multi;

	auto start = std::chrono::steady_clock::now();
	int count = 0;
	for (const auto &variable_entry : getSatisfyingVariables()) {
		if (variable_entry.second == nullptr or variable_values.find(variable_entry.first->getName()) != variable_values.end()) {
			continue;
		}
		count++;
		//LOG(INFO) << "Var name: " << variable_entry.first->getName();
		switch (variable_entry.second->getType()) {

//			case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
//				auto binary_auto = variable_entry.second->getBinaryIntAutomaton();
//				auto formula = binary_auto->GetFormula();
//				model_counter_.add_symbolic_counter(binary_auto->GetSymbolicCounter());
//				//LOG(INFO) << "Binary int with " << formula->GetNumberOfVariables() << " variables";
//				//binary_auto->inspectAuto(false,true);
//				//std::cin.get();
//				auto res = binary_auto->GetModelsWithinBound(num_models,-1);
//				for(auto iter : res) {
////					LOG(INFO) << "Setting " << iter.first;
//					variable_values[iter.first] = iter.second;
//				}
//
//			}
			case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
				auto string_auto = variable_entry.second->getStringAutomaton();
				model_counter_.add_symbolic_counter(string_auto->GetSymbolicCounter());
				//LOG(INFO) << "String int with " << string_auto->GetNumTracks() << " variables";
				auto res = string_auto->GetModelsWithinBound(num_models,-1);
				for(auto iter : res) {
					//LOG(INFO) << "Setting " << iter.first;
					variable_values[iter.first] = iter.second;
				}
				//string_auto->inspectAuto(false,true);
				//std::cin.get();
			}
				break;
//			case Vlab::Solver::Value::Type::INT_AUTOMATON: {
//				auto int_auto = variable_entry.second->getIntAutomaton();
//				model_counter_.add_symbolic_counter(int_auto->GetSymbolicCounter());
//				int_auto->GetModelsWithinBound(num_models,-1);
//			}
//				break;
			default:
				break;
		}
	}
	//LOG(INFO) << "NUM SAT VAR: " << count;

	auto end = std::chrono::steady_clock::now();
	auto t1 = end-start;
	int sat = 0;

	LOG(INFO) << "Getting models took " << std::chrono::duration<long double, std::milli>(t1).count() << " ms";

	start = std::chrono::steady_clock::now();
	symbol_table_->clear_variable_values();
	symbol_table_->push_scope(script_);
	for(auto var : variable_values) {
		Theory::StringAutomaton_ptr union_val = nullptr,temp = nullptr;
		for(auto str_val : var.second) {
			temp = Theory::StringAutomaton::MakeString(str_val);
			if(union_val == nullptr) {
				union_val = temp;
			} else {
				auto res = union_val->Union(temp);
				delete union_val;
				delete temp;
				union_val = res;
			}
		}
		Theory::StringFormula_ptr str_formula = union_val->GetFormula();
		str_formula->AddVariable(var.first,1);
		str_formula->SetType(Theory::StringFormula::Type::VAR);
		symbol_table_->set_value(var.first,new Solver::Value(union_val));
	}
	symbol_table_->pop_scope();
	Solver::ConstraintSolver constraint_solver(script_, symbol_table_, constraint_information_);
	constraint_solver.start();
	if(symbol_table_->isSatisfiable()) {
		LOG(INFO) << "SAT!";
	}
	end = std::chrono::steady_clock::now();


	variable_values.clear();
	for (const auto &variable_entry : getSatisfyingVariables()) {
		if (variable_entry.second == nullptr or variable_values.find(variable_entry.first->getName()) != variable_values.end()) {
			continue;
		}
		count++;
		//LOG(INFO) << "Var name: " << variable_entry.first->getName();
		switch (variable_entry.second->getType()) {

//			case Vlab::Solver::Value::Type::BINARYINT_AUTOMATON: {
//				auto binary_auto = variable_entry.second->getBinaryIntAutomaton();
//				auto formula = binary_auto->GetFormula();
//				model_counter_.add_symbolic_counter(binary_auto->GetSymbolicCounter());
//				//LOG(INFO) << "Binary int with " << formula->GetNumberOfVariables() << " variables";
//				//binary_auto->inspectAuto(false,true);
//				//std::cin.get();
//				auto res = binary_auto->GetModelsWithinBound(num_models,-1);
//				for(auto iter : res) {
////					LOG(INFO) << "Setting " << iter.first;
//					variable_values[iter.first] = iter.second;
//				}
//
//			}
			case Vlab::Solver::Value::Type::STRING_AUTOMATON: {
				auto string_auto = variable_entry.second->getStringAutomaton();
				model_counter_.add_symbolic_counter(string_auto->GetSymbolicCounter());
				//LOG(INFO) << "String int with " << string_auto->GetNumTracks() << " variables";
				auto res = string_auto->GetModelsWithinBound(num_models,-1);
				for(auto iter : res) {
					//LOG(INFO) << "Setting " << iter.first;
					variable_values[iter.first] = iter.second;
				}
				//string_auto->inspectAuto(false,true);
				//std::cin.get();
			}
				break;
//			case Vlab::Solver::Value::Type::INT_AUTOMATON: {
//				auto int_auto = variable_entry.second->getIntAutomaton();
//				model_counter_.add_symbolic_counter(int_auto->GetSymbolicCounter());
//				int_auto->GetModelsWithinBound(num_models,-1);
//			}
//				break;
			default:
				break;
		}
	}


	start = std::chrono::steady_clock::now();
	for(int model_index = 0; model_index < num_models; model_index++) {
		symbol_table_->clear_variable_values();
		symbol_table_->push_scope(script_);

		for(auto var : variable_values) {
			int safety_index = (model_index >= var.second.size()) ? var.second.size()-1 : model_index;
			Theory::StringAutomaton_ptr str_auto = Theory::StringAutomaton::MakeString(var.second[safety_index]);
			Theory::StringFormula_ptr str_formula = str_auto->GetFormula();
			str_formula->AddVariable(var.first,1);
			str_formula->SetType(Theory::StringFormula::Type::VAR);
			symbol_table_->set_value(var.first,new Solver::Value(str_auto));
		}
		symbol_table_->pop_scope();
		Solver::ConstraintSolver constraint_solver(script_, symbol_table_, constraint_information_);
		constraint_solver.start();
		if(symbol_table_->isSatisfiable()) {
			sat++;
		}
		//LOG(INFO) << "sat? " << symbol_table_->isSatisfiable();
		//std::cin.get();
	}
	end = std::chrono::steady_clock::now();
	auto t2 = end-start;

	LOG(INFO) << "Checking models took " << std::chrono::duration<long double, std::milli>(t1).count() << " ms";
	LOG(INFO) << "num sat  : " << sat;
	LOG(INFO) << "num unsat: " << num_models - sat;

}

Theory::BigInteger Driver::CountVariable(const std::string var_name, const unsigned long bound) {
  Theory::BigInteger projected_count, tuple_count;
  tuple_count = GetModelCounterForVariable(var_name,false).Count(bound, bound);
  projected_count = GetModelCounterForVariable(var_name,true).Count(bound, bound);

	return (projected_count < tuple_count) ? projected_count : tuple_count;
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

  script_ = nullptr;
  symbol_table_ = nullptr;
  current_id_ = "";
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

void Driver::loadID(std::string id) {
	if(incremental_states_.find(id) != incremental_states_.end()) {
		LOG(INFO) << "FOUND IT!";
    current_id_ = id;
    symbol_table_ = incremental_states_[current_id_];
	} else {
    LOG(INFO) << "NO FIND!";
		current_id_ = "";
    symbol_table_ = nullptr;
	}

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
  
  script_ = nullptr;

}

std::string Driver::getCurrentID() {
	return current_id_;
}

void Driver::destroyID(std::string id) {
  if(incremental_states_.find(id) != incremental_states_.end()) {
    if(current_id_ == id) {
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
      current_id_ = "";
      symbol_table_ = nullptr;
    }
    delete incremental_states_[id];
    incremental_states_[id] = nullptr;
    incremental_states_.erase(id);
  }
}

void Driver::saveStateAndBranch() {
  static int counter = 0;
  if(current_id_.empty()) {
    return;
  }
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
  std::string next_id = current_id_.append(std::to_string(counter));
  current_id_ = next_id;
  incremental_states_[current_id_] = symbol_table_->clone();
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
