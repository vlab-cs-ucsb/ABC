/*
 * BinaryIntAutomaton.cpp
 *
 *  Created on: Oct 16, 2015
 *      Author: baki
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "BinaryIntAutomaton.h"

namespace Vlab {
namespace Theory {

const int BinaryIntAutomaton::VLOG_LEVEL = 9;

BinaryIntAutomaton::BinaryIntAutomaton(bool is_natural_number)
    : Automaton(Automaton::Type::BINARYINT),
      is_natural_number_ { is_natural_number },
      formula_ { new ArithmeticFormula() } {
}

BinaryIntAutomaton::BinaryIntAutomaton(DFA_ptr dfa, int num_of_variables, bool is_natural_number)
    : Automaton(Automaton::Type::BINARYINT, dfa, num_of_variables),
      is_natural_number_ { is_natural_number },
      formula_ { new ArithmeticFormula() } {
}

BinaryIntAutomaton::BinaryIntAutomaton(DFA_ptr dfa, ArithmeticFormula_ptr formula, bool is_natural_number)
    : Automaton(Automaton::Type::BINARYINT, dfa, formula->GetNumberOfVariables()),
      is_natural_number_ { is_natural_number },
      formula_ { formula } {
}

BinaryIntAutomaton::BinaryIntAutomaton(const BinaryIntAutomaton& other)
    : Automaton(other),
      is_natural_number_(other.is_natural_number_) {
  if (other.formula_) {
    formula_ = other.formula_->clone();
  }
}

BinaryIntAutomaton::~BinaryIntAutomaton() {
  delete formula_;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::clone() const {
  BinaryIntAutomaton_ptr cloned_auto = new BinaryIntAutomaton(*this);
  DVLOG(VLOG_LEVEL) << cloned_auto->id_ << " = [" << this->id_ << "]->clone()";
  return cloned_auto;
}

// What about natural number parameter?
BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeAutomaton(DFA_ptr dfa, Formula_ptr formula, const int number_of_variables) {
	auto bin_auto = new BinaryIntAutomaton(dfa,number_of_variables, not Vlab::Option::Solver::USE_SIGNED_INTEGERS);
	auto arith_formula = dynamic_cast<ArithmeticFormula_ptr>(formula);
	if(arith_formula == nullptr) {
		LOG(FATAL) << "NOT ARITH FORMULA";
	}
	bin_auto->SetFormula(arith_formula);
	return bin_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakePhi(ArithmeticFormula_ptr formula, bool is_natural_number) {
  auto non_accepting_dfa = Automaton::DFAMakePhi(formula->GetNumberOfVariables());
  auto non_accepting_binary_auto = new BinaryIntAutomaton(non_accepting_dfa, formula, is_natural_number);

  DVLOG(VLOG_LEVEL) << non_accepting_binary_auto->id_ << " = MakePhi(" << *formula << ")";
  return non_accepting_binary_auto;
}

/**
 * Binary int automaton does not accept empty string
 */
BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeAnyInt(ArithmeticFormula_ptr formula, bool is_natural_number) {
  auto any_binary_int_dfa = Automaton::DFAMakeAnyButNotEmpty(formula->GetNumberOfVariables());
  auto any_int = new BinaryIntAutomaton(any_binary_int_dfa, formula, is_natural_number);

  DVLOG(VLOG_LEVEL) << any_int->id_ << " = MakeAnyInt(" << *formula << ")";
  return any_int;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeAutomaton(ArithmeticFormula_ptr formula, bool is_natural_number) {
  BinaryIntAutomaton_ptr result_auto = nullptr;

  switch (formula->GetType()) {
    case ArithmeticFormula::Type::EQ: {
      result_auto = BinaryIntAutomaton::MakeEquality(formula, is_natural_number);
      break;
    }
    case ArithmeticFormula::Type::NOTEQ: {
      result_auto = BinaryIntAutomaton::MakeEquality(formula, is_natural_number);
      break;
    }
    case ArithmeticFormula::Type::GT: {
      result_auto = BinaryIntAutomaton::MakeGreaterThan(formula, is_natural_number);
      break;
    }
    case ArithmeticFormula::Type::GE: {
      result_auto = BinaryIntAutomaton::MakeGreaterThanOrEqual(formula, is_natural_number);
      break;
    }
    case ArithmeticFormula::Type::LT: {
      result_auto = BinaryIntAutomaton::MakeLessThan(formula, is_natural_number);
      break;
    }
    case ArithmeticFormula::Type::LE: {
      result_auto = BinaryIntAutomaton::MakeLessThanOrEqual(formula, is_natural_number);
      break;
    }
    case ArithmeticFormula::Type::BOOL: {
    	result_auto = BinaryIntAutomaton::MakeBoolean(formula);
    	break;
    }
    case ArithmeticFormula::Type::VAR: {
      CHECK_EQ(1, formula->GetNumberOfVariables());
      result_auto = BinaryIntAutomaton::MakeAnyInt(formula, is_natural_number);
      break;
    }
    default:
      LOG(FATAL)<< "Equation type is not specified, please set type for input formula: " << *formula;
      break;
    }

  return result_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeAutomaton(int value, std::string var_name, ArithmeticFormula_ptr formula,
                                                         bool add_leading_zeros) {

  auto constant_value_formula = formula;
  constant_value_formula->ResetCoefficients();
  constant_value_formula->SetVariableCoefficient(var_name, 1);
  constant_value_formula->SetConstant(-value);
  constant_value_formula->SetType(ArithmeticFormula::Type::EQ);
  auto binary_auto = BinaryIntAutomaton::MakeAutomaton(constant_value_formula, not add_leading_zeros);

  DVLOG(VLOG_LEVEL) << binary_auto->getId() << " = BinaryIntAutomaton::MakeAutomaton(" << value << ", " << var_name
                    << ", " << *formula << ", " << std::boolalpha << add_leading_zeros << ")";
  return binary_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeAutomaton(SemilinearSet_ptr semilinear_set, std::string var_name,
                                                         ArithmeticFormula_ptr formula, bool add_leading_zeros) {
  DVLOG(VLOG_LEVEL) << "BinaryIntAutomaton::MakeAutomaton("<< *semilinear_set << ", " << var_name;

  int var_index = formula->GetVariableIndex(var_name);
  int number_of_variables = formula->GetNumberOfVariables(), lz_index = 0;
  if (add_leading_zeros) {
    ++number_of_variables;
    lz_index = number_of_variables - 1;
  }

  std::string bit_transition(number_of_variables + 1, 'X');
  bit_transition[number_of_variables] = '\0';

  std::vector<BinaryState_ptr> binary_states;
  BinaryIntAutomaton::ComputeBinaryStates(binary_states, semilinear_set);

  int number_of_binary_states = binary_states.size();
  int number_of_states = number_of_binary_states + 1;
  int leading_zero_state = 0;  // only used if we add leading zeros
  if (add_leading_zeros) {
    ++number_of_states;
    leading_zero_state = number_of_states - 2;
  }

  int sink_state = number_of_states - 1;
  int* indices = GetBddVariableIndices(number_of_variables);
  std::string statuses(number_of_states + 1, '-');
  statuses[number_of_states] = '\0';
  dfaSetup(number_of_states, number_of_variables, indices);
  bool is_final_state = false;
  for (int i = 0; i < number_of_binary_states; i++) {
    is_final_state = is_accepting_binary_state(binary_states[i], semilinear_set);

    if (add_leading_zeros and is_final_state) {
      if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() >= 0) {
        dfaAllocExceptions(3);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '0';
        dfaStoreException(binary_states[i]->getd0(), &bit_transition[0]);
        bit_transition[var_index] = '1';
        bit_transition[lz_index] = 'X';
        dfaStoreException(binary_states[i]->getd1(), &bit_transition[0]);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, &bit_transition[0]);
      } else if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() < 0) {
        dfaAllocExceptions(2);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '0';
        dfaStoreException(binary_states[i]->getd0(), &bit_transition[0]);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, &bit_transition[0]);
      } else if (binary_states[i]->getd0() < 0 && binary_states[i]->getd1() >= 0) {
        dfaAllocExceptions(2);
        bit_transition[var_index] = '1';
        bit_transition[lz_index] = 'X';
        dfaStoreException(binary_states[i]->getd1(), &bit_transition[0]);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, &bit_transition[0]);
      } else {
        dfaAllocExceptions(1);
        bit_transition[var_index] = '0';
        bit_transition[lz_index] = '1';
        dfaStoreException(leading_zero_state, &bit_transition[0]);
      }
      bit_transition[lz_index] = 'X';
    } else {
      if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() >= 0) {
        dfaAllocExceptions(2);
        bit_transition[var_index] = '0';
        dfaStoreException(binary_states[i]->getd0(), &bit_transition[0]);
        bit_transition[var_index] = '1';
        dfaStoreException(binary_states[i]->getd1(), &bit_transition[0]);
      } else if (binary_states[i]->getd0() >= 0 && binary_states[i]->getd1() < 0) {
        dfaAllocExceptions(1);
        bit_transition[var_index] = '0';
        dfaStoreException(binary_states[i]->getd0(), &bit_transition[0]);
      } else if (binary_states[i]->getd0() < 0 && binary_states[i]->getd1() >= 0) {
        dfaAllocExceptions(1);
        bit_transition[var_index] = '1';
        dfaStoreException(binary_states[i]->getd1(), &bit_transition[0]);
      } else {
        dfaAllocExceptions(0);
      }
    }

    dfaStoreState(sink_state);

    if (is_final_state and (not add_leading_zeros)) {
      statuses[i] = '+';
    }
  }

  // for the leading zero state
  if (add_leading_zeros) {
    dfaAllocExceptions(1);
    bit_transition[var_index] = '0';
    bit_transition[lz_index] = '1';
    dfaStoreException(leading_zero_state, &bit_transition[0]);
    dfaStoreState(sink_state);
    statuses[leading_zero_state] = '+';
  }

  // for the sink state
  dfaAllocExceptions(0);
  dfaStoreState(sink_state);

  int zero_state = binary_states[0]->getd0();  // adding leading zeros makes accepting zero 00, fix here
  if (zero_state > -1 and is_accepting_binary_state(binary_states[zero_state], semilinear_set)) {
    // TODO temporary removal
    //    statuses[zero_state] = '+';
  }

  auto binary_dfa = dfaBuild(&statuses[0]);
  // cleanup
  for (auto bin_state : binary_states) {
    delete bin_state;
  }
  binary_states.clear();
  //delete[] indices;
  if (add_leading_zeros) {
    auto tmp_dfa = binary_dfa;
    binary_dfa = dfaProject(binary_dfa, (unsigned) (lz_index));
    dfaFree(tmp_dfa);
    tmp_dfa = nullptr;
    number_of_variables = number_of_variables - 1;
  }

  auto binary_auto = new BinaryIntAutomaton(dfaMinimize(binary_dfa), formula, not add_leading_zeros);
  dfaFree(binary_dfa);
  binary_dfa = nullptr;

  // binary state computation for semilinear sets may have leading zeros, remove them
  if ((not add_leading_zeros) and (not semilinear_set->has_only_constants())) {
    auto trim_helper_auto = BinaryIntAutomaton::MakeTrimHelperAuto(var_index, number_of_variables);
    trim_helper_auto->SetFormula(formula->clone());
    auto tmp_auto = binary_auto;
    binary_auto = binary_auto->Intersect(trim_helper_auto);
    delete trim_helper_auto;
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << binary_auto->getId() << " = BinaryIntAutomaton::MakeAutomaton(<semilinear_set>, " << var_name
                    << ", " << *(binary_auto->formula_) << ", " << std::boolalpha << add_leading_zeros << ")";
  return binary_auto;
}

ArithmeticFormula_ptr BinaryIntAutomaton::GetFormula() {
  return formula_;
}

void BinaryIntAutomaton::SetFormula(ArithmeticFormula_ptr formula) {
	if(formula_ != nullptr) {
		delete formula_;
	}
  this->formula_ = formula;
}

bool BinaryIntAutomaton::is_natural_number() {
  return is_natural_number_;
}

bool BinaryIntAutomaton::HasNegative1() {
  CHECK_EQ(1, num_of_bdd_variables_)<< "implemented for single track binary automaton";

  if (is_natural_number_) {
    return false;
  }

  std::vector<char> exception = {'1'};
  std::map<int, bool> is_visited;
  int current_state = this->dfa_->s;
  while (not is_visited[current_state]) {
    is_visited[current_state] = true;
    current_state = getNextState(current_state, exception);
    if (current_state > -1 and IsAcceptingState(current_state)) {
      return true;
    }
  }

  return false;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::Complement() {
  DFA_ptr complement_dfa = dfaCopy(this->dfa_);

  dfaNegation(complement_dfa);

  auto tmp_auto = new BinaryIntAutomaton(complement_dfa, this->formula_->clone(), is_natural_number_);
  // a complemented auto may have initial state accepting, we should be safely avoided from that
  auto any_int_auto = BinaryIntAutomaton::MakeAnyInt(this->formula_->clone(), is_natural_number_);
  auto complement_auto = any_int_auto->Intersect(tmp_auto);
  delete any_int_auto;
  delete tmp_auto;
  complement_auto->SetFormula(this->formula_->negate());

  DVLOG(VLOG_LEVEL) << complement_auto->id_ << " = [" << this->id_ << "]->Complement()";
  return complement_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::Intersect(BinaryIntAutomaton_ptr other_auto) {



  BinaryIntAutomaton_ptr left_auto = nullptr, right_auto = nullptr;
  ArithmeticFormula_ptr intersect_formula = nullptr;

/*
  for(auto it : this->formula_->GetVariableCoefficientMap()) {
    LOG(INFO) << it.first << "," << it.second;
  }
  LOG(INFO) << "--";
  for(auto it : other_auto->GetFormula()->GetVariableCoefficientMap()) {
    LOG(INFO) << it.first << "," << it.second;
  }
  if(this->is_natural_number_ != other_auto->is_natural_number_) {
    LOG(FATAL) << "Numbers don't match";
  }
*/
  auto left_num_tracks = this->GetFormula()->GetNumberOfVariables();
  auto right_num_tracks = other_auto->GetFormula()->GetNumberOfVariables();
  if(left_num_tracks > right_num_tracks) {
    left_auto = this;
    right_auto = other_auto->ChangeIndicesMap(this->formula_->clone());
    intersect_formula = this->formula_->clone();
  } else if(left_num_tracks < right_num_tracks) {
    left_auto = other_auto;
    right_auto = this->ChangeIndicesMap(other_auto->formula_->clone());
    intersect_formula = other_auto->formula_->clone();
  } else {
    left_auto = this;
    right_auto = other_auto;
    intersect_formula = this->formula_->Intersect(other_auto->formula_);
  }

/*
  std::string id1, id2;

  std::stringstream os1;
  //{
  //  cereal::BinaryOutputArchive ar(os1);
  //  Util::Serialize::save(ar,left_auto->dfa_);
  //}
  left_auto->toBDD(os1);
  id1 = os1.str();



  std::stringstream os2;
  //{
  //  cereal::BinaryOutputArchive ar(os2);
  //  Util::Serialize::save(ar,right_auto->dfa_);
  //}
  right_auto->toBDD(os2);
  id2 = os2.str();
//  right_auto->inspectAuto(false,true);
//  right_auto->inspectBDD();
//  LOG(INFO) << id2;
//  std::cin.get();
  //std::pair<std::string,std::string> stupid_key1(id1,id2);
  //std::pair<std::string,std::string> stupid_key2(id2,id1);
  std::string stupid_key1 = id1 + id2;
  std::string stupid_key2 = id2 + id1;
  DFA_ptr intersect_dfa = nullptr;


 //   LOG(FATAL) << "HERE";

  auto &c = rdx_->commandSync<std::string>({"GET", stupid_key1});

  bool has_result = false;
  std::string cached_data;
  if (c.ok()) {
    has_result = true;
    cached_data = c.reply();
  }
  c.free();
  if (has_result) {
    std::stringstream is(cached_data);
    {
      cereal::BinaryInputArchive ar(is);
      Util::Serialize::load(ar, intersect_dfa);
    }
    num_hits++;
  } else {
    intersect_dfa = Automaton::DFAIntersect(left_auto->dfa_, right_auto->dfa_);
    std::stringstream os;
    {
      cereal::BinaryOutputArchive ar(os);
      Util::Serialize::save(ar, intersect_dfa);
    }
    rdx_->command<std::string>({"SET", stupid_key1, os.str()});
    num_misses++;
  }
*/

  auto intersect_dfa = Automaton::DFAIntersect(left_auto->dfa_, right_auto->dfa_);


  intersect_formula->ResetCoefficients();
  intersect_formula->SetType(ArithmeticFormula::Type::INTERSECT);
  auto intersect_auto = new BinaryIntAutomaton(intersect_dfa, intersect_formula, is_natural_number_);

  // LOG(INFO) << "------BEFORE----:";
  // for(auto it : left_auto->GetFormula()->GetVariableCoefficientMap()) {
  //   LOG(INFO) << it.first << left_auto->GetFormula()->GetVariableIndex(it.first);
  // }
  // LOG(INFO) << "";
  // for(auto it : right_auto->GetFormula()->GetVariableCoefficientMap()) {
  //   LOG(INFO) << it.first << right_auto->GetFormula()->GetVariableIndex(it.first);
  // }
  // LOG(INFO) << "-------AFTER-----:";
  // for(auto it : intersect_auto->GetFormula()->GetVariableCoefficientMap()) {
  //   LOG(INFO) << it.first << intersect_auto->GetFormula()->GetVariableIndex(it.first);
  // }
  // std::cin.get();


  // intersect_auto->inspectAuto(false,true);
  // std::cin.get();


//  left_auto->inspectAuto(false,true);
//  right_auto->inspectAuto(false,true);
//  intersect_auto->inspectAuto(false,true);
//  std::cin.get();



  DVLOG(VLOG_LEVEL) << intersect_auto->id_ << " = [" << this->id_ << "]->Intersect(" << right_auto->id_ << ")";
  return intersect_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::Union(BinaryIntAutomaton_ptr other_auto) {
  auto union_dfa = Automaton::DFAUnion(this->dfa_, other_auto->dfa_);
  ArithmeticFormula_ptr union_formula = nullptr;
	if(formula_ != nullptr && other_auto->formula_ != nullptr) {
		union_formula = formula_->Union(other_auto->formula_);
	} else if(formula_ != nullptr) {
		union_formula = formula_->clone();
	} else {
		union_formula = nullptr;
	}
  union_formula->ResetCoefficients();
  union_formula->SetType(ArithmeticFormula::Type::UNION);
  auto union_auto = new BinaryIntAutomaton(union_dfa, union_formula, is_natural_number_);

  DVLOG(VLOG_LEVEL) << union_auto->id_ << " = [" << this->id_ << "]->Union(" << other_auto->id_ << ")";
  return union_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::Difference(BinaryIntAutomaton_ptr other_auto) {
  auto complement_auto = other_auto->Complement();
  auto difference_auto = this->Intersect(complement_auto);
  delete complement_auto;

  DVLOG(VLOG_LEVEL) << difference_auto->id_ << " = [" << this->id_ << "]->Difference(" << other_auto->id_ << ")";
  return difference_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::Exists(std::string var_name) {
  LOG(FATAL)<< "implement me";
  return nullptr;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::GetBinaryAutomatonFor(std::string var_name) {
  CHECK_EQ(num_of_bdd_variables_, formula_->GetNumberOfVariables())<< "number of variables is not consistent with formula";
  int bdd_var_index = formula_->GetVariableIndex(var_name);;
  auto single_var_dfa = Automaton::DFAProjectTo(this->dfa_, num_of_bdd_variables_, bdd_var_index);
  auto single_var_formula = new ArithmeticFormula();
  single_var_formula->SetType(ArithmeticFormula::Type::INTERSECT);
  single_var_formula->AddVariable(var_name, 1);
  auto single_var_auto = new BinaryIntAutomaton(single_var_dfa, single_var_formula, is_natural_number_);

  DVLOG(VLOG_LEVEL) << single_var_auto->id_ << " = [" << this->id_ << "]->GetBinaryAutomatonOf(" << var_name << ")";
  return single_var_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::ChangeIndicesMap(ArithmeticFormula_ptr new_formula, bool clone) {
  BinaryIntAutomaton_ptr unmapped_auto = nullptr;
//  auto start = std::chrono::steady_clock::now();

	auto old_coeff_map = this->formula_->GetVariableCoefficientMap();
	auto new_coeff_map = new_formula->GetVariableCoefficientMap();
	int old_num_tracks = this->formula_->GetNumberOfVariables();
	int new_num_tracks = new_formula->GetNumberOfVariables();

	// if previously only one track, we need to add lambda (9th bdd variable)
	// just make new auto and return that
	if(old_num_tracks == 1) {
    if(new_num_tracks == 1) {
      auto ret_auto = this->clone();
      ret_auto->SetFormula(new_formula);

      return ret_auto;
    }
    // should ALWAYS have formula, but add check just to make sure
	  if(this->formula_ == nullptr || this->formula_->GetNumberOfVariables() == 0) {
	    LOG(FATAL) << "Can't remap indices! Automaton has no formula or formula has no variables!";
	  }
//	  std::string var_name = this->formula_->GetVariableAtIndex(0);
	  unmapped_auto = new BinaryIntAutomaton(this->dfa_,1,this->is_natural_number_);
	  unmapped_auto->SetFormula(this->formula_->clone());
//	  unmapped_auto->SetFormula(new_formula);
//	  return unmapped_auto;
	} else if(clone) {
	  unmapped_auto = this->clone();
	} else {
	  unmapped_auto = this;
	}

	// though we're remapping indices, we're not adding any new variables right now
	// (this will be done during intersection
	int* map = CreateBddVariableIndices(old_num_tracks);

//	LOG(INFO) << "Old map:";
//	for(auto iter : old_coeff_map) {
//	  LOG(INFO) << "  " << iter.first;
//	}
//
//	LOG(INFO) << "New map:";
//	for(auto iter : new_coeff_map) {
//	  LOG(INFO) << "  " << iter.first;
//	}

  bool replace = false;

	for(auto iter : old_coeff_map) {

		int old_index = unmapped_auto->formula_->GetVariableIndex(iter.first);
		int new_index = new_formula->GetVariableIndex(iter.first);

    if(old_index != new_index) replace = true;

//		for(int i = 0; i < VAR_PER_TRACK; i++) {
			map[old_index] = new_index;
//		}
	}

//   for(int i = 0; i < old_num_tracks; i++) {
//     LOG(INFO) << "map[" << i << "] = " << map[i];
//   }

//	auto remapped_dfa = unmapped_auto->dfa_;//dfaCopy(unmapped_auto->dfa_);
	if(replace) dfaReplaceIndices(unmapped_auto->dfa_,map);
//	std::cin.get();
	delete[] map;
//	auto remapped_auto = new BinaryIntAutomaton(remapped_dfa,unmapped_auto->num_of_bdd_variables_,is_natural_number_);
//	remapped_auto->SetFormula(new_formula);
//	delete unmapped_auto;

  unmapped_auto->SetFormula(new_formula);

//  auto end = std::chrono::steady_clock::now();
//  diff += end-start;
	return unmapped_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::GetPositiveValuesFor(std::string var_name) {
  std::vector<int> indexes;
  int var_index = formula_->GetVariableIndex(var_name);
  indexes.push_back(var_index);

  auto greater_than_or_equalt_to_zero_auto = BinaryIntAutomaton::MakeIntGraterThanOrEqualToZero(
      indexes, formula_->GetNumberOfVariables());
  greater_than_or_equalt_to_zero_auto->SetFormula(formula_->clone());
  auto positives_auto = this->Intersect(greater_than_or_equalt_to_zero_auto);
  delete greater_than_or_equalt_to_zero_auto;

  DVLOG(VLOG_LEVEL) << positives_auto->id_ << " = [" << this->id_ << "]->GetPositiveValuesFor(" << var_name << ")";
  return positives_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::GetNegativeValuesFor(std::string var_name) {
  BinaryIntAutomaton_ptr negatives_auto = nullptr;

  LOG(FATAL)<< "implement me";

  DVLOG(VLOG_LEVEL) << negatives_auto->id_ << " = [" << this->id_ << "]->GetNegativeValuesFor(" << var_name << ")";
  return negatives_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::TrimLeadingZeros() {
  CHECK_EQ(1, num_of_bdd_variables_)<< "trimming is implemented for single track positive binary automaton";

  auto tmp_auto = this->clone();

  // identify leading zeros
  std::vector<char> exception = {'0'};
  int next_state = -1;
  int sink_state = tmp_auto->GetSinkState();
  std::map<int, std::vector<int>> possible_final_states;
  std::stack<int> final_states;
  for (int i = 0; i < tmp_auto->dfa_->ns; i++) {
    next_state = getNextState(i, exception);
    if ((sink_state not_eq next_state) and (i not_eq next_state)) {
      possible_final_states[next_state].push_back(i);
    }
    if (IsAcceptingState(i)) {
      final_states.push(i);
    }
  }

  while (not final_states.empty()) {
    next_state = final_states.top(); final_states.pop();
    for (auto s : possible_final_states[next_state]) {
      if (not tmp_auto->IsAcceptingState(s)) {
        tmp_auto->dfa_->f[s] = 1;
        final_states.push(s);
      }
    }
  }

  tmp_auto->Minimize();

  auto trim_helper_auto = BinaryIntAutomaton::MakeTrimHelperAuto(0,num_of_bdd_variables_);
  trim_helper_auto->SetFormula(tmp_auto->formula_->clone());
  auto trimmed_auto = tmp_auto->Intersect(trim_helper_auto);
  delete tmp_auto;
  delete trim_helper_auto;

  DVLOG(VLOG_LEVEL) << trimmed_auto->id_ << " = [" << this->id_ << "]->TrimLeadingZeros()";
  return trimmed_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::AddLeadingZeros() {
  LOG(FATAL)<< "implement me (similar to string->toUnary function)";
  BinaryIntAutomaton_ptr leading_zero_auto = nullptr;
  DFA_ptr leading_zero_dfa = nullptr, tmp_dfa = nullptr;

  int number_of_variables = num_of_bdd_variables_ + 1,
  leading_zero_state = number_of_variables - 1,
  to_state = 0;
  int* indices = GetBddVariableIndices(number_of_variables);

  std::vector<char> leading_zero_exception;
  std::map<std::vector<char>*, int> exceptions;
  std::vector<char>* current_exception = nullptr;

  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;

  for (int i = 0; i < number_of_variables; i++) {
    leading_zero_exception.push_back('0');
  }

  DVLOG(VLOG_LEVEL) << leading_zero_auto->id_ << " = [" << this->id_ << "]->TrimLeadingZeros()";
  return leading_zero_auto;
}

/*
 *  TODO options to fix problems, works for automaton that has 1 variable
 *  Search to improve period search part to make it sound
 *
 */
SemilinearSet_ptr BinaryIntAutomaton::GetSemilinearSet() {
  SemilinearSet_ptr semilinear_set = nullptr, current_set = nullptr, tmp_set = nullptr;
  BinaryIntAutomaton_ptr subject_auto = nullptr, tmp_1_auto = nullptr, tmp_2_auto = nullptr, diff_auto = nullptr;
  std::vector<SemilinearSet_ptr> semilinears;
  std::string var_name = this->formula_->GetVariableCoefficientMap().begin()->first;
  int current_state = this->dfa_->s, sink_state = this->GetSinkState();
  std::vector<int> constants, bases;
  bool is_cyclic = false;
  std::map<int, bool> cycle_status;

  semilinear_set = new SemilinearSet();

  // 1- First get the constants that are reachable by only taking an edge of a SCC that has one state inside

  is_cyclic = GetCycleStatus(cycle_status);
  GetConstants(cycle_status, constants);
  Util::List::sort_and_remove_duplicate(constants);
  cycle_status.clear();
  semilinear_set->set_constants(constants);

  // CASE automaton has only constants
  if (not is_cyclic) {
    DVLOG(VLOG_LEVEL) << *semilinear_set;
    DVLOG(VLOG_LEVEL) << "<semilinear set> = [" << this->id_ << "]->GetSemilinearSet()";
    return semilinear_set;
  }

  /*
   * - Get the maximum constant and make an automaton Ac that accepts 0 <= x <= max
   * - Make new constants equal to the numbers that are accepted by original automaton (A)
   * intersection with Ac
   * Delete these numbers from original automaton
   */
  if (semilinear_set->has_constants()) {

    int max_constant = constants.back();  // it is already sorted
    constants.clear();
    for (int i = 0; i <= max_constant; i++) {
      constants.push_back(i);
    }
    semilinear_set->set_constants(constants);
    constants.clear();
    tmp_1_auto = BinaryIntAutomaton::MakeAutomaton(semilinear_set, var_name, formula_->clone(), false);
    semilinear_set->clear();

    tmp_2_auto = this->Intersect(tmp_1_auto);
    delete tmp_1_auto;
    tmp_1_auto = nullptr;

    tmp_2_auto->GetBaseConstants(constants);  // if automaton is acyclic, it will return all constants
    Util::List::sort_and_remove_duplicate(constants);
    semilinear_set->set_constants(constants);
    constants.clear();

    subject_auto = this->Difference(tmp_2_auto);
    delete tmp_2_auto;
    tmp_2_auto = nullptr;
  } else {
    subject_auto = this->clone();
  }

  semilinears.push_back(semilinear_set);

  unsigned i = 0;
  int cycle_head = 0;
  std::vector<int> tmp_periods;
  int bound = 0;
  while (not subject_auto->IsEmptyLanguage() and (bound++ < 5)) {
    i = 0;
    cycle_head = 0;
    tmp_periods.clear();
    semilinear_set = new SemilinearSet();
    subject_auto->GetBaseConstants(bases);
    Util::List::sort_and_remove_duplicate(bases);

    // usually we do not need to much numbers once they are sorted, note that this is not sound
    // to make it sound iteratively check for periods instead of deleting them
    if (bases.size() > 10) {
      bases.erase(bases.begin() + 10, bases.end());
    }

    if (bases.size() == 1) {
      semilinear_set->set_period(bases[0]);
      semilinear_set->add_periodic_constant(0);
      semilinears.push_back(semilinear_set->clone());
      // no need to verify period
    } else if (bases.size() > 1) {
      int possible_period = 0;

      for (auto it = bases.begin(); it < bases.end() - 1; it++) {

        cycle_head = *it;
        bool period_found = false;
        for (auto jt = it + 1; jt < bases.end(); jt++) {
          possible_period = *jt - cycle_head;

          bool add_me = true;
          for (auto p : tmp_periods) {
            if ((possible_period % p) == 0) {
              add_me = false;
              break;
            }
          }
          if (add_me) {
            current_set = new SemilinearSet();
            current_set->set_cycle_head(cycle_head);
            current_set->set_period(possible_period);
            current_set->add_periodic_constant(0);

            tmp_1_auto = BinaryIntAutomaton::MakeAutomaton(current_set, var_name, formula_->clone(), false);
            tmp_2_auto = subject_auto->Intersect(tmp_1_auto);
            diff_auto = tmp_1_auto->Difference(tmp_2_auto);
            delete tmp_1_auto;
            tmp_1_auto = nullptr;
            delete tmp_2_auto;
            tmp_2_auto = nullptr;
            if (diff_auto->IsEmptyLanguage()) {
              tmp_set = semilinear_set;
              semilinear_set = tmp_set->Merge(current_set);
              delete tmp_set;
              tmp_set = nullptr;
              semilinears.push_back(current_set);
              tmp_periods.push_back(possible_period);
              period_found = true;
              delete diff_auto;
              diff_auto = nullptr;
              break;
            } else {
              delete current_set;
            }
            delete diff_auto;
            diff_auto = nullptr;
            current_set = nullptr;
          }
        }

        if (period_found) {
          for (auto rt = it + 1; rt < bases.end();) {
            possible_period = *rt - cycle_head;
            bool remove_me = false;
            for (auto p : tmp_periods) {
              if ((possible_period % p) == 0) {
                remove_me = true;
                break;
              }
            }
            if (remove_me) {
              rt = bases.erase(rt);
            } else {
              rt++;
            }
          }
          period_found = false;
        }
      }
    } else {
      LOG(FATAL)<< "Automaton must have an accepting state, check base extraction algorithm";
    }
    tmp_1_auto = BinaryIntAutomaton::MakeAutomaton(semilinear_set, var_name, formula_->clone(), false);
    tmp_2_auto = subject_auto;
    subject_auto = tmp_2_auto->Difference(tmp_1_auto);
    delete tmp_1_auto;
    tmp_1_auto = nullptr;
    delete tmp_2_auto;
    tmp_2_auto = nullptr;
    delete semilinear_set;
    semilinear_set = nullptr;
    bases.clear();
  }

  delete subject_auto;
  subject_auto = nullptr;

  semilinear_set = new SemilinearSet();
  for (auto s : semilinears) {
    tmp_set = semilinear_set;
    semilinear_set = tmp_set->Merge(s);
    delete tmp_set;
    delete s;
  }

  DVLOG(VLOG_LEVEL) << *semilinear_set;
  DVLOG(VLOG_LEVEL) << "semilinear set = [" << this->id_ << "]->GetSemilinearSet()";

  return semilinear_set;
}

UnaryAutomaton_ptr BinaryIntAutomaton::ToUnaryAutomaton() {
  UnaryAutomaton_ptr unary_auto = nullptr;
  BinaryIntAutomaton_ptr trimmed_auto = nullptr;
  SemilinearSet_ptr semilinear_set = nullptr;
  trimmed_auto = this->TrimLeadingZeros();

  semilinear_set = trimmed_auto->GetSemilinearSet();
  delete trimmed_auto;
  trimmed_auto = nullptr;

  unary_auto = UnaryAutomaton::MakeAutomaton(semilinear_set);
  delete semilinear_set;
  semilinear_set = nullptr;
  DVLOG(VLOG_LEVEL) << unary_auto->getId() << " = [" << this->id_ << "]->ToUnaryAutomaton()";
  return unary_auto;
}

std::map<std::string, int> BinaryIntAutomaton::GetAnAcceptingIntForEachVar() {
  std::map<std::string, int> var_values;
  std::map<int, int> values;
  std::vector<bool>* example = getAnAcceptingWord();

  // Reads from most significant bits

  auto rit = example->rbegin();
  if (not is_natural_number_) {
    // read the sign bit for integers
    for (int var_index = num_of_bdd_variables_ - 1; var_index >= 0; --var_index) {
      if (*rit) {
        values[var_index] = -1;
      } else {
        values[var_index] = 0;
      }
      rit++;
    }
  }

  // read value bits
  for (int var_index = num_of_bdd_variables_ - 1; rit != example->rend(); rit++) {
    values[var_index] <<= 1;
    values[var_index] |= (*rit);
    var_index--;

    if (var_index == -1) {
      var_index = num_of_bdd_variables_ - 1;
    }
  }

  delete example;
  example = nullptr;

  int var_index;
  std::string var_name;
  for (auto& var_entry : formula_->GetVariableCoefficientMap()) {
    var_name = var_entry.first;
    var_index = formula_->GetVariableIndex(var_name);;
    if (var_name.length() > 10) {
      var_name = var_name.substr(0, 10);
    }
    var_values[var_name] = values[var_index];
  }

  return var_values;
}

void BinaryIntAutomaton::decide_counting_schema(Eigen::SparseMatrix<BigInteger>& count_matrix) {
  if (is_natural_number_) {
    counter_.set_type(SymbolicCounter::Type::BINARYUNSIGNEDINT);
  } else {
    counter_.set_type(SymbolicCounter::Type::BINARYINT);
  }
}

BigInteger BinaryIntAutomaton::SymbolicCount(double bound, bool count_less_than_or_equal_to_bound) {
  std::stringstream cmd;
  std::string str_result;
  std::string tmp_result_file = Option::Theory::TMP_PATH + "/arith_result.dot";
  std::string math_script_path = Option::Theory::SCRIPT_PATH + "/count.m";

  std::ofstream outfile(tmp_result_file.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << tmp_result_file << std::endl;
    exit(2);
  }

  this->ToDot(outfile, false);

  cmd << "math -script " << math_script_path << " " << tmp_result_file << " ";

  if (not is_natural_number_) {
    ++bound;  // consider sign bit
  }

  if (std::floor(bound) == bound) {
    cmd << static_cast<int>(bound);
  } else {
    cmd << bound;
  }

  try {
    DVLOG(VLOG_LEVEL) << "run_cmd(`" << cmd.str() << "`)";
    str_result = Util::Cmd::run_cmd(cmd.str());
  } catch (std::string& e) {
    LOG(ERROR)<< e;
  }

  return BigInteger(str_result);
}

std::map<std::string,std::vector<std::string>> BinaryIntAutomaton::GetModelsWithinBound(int num_models, int bound) {
	//inspectAuto(false,true);
	//std::cin.get();
	int num_tracks;
	if(formula_ == nullptr) {
		num_tracks = this->num_of_bdd_variables_;
	} else {
		num_tracks = formula_->GetNumberOfVariables();
	}

	if(bound == -1 and num_models == -1) {
		LOG(FATAL) << "both bound and num_models cant be -1";
	} else if(bound == -1) {
		auto counter = GetSymbolicCounter();
		bound = counter.GetMinBound(num_models);
	}

//	LOG(INFO) << "num_models : " << num_models;
//	LOG(INFO) << "bound      : " << bound;

  // compute BFS for unweighted graph (dfa)
  std::queue<int> states_to_process;
  std::vector<int> distances(this->dfa_->ns,INT_MAX);
  std::set<int> final_states;

  std::vector<int> shortest_accepting_path(this->dfa_->ns,INT_MAX);
  for(int start_state = 0; start_state < this->dfa_->ns; start_state++) {
  	distances[start_state] = 0;
		states_to_process.push(start_state);

		while(not states_to_process.empty()) {
			int s = states_to_process.front();
			states_to_process.pop();
			// mark final states for later
			if(this->dfa_->f[s] == 1) {
				final_states.insert(s);
			}

			for(auto iter : getNextStates(s)) {
				if(distances[iter] == INT_MAX) {
					states_to_process.push(iter);
					distances[iter] = distances[s] + 1;
				}
			}
		}

		int shortest = INT_MAX;
		for(auto final : final_states) {
			if(distances[final] < shortest) {
				shortest = distances[final];
			}
		}
		shortest_accepting_path[start_state] = shortest;


		distances = std::vector<int>(this->dfa_->ns,INT_MAX);
  }

//  for(int i = 0; i < this->dfa_->ns; i++) {
//  	LOG(INFO) << "shortest path for state " << i << " = " << shortest_accepting_path[i];
//  }
//
//  LOG(INFO) << "Done computing shortest paths to final state";

  // assume num_tracks > 1; Otherwise, juse call normal version
  int models_so_far = 0;
  int num_variables = this->num_of_bdd_variables_;
  int var_per_track = num_variables / num_tracks;

  std::vector<std::pair<int,std::vector<char>>> next_states;

  // cache the process for finding next transitions from a state
  std::vector<std::vector<std::pair<int,std::vector<char>>>> next_states_matrix(this->dfa_->ns);
  for(int i = 0; i < this->dfa_->ns; i++) {
  	int current_state = i;
  	std::vector<std::pair<int,std::vector<char>>> inner_next_states;
		std::vector<unsigned> nodes;
		std::vector<std::vector<char>> transition_stack;
		std::vector<char> current_transition;
		int sink = GetSinkState();

		unsigned p, l, r, index; // BDD traversal variables
		p = this->dfa_->q[current_state];
		nodes.push_back(p);
		transition_stack.push_back(std::vector<char>());
		while (not nodes.empty()) {
			p = nodes.back();
			nodes.pop_back();
			current_transition = transition_stack.back();
			transition_stack.pop_back();
			LOAD_lri(&this->dfa_->bddm->node_table[p], l, r, index);
			if (index == BDD_LEAF_INDEX) {
				int to_state = l;
				// if to_state is sink state, ignore
				if(to_state == sink) {
					continue;
				}

				while (current_transition.size() < (unsigned) num_of_bdd_variables_) {
					current_transition.push_back('X');
				}

				// if transition is to a final state, unroll the 'X'
				// must do this now because of leading zeros or ones causes issues later
				// TODO: Will, think of better way to handle this
				if(this->dfa_->f[to_state] == 1) {
					std::vector<std::vector<char>> models;
					models.push_back(std::vector<char>());
					for(int k = 0; k < current_transition.size(); k++) {
						if(current_transition[k] == 'X') {
							std::vector<std::vector<char>> temp_models;
							for(int j = 0; j < models.size(); j++) {
								std::vector<char> m = models[j];
								m.push_back('0');
								temp_models.push_back(m);
								models[j].push_back('1');
							}
							models.insert(models.end(),temp_models.begin(),temp_models.end());
						} else {
							for(int j = 0; j < models.size(); j++) {
								models[j].push_back(current_transition[k]);
							}
						}
					}
					// put loops first, other states at back
					for(int k = 0; k < models.size(); k++) {
						if(to_state != current_state) {
							next_states_matrix[i].push_back(std::make_pair(to_state, models[k]));
						} else {
							next_states_matrix[i].insert(next_states_matrix[i].begin(),std::make_pair(to_state,models[k]));
						}
					}

				} else {
					// put loops first, other states at back
					if(to_state != current_state) {
						next_states_matrix[i].push_back(std::make_pair(to_state, current_transition));
					} else {
						next_states_matrix[i].insert(next_states_matrix[i].begin(),std::make_pair(to_state,current_transition));
					}
				}
			} else {
				while (current_transition.size() < index) {
					unsigned i = current_transition.size();
					current_transition.push_back('X');
				}
				std::vector<char> left = current_transition;
				left.push_back('0');
				std::vector<char> right = current_transition;
				right.push_back('1');
				transition_stack.push_back(right);
				nodes.push_back(r);
				transition_stack.push_back(left);
				nodes.push_back(l);
			}
		}
  }

  //LOG(INFO) << "Done precomputing transition matrix";


  int start = this->dfa_->s;
	int sink = GetSinkState();
	bool get_more_models = true;
	// since we're not expanding dont-care characters ('X') yet, the models we find are unfinished
	std::set<std::vector<std::vector<char>>> unfinished_models;
	std::set<std::vector<std::vector<bool>>> finished_models;
	std::stack<std::pair<int,std::vector<std::vector<char>>>> models_to_process;
	std::vector<std::vector<char>> track_characters(num_tracks,std::vector<char>());
	models_to_process.push(std::make_pair(start,track_characters));
	int num_loops = 0;
	while(not models_to_process.empty() and get_more_models) {
		std::pair<int,std::vector<std::vector<char>>> current_model = models_to_process.top();
		models_to_process.pop();

		int current_state = current_model.first;
		int length = current_model.second[0].size() / var_per_track;

		if(shortest_accepting_path[current_state] + length > bound) {
			continue;
		}



		for(auto iter : next_states_matrix[current_state]) {
		// next_state is in first position
			int to_state = iter.first;
			// if the current length + shortest path to final state from to_state + 1 (for transition from current -> to_state)
			// is greater than bound, ignore
			if(to_state == sink || length + shortest_accepting_path[to_state]+1 > bound) {
				continue;
			}


			if(to_state != sink and (length < bound or bound == -1)) {
				std::vector<char> transition = iter.second;

				// transition is in second position
				track_characters = current_model.second;
				for(int i = 0; i < num_tracks; i++) {
					for(int k = 0; k < var_per_track; k++) {
						// since tracks are interleaved, track i's characters don't lie in order in the transition we got
						// however, this is a binaryint, so each var should only take 1 bit, so this isn't really needed
						track_characters[i].push_back(transition[i+num_tracks*k]);
					}
				}

				models_to_process.push(std::make_pair(to_state,track_characters));
			}
		}

		// check if its final state
		// since we can have any number of leading zeros or ones, first truncate
		// all leading zeros or ones (except for one) and add the transition if we haven't
		// seen it yet
		if(this->dfa_->f[current_state] == 1) {
			if((count_bound_exact_ and length == bound) or (not count_bound_exact_ and length <= bound)) {
//				LOG(INFO) << "Length: " << length;

				// for each track, truncate leading zeros or ones (except for one)
				// in dfa representation, we read backwards (0101 = 5, instead of 3) so leading zeros
				// or ones are at the end of the transition
				if(is_natural_number_) {
					// for unsigned, just get rid of leading 0s
					for(int i = 0; i < num_tracks; i++) {
						int pos = current_model.second[i].size()-1;
						while(current_model.second[i].back() == '0' and pos > 0) {
							current_model.second[i].pop_back();
							pos--;
						}
					}
				}
				else {
					// for signed, we need to get rid of most leading 0s and 1s
					for(int i = 0; i < num_tracks; i++) {
						char last_char = current_model.second[i].back();
						int pos = current_model.second[i].size()-2;
						while(pos >= 0 and current_model.second[i][pos] == last_char and last_char != 'X') {
							current_model.second[i].pop_back();
							pos--;
						}
					}
				}

				// if we haven't seen the truncated version, add it
				if(unfinished_models.find(current_model.second) == unfinished_models.end()) {
					int max_x = 0;
					// each track can have differing number of x's
					// find the max number of x's in all tracks
					for(int i = 0; i < num_tracks; i++) {
						int num_x = 0;
						for(int k = 0; k < current_model.second[i].size(); k++) {
							if(current_model.second[i][k] == 'X') {
								num_x++;
							}
						}
						if(num_x > max_x) {
							max_x = num_x;
						}
					}

					// for each 'X', there are 2 possible transitions
					models_so_far += (1 << max_x);
					unfinished_models.insert(current_model.second);

//					std::string s1,s2;
//					for(int k = 0; k < current_model.second[0].size(); k++) {
//						s1 += current_model.second[0][k];
//					}
//					for(int k = 0; k < current_model.second[1].size(); k++) {
//						s2 += current_model.second[1][k];
//					}
//					LOG(INFO) << "ADDED:";
//					LOG(INFO) << "  s1: " << s1;
//					LOG(INFO) << "  s2: " << s2;
//					LOG(INFO) << "";
//					std::cin.get();

					// set finish condition if necessary
					if(num_models != -1 and models_so_far >= num_models) {
						get_more_models = false;
					}
				}
			}
		}
	}

	//LOG(INFO) << "Got unfinished models";

	// unfinished_models contain 'X' (dont care) in transitions
	// we need to expand those
	bool expand = true;
	int num_initial = unfinished_models.size();
	int num_finished = 0;
	int count = 0;
	for(auto iter : unfinished_models) {
		int num_remaining = unfinished_models.size()-count;
		// for each track

		std::vector<std::vector<std::vector<bool>>> expanded_track_models(num_tracks);
		int cartesian_size = 1;
		for(int j = 0; j < iter.size(); j++) {
			// initial unfinished model
			int num_models_current_track = 1;

			// don't expand 'X's in transitions if we already have enough models
			// instead, flatten them to 0 or 1.
			if(expand and cartesian_size + num_remaining + num_finished >= num_models) {
				expand = false;
			}

			std::vector<std::vector<bool>> models;
			models.push_back(std::vector<bool>());

			for(int k = 0; k < iter[j].size(); k++) {
				// if a character is X (dont care), duplicate transition, one for 1, one for 0
				if(iter[j][k] == 'X') {
					// dont add both transitions for X if we are at the desired number of models
					if(!expand) {
						for(int i = 0; i < models.size(); i++) {
							models[i].push_back(0);
						}
					} else {
						std::vector<std::vector<bool>> temp_models;
						for(int i = 0; i < models.size(); i++) {
							// dont add both transitions for X if we are at the desired number of models
							if(expand) {
								std::vector<bool> m = models[i];
								m.push_back(1);
								temp_models.push_back(m);
								num_models_current_track++;
							}
							models[i].push_back(0);

						}
						models.insert(models.end(),temp_models.begin(),temp_models.end());
						if(num_finished + num_remaining + cartesian_size*num_models_current_track >= num_models) {
							expand = false;
						}
					}
				} else {
					for(int i = 0; i < models.size(); i++) {
						if(iter[j][k] == '0') {
							models[i].push_back(0);
						} else {
							models[i].push_back(1);
						}
					}
				}
			}
			cartesian_size *= num_models_current_track;
			expanded_track_models[j] = models;
		}

		std::vector<std::vector<bool>> temp_model(num_tracks);
		std::vector<int> next_model_to_use(num_tracks,0);
		// add all pairs in expanded_track_models to finished_models
		int pos = 0;
		do {
			pos = 0;
			// build the next model from next_model_to_use vector of positions
			for(int i = 0; i < num_tracks; i++) {
				temp_model[i] = expanded_track_models[i][next_model_to_use[i]];
			}
			// insert it into finished_models
			finished_models.insert(temp_model);

			while(pos < num_tracks and next_model_to_use[pos] >= expanded_track_models[pos].size()-1) {
				next_model_to_use[pos] = 0;
				pos++;
			}

			// increment position of next model we want to use if we're still in range
			if(pos < num_tracks) {
				next_model_to_use[pos]++;
			}

		} while (pos < num_tracks and finished_models.size() < num_models);

		count++;
	}

	//LOG(INFO) << "Got finished models";

	std::set<std::vector<int>> printable_models;
	for(auto iter : finished_models) {
		// only add num_models
		if(num_models != -1 and printable_models.size() >= num_models) {
			break;
		}

		std::vector<int> model(iter.size());
		for(int i = 0; i < iter.size(); i++) {
			unsigned int length = iter[i].size() / var_per_track;
			int num = 0;
			// if we're using signed numbers and the sign bit is set,
			// we need to add leading ones for c++ int to be negative
			if(not is_natural_number_ and iter[i][length-1] == 1) {
				int int_bytes = sizeof(int) * 8; // 8 bits per byte
				for(int k = 0; k < int_bytes-length; k++) {
					num |= 1;
					num <<= 1;
				}
			}

			// since bits are in reverse, iterate backwards
			for(int k = length-1; k >= 0; k--) {
				if(iter[i][k]) {
					num |= 1;
				} else {
					num |= 0;
				}
				if(k != 0) {
					num <<= 1;
				}
			}
			model[i] = num;
		}
		printable_models.insert(model);
	}

//	int count2 = 0;
//	for(auto iter: printable_models) {
//		LOG(INFO) << "Solution " << count2;
//		for(int i = 0; i < iter.size(); i++) {
//			LOG(INFO) << "	Track " << i << " = " << iter[i];
//		}
//		count2++;
//	}
//
//	LOG(INFO) << "num_models: " << unfinished_models.size();
//	LOG(INFO) << "num finished_models: " << finished_models.size();
//
	LOG(INFO) << "Number of models: " << printable_models.size();
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeBoolean(ArithmeticFormula_ptr formula) {

	auto boolean_variables = formula->GetBooleans();

	std::string boolean_var = boolean_variables.begin()->first;
	int index = formula->GetVariableIndex(boolean_var);

	int number_of_variables = formula->GetNumberOfVariables();
	int* bin_variable_indices = GetBddVariableIndices(number_of_variables);

	char statuses[3] = {'-', '+', '-'};
	std::vector<char> exception(number_of_variables,'X');
	exception[index] = (boolean_variables[boolean_var] ? '1' : '0');
	exception.push_back('\0');

	dfaSetup(3, number_of_variables, bin_variable_indices);
	dfaAllocExceptions(1);
	dfaStoreException(1, &*exception.begin());
	dfaStoreState(2);

	dfaAllocExceptions(1);
	exception[index] = '0';
	dfaStoreException(1, &*exception.begin());
	dfaStoreState(2);

	dfaAllocExceptions(0);
	dfaStoreState(2);

	auto boolean_dfa = dfaBuild(statuses);
	auto boolean_auto = new BinaryIntAutomaton(boolean_dfa,formula,false);

	DVLOG(VLOG_LEVEL) << boolean_auto->id_ << " = [BinaryIntAutomaton]->MakeBoolean()";


	return boolean_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeIntGraterThanOrEqualToZero(std::vector<int> indexes,
                                                                          int number_of_variables) {
  int* bin_variable_indices = GetBddVariableIndices(number_of_variables);
  int number_of_states = 3;
  char statuses[3] { '-', '+', '-' };
  std::vector<char> exception;

  for (int i = 0; i < number_of_variables; i++) {
    exception.push_back('X');
  }
  exception.push_back('\0');

  dfaSetup(3, number_of_variables, bin_variable_indices);
  dfaAllocExceptions(1);
  for (int i : indexes) {
    exception[i] = '0';
  }
  dfaStoreException(1, &*exception.begin());
  dfaStoreState(0);

  dfaAllocExceptions(1);
  for (int i : indexes) {
    exception[i] = '1';
  }
  dfaStoreException(0, &*exception.begin());
  dfaStoreState(1);

  dfaAllocExceptions(0);
  dfaStoreState(2);

  auto positive_numbers_dfa = dfaBuild(statuses);
  auto postivie_numbers_auto = new BinaryIntAutomaton(positive_numbers_dfa, number_of_variables, false);

  //delete[] bin_variable_indices;

  DVLOG(VLOG_LEVEL) << postivie_numbers_auto->id_
                    << " = [BinaryIntAutomaton]->MakeIntGraterThanOrEqualToZero(<indexes>, " << number_of_variables
                    << ")";
  return postivie_numbers_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeEquality(ArithmeticFormula_ptr formula, bool is_natural_number) {
  if (is_natural_number) {
    return MakeNaturalNumberEquality(formula);
  } else {
    return MakeIntEquality(formula);
  }
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeIntEquality(ArithmeticFormula_ptr formula) {


  if (not formula->Simplify()) {
    auto equality_auto = BinaryIntAutomaton::MakePhi(formula, false);
    DVLOG(VLOG_LEVEL) << equality_auto->id_ << " = MakeIntEquality(" << *formula << ")";
    return equality_auto;
  }

//  auto new_coeff_map = new_formula->GetVariableCoefficientMap();
//  ArithmeticFormula_ptr formula = new ArithmeticFormula();
//  formula->SetType(new_formula->GetType());
//  for(auto variable_coeff : new_coeff_map) {
//    if(variable_coeff.second != 0) {
//      formula->AddVariable(variable_coeff.first, variable_coeff.second);
//    }
//  }

  auto coeffs_map = formula->GetVariableCoefficientMap();
  auto coeffs = formula->GetCoefficients();
  auto boolean_variables = formula->GetBooleans();
  int min = 0, max = 0, num_of_zero_coefficient = 0;
  for (int coeff : coeffs) {
    if (coeff > 0) {
      max += coeff;
    } else if (coeff < 0) {
      min += coeff;
    } else {
      ++num_of_zero_coefficient;
    }
  }

  const int constant = formula->GetConstant();
  if (max < constant) {
    max = constant;
  } else if (min > constant) {
    min = constant;
  }

  const int num_of_states = 2 * (max - min + 2);
  const int sink_state = num_of_states - 2;
  const int shifted_initial_state = num_of_states - 1;

  unsigned max_states_allowed = 0x80000000;
  unsigned mona_check = 8 * num_of_states;
  CHECK_LE(mona_check, max_states_allowed);  // otherwise, MONA infinite loops

  const int total_num_variables = formula->GetNumberOfVariables();
  const int active_num_variables = total_num_variables - num_of_zero_coefficient;
  CHECK_LT(active_num_variables, 64);
  // TODO instead of doing shift, try to update algorithm
  unsigned long transitions = 1 << active_num_variables;  //number of transitions from each state

  int* indices = GetBddVariableIndices(total_num_variables);
  dfaSetup(num_of_states, total_num_variables, indices);

  std::map<std::vector<char>, int> transitions_from_initial_state; // populated if initial state is in cycle and accepting

  std::map<int, StateIndices> carry_map;  // maps carries to state indices
  carry_map[constant].sr = 1;
  carry_map[constant].i = -1;
  carry_map[constant].ir = 0;

  const bool is_equality = (ArithmeticFormula::Type::EQ == formula->GetType());
  const bool needs_shift_state = (not is_equality);
  bool is_initial_state_shifted = false;

  int next_index = 0,
      next_label = constant,
      current_state = 0;

  while (next_label < max + 1) {  //there is a state to expand (excuding sink)
    if (carry_map[next_label].i == current_state) {
      carry_map[next_label].s = 2;
    } else {
      carry_map[next_label].sr = 2;
    }

    dfaAllocExceptions(transitions / 2);
    int result, target;
    for (unsigned long j = 0; j < transitions; j++) {
      result = next_label + formula->CountOnes(j);
      if (not (result & 1)) {
        std::vector<char> binary_string = GetReversedBinaryFormat(j, active_num_variables);
        std::vector<char> current_exception(total_num_variables, 'X');
        current_exception.push_back('\0');
        for (int i = 0, k = 0; i < total_num_variables; i++) {
          if (coeffs[i] != 0) {
            current_exception[i] = binary_string[k];
            ++k;
          }
        }
        for (auto& it : boolean_variables) {
        	int temp_index = coeffs_map[it.first];
        	if(current_state == 0) {
        		current_exception[temp_index] = (it.second) ? '1' : '0';
        	} else {
        		current_exception[temp_index] = 0;
        	}
        }
        target = result / 2;
        int to_state;
        if (target == next_label) {
          if (carry_map[target].s == 0) {
            carry_map[target].s = 1;
            ++next_index;
            carry_map[target].i = next_index;
          }
          to_state = carry_map[target].i;
        } else {
          if (carry_map[target].sr == 0) {
            carry_map[target].sr = 1;
            ++next_index;
            carry_map[target].ir = next_index;
          }
          to_state = carry_map[target].ir;
        }

        if (needs_shift_state) {
          if (to_state == 0) {
            to_state = shifted_initial_state;
            is_initial_state_shifted = true;
          }
          if (current_state == 0) { // save transition for shifted initial start
            transitions_from_initial_state[current_exception] = to_state;
          }
        }
        dfaStoreException(to_state, &current_exception[0]);
      }
    }

    dfaStoreState(sink_state);

    ++current_state;

    //find next state to expand
    for (next_label = min;
        (next_label <= max) and (carry_map[next_label].i != current_state) and (carry_map[next_label].ir != current_state);
        ++next_label) {
    }
  }

  for (; current_state < num_of_states; ++current_state) {
    if (is_initial_state_shifted and current_state == shifted_initial_state) {
      dfaAllocExceptions(transitions_from_initial_state.size());
      for (auto& el : transitions_from_initial_state) {
        auto excep = el.first;
        dfaStoreException(el.second, &excep[0]);
      }
      dfaStoreState(sink_state);
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(sink_state);
    }
  }

  //define accepting and rejecting states
  char initial_status = '-';
  char target_status = '+';
  if (not is_equality) {
    initial_status = '+';
    target_status = '-';
  }

  //define accepting and rejecting states
  char *statuses = new char[num_of_states + 1];
  statuses[0] = '-';
  for (int i = 1; i < num_of_states; ++i) {
    statuses[i] = initial_status;
  }

  for (next_label = min; next_label <= max; ++next_label) {
    if (carry_map[next_label].s == 2) {
      if (carry_map[next_label].i == 0 and is_initial_state_shifted) {
        statuses[shifted_initial_state] = target_status;
      } else {
        statuses[carry_map[next_label].i] = target_status;
      }
    }
  }

  statuses[num_of_states] = '\0';
  auto tmp_dfa = dfaBuild(statuses);
  auto equality_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);
  //delete[] indices;
  delete[] statuses;

  auto equality_auto = new BinaryIntAutomaton(equality_dfa, formula, false);
  CHECK_EQ(false, equality_auto->IsInitialStateAccepting());

//  auto temp_auto = equality_auto->ChangeIndicesMap(new_formula);
//
//  delete equality_auto;
//  equality_auto = temp_auto;

  DVLOG(VLOG_LEVEL) << equality_auto->id_ << " = MakeIntEquality(" << *formula << ")";
  return equality_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeNaturalNumberEquality(ArithmeticFormula_ptr formula) {
  if (not formula->Simplify()) {
    auto equality_auto = BinaryIntAutomaton::MakePhi(formula, true);
    DVLOG(VLOG_LEVEL) << equality_auto->id_ << " = MakeNaturalNumberEquality(" << *formula << ")";
    return equality_auto;
  }

  // auto new_coeff_map = new_formula->GetVariableCoefficientMap();
  // ArithmeticFormula_ptr formula = new ArithmeticFormula();
  // formula->SetType(new_formula->GetType());
  // for(auto variable_coeff : new_coeff_map) {
  //   if(variable_coeff.second != 0) {
  //     formula->AddVariable(variable_coeff.first, variable_coeff.second);
  //   }
  // }



  auto coeffs_map = formula->GetVariableCoefficientMap();
	auto coeffs = formula->GetCoefficients();
	auto boolean_variables = formula->GetBooleans();
  int min = 0, max = 0, num_of_zero_coefficient = 0;
  for (int coeff : coeffs) {
    if (coeff > 0) {
      max += coeff;
    } else if (coeff < 0) {
      min += coeff;
    } else {
      ++num_of_zero_coefficient;
    }
  }

  const int constant = formula->GetConstant();
  if (max < constant) {
    max = constant;
  } else if (min > constant) {
    min = constant;
  }

  const int num_of_states = max - min + 3;
  const int sink_state = num_of_states - 2;
  const int shifted_initial_state = num_of_states - 1;

  unsigned max_states_allowed = 0x80000000;
  unsigned mona_check = 8 * num_of_states;
  CHECK_LE(mona_check, max_states_allowed);  // otherwise, MONA infinite loops

  const int total_num_variables = formula->GetNumberOfVariables();
  const int active_num_variables = total_num_variables - num_of_zero_coefficient;
  CHECK_LT(active_num_variables, 64);
  // TODO instead of doing shift, try to update algorithm
  unsigned long transitions = 1 << active_num_variables;  //number of transitions from each state

  int* indices = GetBddVariableIndices(total_num_variables);
  dfaSetup(num_of_states, total_num_variables, indices);

  std::map<std::vector<char>, int> transitions_from_initial_state; // populated if initial state is in cycle and accepting

  std::map<int, StateIndices> carry_map;  // maps carries to state indices
  carry_map[constant].s = 1;
  carry_map[constant].i = 0;

  const bool is_equality = (ArithmeticFormula::Type::EQ == formula->GetType());
  const bool needs_shift_state = ((is_equality and constant == 0) or ((not is_equality) and constant != 0));
  bool is_initial_state_shifted = false;

  int next_index = 0,
      next_label = constant,
      current_state = 0;

  while (next_label < max + 1) {  //there is a state to expand (excuding sink)
    carry_map[next_label].s = 2;

    dfaAllocExceptions(transitions / 2);
    int result, target;
    for (unsigned long j = 0; j < transitions; ++j) {
      result = next_label + formula->CountOnes(j);
      if (not (result & 1)) {
        target = result / 2;
        if (carry_map[target].s == 0) {
          carry_map[target].s = 1;
          ++next_index;
          carry_map[target].i = next_index;
        }

        std::vector<char> binary_string = GetReversedBinaryFormat(j, active_num_variables);
        std::vector<char> current_exception(total_num_variables, 'X');
        current_exception.push_back('\0');
        for (int i = 0, k = 0; i < total_num_variables; i++) {
          if (coeffs[i] != 0) {
            current_exception[i] = binary_string[k];
            ++k;
          }
        }
        for (auto& it : boolean_variables) {
					int temp_index = coeffs_map[it.first];
					if(current_state == 0) {
						current_exception[temp_index] = (it.second) ? '1' : '0';
					} else {
						current_exception[temp_index] = 0;
					}
				}
        // hack to avoid an accepting initial state
        int to_state = carry_map[target].i;
        if (needs_shift_state) { // initial state is accepting, shift it
          if (to_state == 0) {
            to_state = shifted_initial_state;
            is_initial_state_shifted = true;
          }
          if (current_state == 0) { // save transition for shifted initial start
            transitions_from_initial_state[current_exception] = to_state;
          }
        }
        dfaStoreException(to_state, &current_exception[0]);
      }
    }

    dfaStoreState(sink_state);

    ++current_state;

    //find next state to expand
    for (next_label = min;
        (next_label <= max) and (carry_map[next_label].i != current_state);
        ++next_label) {
    }

  }

  for (; current_state < num_of_states; ++current_state) {
    if (is_initial_state_shifted and current_state == shifted_initial_state) {
      dfaAllocExceptions(transitions_from_initial_state.size());
      for (auto& el : transitions_from_initial_state) {
        auto excep = el.first;
        dfaStoreException(el.second, &excep[0]);
      }
      dfaStoreState(sink_state);
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(sink_state);
    }
  }

  //define accepting and rejecting states
  char initial_status = '-';
  char target_status = '+';
  if (not is_equality) {
    initial_status = '+';
    target_status = '-';
  }

  char *statuses = new char[num_of_states + 1];
  statuses[0] = '-';
  for (int i = 1; i < num_of_states; i++) {
    statuses[i] = initial_status;
  }

  if (carry_map[0].s == 2) {
    if (carry_map[0].i == 0 and is_initial_state_shifted) {
      statuses[shifted_initial_state] = target_status;
    } else {
      statuses[carry_map[0].i] = target_status;
    }
  }

  statuses[num_of_states] = '\0';

  auto tmp_dfa = dfaBuild(statuses);
  auto equality_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);
  //delete[] indices;
  delete[] statuses;

  auto equality_auto = new BinaryIntAutomaton(equality_dfa, formula, true);
  CHECK_EQ(false, equality_auto->IsInitialStateAccepting());

  // auto temp_auto = equality_auto->ChangeIndicesMap(new_formula);
  // delete equality_auto;
  // equality_auto = temp_auto;

  DVLOG(VLOG_LEVEL) << equality_auto->id_ << " = MakeNaturalNumberEquality(" << formula << ")";
  return equality_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeLessThan(ArithmeticFormula_ptr formula, bool is_natural_number) {
  if (is_natural_number) {
    return MakeNaturalNumberLessThan(formula);
  } else {
    return MakeIntLessThan(formula);
  }
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeIntLessThan(ArithmeticFormula_ptr formula) {
  if (not formula->Simplify()) {
    DVLOG(VLOG_LEVEL) << "no simplify...";
    auto equality_auto = BinaryIntAutomaton::MakePhi(formula, true);
    DVLOG(VLOG_LEVEL) << equality_auto->id_ << " = MakeIntLessThan(" << *formula << ")";
    return equality_auto;
  }

  // auto new_coeff_map = new_formula->GetVariableCoefficientMap();
  // ArithmeticFormula_ptr formula = new ArithmeticFormula();
  // formula->SetType(new_formula->GetType());
  // for(auto variable_coeff : new_coeff_map) {
  //   if(variable_coeff.second != 0) {
  //     formula->AddVariable(variable_coeff.first, variable_coeff.second);
  //   }
  // }

  auto coeffs_map = formula->GetVariableCoefficientMap();
	auto boolean_variables = formula->GetBooleans();
  auto coeffs = formula->GetCoefficients();
  int min = 0, max = 0, num_of_zero_coefficient = 0;
  for (int coeff : coeffs) {
    if (coeff > 0) {
      max += coeff;
    } else if (coeff < 0) {
      min += coeff;
    } else {
      ++num_of_zero_coefficient;
    }
  }

  const int constant = formula->GetConstant();
  if (max < constant) {
    max = constant;
  } else if (min > constant) {
    min = constant;
  }

  const int num_of_states = 2 * (max - min + 1);

  unsigned max_states_allowed = 0x80000000;
  unsigned mona_check = 8 * num_of_states;
  CHECK_LE(mona_check, max_states_allowed);  // otherwise, MONA infinite loops

  const int total_num_variables = formula->GetNumberOfVariables();
  const int active_num_variables = total_num_variables - num_of_zero_coefficient;
  CHECK_LT(active_num_variables, 64);
  // TODO instead of doing shift, try to update algorithm
  unsigned long transitions = 1 << active_num_variables;  //number of transitions from each state

  int* indices = GetBddVariableIndices(total_num_variables);
  dfaSetup(num_of_states, total_num_variables, indices);

  std::map<int, StateIndices> carry_map;  // maps carries to state indices
  carry_map[constant].sr = 1;
  carry_map[constant].i = -1;
  carry_map[constant].ir = 0;

  int next_index = 0,
      next_label = constant,
      current_state = 0;

  while (next_label < max + 1) {  //there is a state to expand (excuding sink)
    if (carry_map[next_label].i == current_state) {
      carry_map[next_label].s = 2;
    } else {
      carry_map[next_label].sr = 2;
    }

    // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
    dfaAllocExceptions(transitions);
    int result, target, write1, label1, label2;
    for (unsigned long j = 0; j < transitions; j++) {
      int ones = formula->CountOnes(j);
      result = next_label + ones;
      if (result >= 0) {
        target = result / 2;
      } else {
        target = (result - 1) / 2;
      }

      write1 = result & 1;
      label1 = next_label;
      label2 = target;

      while (label1 != label2) {
        label1 = label2;
        result = label1 + ones;
        if (result >= 0) {
          label2 = result / 2;
        } else {
          label2 = (result - 1) / 2;
        }
        write1 = result & 1;
      }

      std::vector<char> binary_string = GetReversedBinaryFormat(j, active_num_variables);
      std::vector<char> current_exception(total_num_variables, 'X');
      current_exception.push_back('\0');
      for (int i = 0, k = 0; i < total_num_variables; i++) {
        if (coeffs[i] != 0) {
          current_exception[i] = binary_string[k];
          ++k;
        }
      }
      for (auto& it : boolean_variables) {
				int temp_index = coeffs_map[it.first];
				if(current_state == 0) {
					current_exception[temp_index] = (it.second) ? '1' : '0';
				} else {
					current_exception[temp_index] = 0;
				}
			}

      if (write1) {
        if (carry_map[target].s == 0) {
          carry_map[target].s = 1;
          next_index++;
          carry_map[target].i = next_index;
        }
        dfaStoreException(carry_map[target].i, &current_exception[0]);
      } else {
        if (carry_map[target].sr == 0) {
          carry_map[target].sr = 1;
          next_index++;
          carry_map[target].ir = next_index;
        }
        dfaStoreException(carry_map[target].ir, &current_exception[0]);
      }
    }

    dfaStoreState(current_state);

    ++current_state;

    //find next state to expand
    for (next_label = min;
        (next_label <= max) and (carry_map[next_label].i != current_state) and (carry_map[next_label].ir != current_state);
        ++next_label) {
    }

  }

  for (; current_state < num_of_states; ++current_state) {
    dfaAllocExceptions(0);
    dfaStoreState(current_state);
  }

  //define accepting and rejecting states
  char *statuses = new char[num_of_states + 1];
  for (int i = 0; i < num_of_states; ++i) {
    statuses[i] = '-';
  }

  for (next_label = min; next_label <= max; ++next_label) {
    if (carry_map[next_label].s == 2) {
      statuses[carry_map[next_label].i] = '+';
    }
  }
  statuses[num_of_states] = '\0';

  auto tmp_dfa = dfaBuild(statuses);
  auto less_than_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);
  //delete[] indices;
  delete[] statuses;

  auto less_than_auto = new BinaryIntAutomaton(less_than_dfa, formula, false);
  CHECK_EQ(false, less_than_auto->IsInitialStateAccepting());

  // for(auto iter : formula->GetVariableCoefficientMap()) {
  //   LOG(INFO) << iter.first << "," << iter.second;
  // }
  // auto temp_auto = less_than_auto->ChangeIndicesMap(new_formula);
  // for(auto iter : new_formula->GetVariableCoefficientMap()) {
  //   LOG(INFO) << iter.first << "," << iter.second;
  // }

  // delete less_than_auto;
  // less_than_auto = temp_auto;

  DVLOG(VLOG_LEVEL) << less_than_auto->id_ << " = MakeIntLessThan(" << formula << ")";
  return less_than_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeNaturalNumberLessThan(ArithmeticFormula_ptr formula) {
  formula->Simplify();

  // auto new_coeff_map = new_formula->GetVariableCoefficientMap();
  // ArithmeticFormula_ptr formula = new ArithmeticFormula();
  // formula->SetType(new_formula->GetType());
  // for(auto variable_coeff : new_coeff_map) {
  //   if(variable_coeff.second != 0) {
  //     formula->AddVariable(variable_coeff.first, variable_coeff.second);
  //   }
  // }

  auto coeffs_map = formula->GetVariableCoefficientMap();
	auto boolean_variables = formula->GetBooleans();
  auto coeffs = formula->GetCoefficients();
  int min = 0, max = 0, num_of_zero_coefficient = 0;
  for (int coeff : coeffs) {
    if (coeff > 0) {
      max += coeff;
    } else if (coeff < 0) {
      min += coeff;
    } else {
      ++num_of_zero_coefficient;
    }
  }

  const int constant = formula->GetConstant();
  if (max < constant) {
    max = constant;
  } else if (min > constant) {
    min = constant;
  }

  const int num_of_states = max - min + 2;
  const int shifted_initial_state = num_of_states - 1;

  unsigned max_states_allowed = 0x80000000;
  unsigned mona_check = 8 * num_of_states;
  CHECK_LE(mona_check, max_states_allowed);  // otherwise, MONA infinite loops

  const int total_num_variables = formula->GetCoefficients().size();
  const int active_num_variables = total_num_variables - num_of_zero_coefficient;
  CHECK_LT(active_num_variables, 64);
  // TODO instead of allocating that many of transitions, try to reduce them with a preprocessing
  unsigned long transitions = 1 << active_num_variables;  //number of transitions from each state

  int* indices = GetBddVariableIndices(total_num_variables);
  dfaSetup(num_of_states, total_num_variables, indices);

  std::map<std::vector<char>, int> transitions_from_initial_state; // populated if initial state is in cycle and accepting
  bool is_initial_state_in_cycle = false;

  std::map<int, StateIndices> carry_map;  // maps carries to state indices
  carry_map[constant].s = 1;
  carry_map[constant].i = 0;

  int next_index = 0,
      next_label = constant,
      current_state = 0;

  while (next_label < max + 1) {  //there is a state to expand (excuding sink)
    carry_map[next_label].s = 2;

    dfaAllocExceptions(transitions);

    int result, target;
    for (unsigned long j = 0; j < transitions; ++j) {
      result = next_label + formula->CountOnes(j);
      if (result >= 0) {
        target = result / 2;
      } else {
        target = (result - 1) / 2;
      }

      if (carry_map[target].s == 0) {
        carry_map[target].s = 1;
        ++next_index;
        carry_map[target].i = next_index;
      }

      std::vector<char> binary_string = GetReversedBinaryFormat(j, active_num_variables);
      std::vector<char> current_exception(total_num_variables, 'X');
      current_exception.push_back('\0');
      for (int i = 0, k = 0; i < total_num_variables; i++) {
        if (coeffs[i] != 0) {
          current_exception[i] = binary_string[k];
          ++k;
        }
      }
      for (auto& it : boolean_variables) {
				int temp_index = coeffs_map[it.first];
				if(current_state == 0) {
					current_exception[temp_index] = (it.second) ? '1' : '0';
				} else {
					current_exception[temp_index] = 0;
				}
			}

      // hack to avoid an accepting initial state
      int to_state = carry_map[target].i;

      if (to_state == 0) {
        to_state = shifted_initial_state;
        is_initial_state_in_cycle = true;
      }
      if (current_state == 0 and is_initial_state_in_cycle) { // save transition for shifted initial start
        transitions_from_initial_state[current_exception] = to_state;
      }
      dfaStoreException(to_state, &current_exception[0]);
    }

    dfaStoreState(current_state);
    ++current_state;

    //find next state to expand
    for (next_label = min;
        (next_label <= max) and (carry_map[next_label].i != current_state);
        ++next_label) {
    }

  }

  for (; current_state < num_of_states; ++current_state) {
    if (is_initial_state_in_cycle and current_state == shifted_initial_state) {
      dfaAllocExceptions(transitions_from_initial_state.size());
      for (auto& el : transitions_from_initial_state) {
        auto excep = el.first;
        dfaStoreException(el.second, &excep[0]);
      }
      dfaStoreState(current_state);
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(current_state);
    }
  }

  //define accepting and rejecting states
  char *statuses = new char[num_of_states + 1];
  for (int i = 0; i < num_of_states; ++i) {
    statuses[i] = '-';
  }

  for (int i = min; i < 0; ++i) {
    if (carry_map[i].s == 2) {
      if (carry_map[i].i == 0 ) {
        if (is_initial_state_in_cycle) {
          statuses[shifted_initial_state] = '+';
        }
      } else {
        statuses[carry_map[i].i] = '+';
      }
    }
  }
  statuses[num_of_states] = '\0';
  auto tmp_dfa = dfaBuild(statuses);
  auto less_than_dfa = dfaMinimize(tmp_dfa);
  dfaFree(tmp_dfa);
  //delete[] indices;
  delete[] statuses;

  auto less_than_auto = new BinaryIntAutomaton(less_than_dfa, formula, true);
  CHECK_EQ(false, less_than_auto->IsInitialStateAccepting());

  // auto temp_auto = less_than_auto->ChangeIndicesMap(new_formula);

  // delete less_than_auto;
  // less_than_auto = temp_auto;

  DVLOG(VLOG_LEVEL) << less_than_auto->id_ << " = MakeNaturalNumberLessThan(" << formula << ")";
  return less_than_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeLessThanOrEqual(ArithmeticFormula_ptr formula, bool is_natural_number) {
  auto less_than_formula = formula->clone();
  less_than_formula->SetConstant(less_than_formula->GetConstant() - 1);
  less_than_formula->SetType(ArithmeticFormula::Type::LT);

  auto less_than_or_equal_auto = BinaryIntAutomaton::MakeLessThan(less_than_formula, is_natural_number);
  less_than_or_equal_auto->SetFormula(formula);

  DVLOG(VLOG_LEVEL) << less_than_or_equal_auto->id_ << " = MakeLessThanOrEqual(" << *formula << ")";
  return less_than_or_equal_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeGreaterThan(ArithmeticFormula_ptr formula, bool is_natural_number) {
  auto less_than_formula = formula->Multiply(-1);
  less_than_formula->SetType(ArithmeticFormula::Type::LT);

  auto greater_than_auto = BinaryIntAutomaton::MakeLessThan(less_than_formula, is_natural_number);
  greater_than_auto->SetFormula(formula);

  DVLOG(VLOG_LEVEL) << greater_than_auto->id_ << " = MakeGreaterThan(" << *formula << ")";
  return greater_than_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeGreaterThanOrEqual(ArithmeticFormula_ptr formula,
                                                                  bool is_natural_number) {
  auto less_than_formula = formula->Multiply(-1);
  less_than_formula->SetConstant(less_than_formula->GetConstant() - 1);
  less_than_formula->SetType(ArithmeticFormula::Type::LT);

  auto greater_than_or_equal_auto = BinaryIntAutomaton::MakeLessThan(less_than_formula, is_natural_number);
  greater_than_or_equal_auto->SetFormula(formula);

  DVLOG(VLOG_LEVEL) << greater_than_or_equal_auto->id_ << " = MakeGreaterThanOrEqual(" << *formula << ")";
  return greater_than_or_equal_auto;
}

BinaryIntAutomaton_ptr BinaryIntAutomaton::MakeTrimHelperAuto(int var_index, int number_of_variables) {
  char statuses[5] = { '-', '+', '+', '-', '-' };
  char* exception = new char[number_of_variables + 1];
  for (int i = 0; i < number_of_variables; i++) {
    exception[i] = 'X';
  }
  exception[number_of_variables] = '\0';

  int* indices = GetBddVariableIndices(number_of_variables);
  int number_of_states = 5;
  dfaSetup(number_of_states, number_of_variables, indices);
  // state 0
  dfaAllocExceptions(2);
  exception[var_index] = '0';
  dfaStoreException(1, exception);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(0);
  // state 1
  dfaAllocExceptions(2);
  exception[var_index] = '0';
  dfaStoreException(3, exception);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(1);
  // state 2
  dfaAllocExceptions(1);
  exception[var_index] = '0';
  dfaStoreException(4, exception);
  dfaStoreState(2);
  // state 3
  dfaAllocExceptions(1);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(3);
  // state 4
  dfaAllocExceptions(1);
  exception[var_index] = '1';
  dfaStoreException(2, exception);
  dfaStoreState(4);

  auto trim_helper_dfa = dfaBuild(statuses);
  auto trim_helper_auto = new BinaryIntAutomaton(trim_helper_dfa, number_of_variables, false);

  //delete[] indices;
  delete[] exception;

  DVLOG(VLOG_LEVEL) << trim_helper_auto->id_ << " = [BinaryIntAutomaton]->MakeTrimHelperAuto(" << var_index << ", "
                    << number_of_variables << ")";
  return trim_helper_auto;
}

void BinaryIntAutomaton::ComputeBinaryStates(std::vector<BinaryState_ptr>& binary_states,
                                               SemilinearSet_ptr semilinear_set) {
  if (semilinear_set->get_period() == 0) {
    AddBinaryState(binary_states, semilinear_set->get_constants());
  } else {
    AddBinaryState(binary_states, semilinear_set->get_cycle_head(), semilinear_set->get_period(), BinaryState::Type::VAL,
                     -1, -1);
  }
}

/**
 * works for positive numbers for now
 */
void BinaryIntAutomaton::AddBinaryState(std::vector<BinaryState_ptr>& binary_states, std::vector<int>& constants) {
  std::map<std::pair<int, int>, int> binary_state_map;

  binary_states.push_back(new BinaryState(-1, 0));
  binary_state_map.insert(std::make_pair(std::make_pair(-1, 0), 0));

  for (auto value : constants) {
    CHECK_GE(value, 0)<< "works for positive numbers only";
    unsigned i = 0;
    int rank = 1;
    int mask = value;
    int state_value = 0;
    int current_bit = 0;

    do {
      current_bit = mask & 1;
      if (current_bit) {
        state_value = state_value | (1 << (rank - 1));
      }
      auto key = std::make_pair(state_value, rank);
      auto it = binary_state_map.find(key);

      if (it == binary_state_map.end()) {
        binary_states.push_back(new BinaryState(state_value, rank));

        int index = binary_states.size() - 1;
        binary_state_map[key] = index;
        if (current_bit) {
          binary_states[i]->setd1(index);
        } else {
          binary_states[i]->setd0(index);
        }
        i = index;
      } else {
        i = it->second;
      }

      mask >>= 1;
      rank += 1;
    }while (state_value not_eq value);
  }
}

int BinaryIntAutomaton::AddBinaryState(std::vector<BinaryState_ptr>& binary_states, int C, int R, BinaryState::Type t,
                                         int v, int b) {
  unsigned i = 0;
  int d0 = -1, d1 = -1;

  for (i = 0; i < binary_states.size(); i++) {
    if (binary_states[i]->isEqualTo(t, v, b)) {
      return i;
    }
  }

  binary_states.push_back(new BinaryState(t, v, b));

  if (b < 0) {
    if (C == 0) {
      d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, 1 % R, 1 % R);
      d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, 0, 1 % R);
    } else if (C == 1) {
      d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, 1 % R, 1 % R);
      d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMF, 0, 1 % R);
    } else {
      d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, 1, 1);
      d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, 0, 1);
    }
  } else if (BinaryState::Type::VAL == t && (v + 2 * b >= C)) {
    d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
    d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMF, v % R, (2 * b) % R);
  } else if (BinaryState::Type::VAL == t && (v + 2 * b < C)) {
    d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, v + 2 * b, 2 * b);
    d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::VAL, v, 2 * b);
  } else if (BinaryState::Type::REMT == t) {
    d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
    d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, v % R, (2 * b) % R);
  } else if (BinaryState::Type::REMF == t) {
    d1 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMT, (v + 2 * b) % R, (2 * b) % R);
    d0 = AddBinaryState(binary_states, C, R, BinaryState::Type::REMF, v % R, (2 * b) % R);
  }

  binary_states[i]->setd0d1(d0, d1);

  return i;
}

bool BinaryIntAutomaton::is_accepting_binary_state(BinaryState_ptr binary_state, SemilinearSet_ptr semilinear_set) {
  if (BinaryState::Type::VAL == binary_state->getType()) {
    for (auto i : semilinear_set->get_constants()) {
      if (i == binary_state->getV()) {
        return true;
      }
    }
  } else if (BinaryState::Type::REMT == binary_state->getType()) {
    for (auto i : semilinear_set->get_periodic_constants()) {
      if (((i + semilinear_set->get_cycle_head()) % (semilinear_set->get_period())) == binary_state->getV()) {
        return true;
      }
    }
  }
  return false;
}

bool BinaryIntAutomaton::GetCycleStatus(std::map<int, bool>& cycle_status) {
  std::map<int, int> disc;
  std::map<int, int> low;
  std::map<int, bool> is_stack_member;
  std::vector<int> st;
  std::vector<bool> path;
  int time = 0;
  int sink_state = GetSinkState();

  if (sink_state > 0) {
    disc[sink_state] = 0;  // avoid exploring sink state
    is_stack_member[sink_state] = false;  // avoid looping to sink state
    cycle_status[sink_state] = true;
  }
  GetCycleStatus(this->dfa_->s, disc, low, st, is_stack_member, cycle_status, time);
  DVLOG(VLOG_LEVEL) << cycle_status[-2] << " = [" << this->id_ << "]->getCycleStatus(<constants>)";
  return cycle_status[-2];  // -2 is to keep if it is cyclic at all or not
}

void BinaryIntAutomaton::GetCycleStatus(int state, std::map<int, int>& disc, std::map<int, int>& low,
                                        std::vector<int>& st, std::map<int, bool>& is_stack_member,
                                        std::map<int, bool>& cycle_status, int& time) {
  int next_state = 0;
  std::vector<char> exception = { '0' };
  int l, r;
//  std::cout << "visiting: " << state << std::endl;
  disc[state] = low[state] = time;
  time++;
  st.push_back(state);
  is_stack_member[state] = true;

  l = getNextState(state, exception);
  exception[0] = '1';
  r = getNextState(state, exception);

  for (int b = 0; b < 2; b++) {
    next_state = (b == 0) ? l : r;
    if (disc.find(next_state) == disc.end()) {
      GetCycleStatus(next_state, disc, low, st, is_stack_member, cycle_status, time);
      low[state] = std::min(low[state], low[next_state]);
    } else if (is_stack_member[next_state]) {
      low[state] = std::min(low[state], disc[next_state]);
    }
  }

  if (low[state] == disc[state]) {  // head of SCC
    int current_state = st.back();

    while (current_state != state) {
      st.pop_back();
      is_stack_member[current_state] = false;
      cycle_status[current_state] = true;
      cycle_status[-2] = true;
      current_state = st.back();
    }

    is_stack_member[current_state] = false;
    st.pop_back();

    if (current_state == l or current_state == r) {
      cycle_status[current_state] = true;
      cycle_status[-2] = true;
    }
  }

  return;
}

void BinaryIntAutomaton::GetConstants(std::map<int, bool>& cycle_status, std::vector<int>& constants) {
  std::vector<bool> path;

  // current state cannot be accepting in binary automaton
  if ((not IsSinkState(this->dfa_->s)) and (not cycle_status[this->dfa_->s])) {
    GetConstants(this->dfa_->s, cycle_status, path, constants);
  }

  DVLOG(VLOG_LEVEL) << "<void> = [" << this->id_ << "]->getConstants(<cycle status>, <constants>)";
  return;
}

void BinaryIntAutomaton::GetConstants(int state, std::map<int, bool>& cycle_status, std::vector<bool>& path,
                                      std::vector<int>& constants) {
  int next_state = 0;
  std::vector<char> exception = { '0' };
  int l, r;

  if (path.size() > 31) {  // limit samples to integer length for now
    return;
  }

  l = getNextState(state, exception);
  exception[0] = '1';
  r = getNextState(state, exception);

  for (int b = 0; b < 2; b++) {
    next_state = (b == 0) ? l : r;

    if ((not IsSinkState(next_state))) {
      path.push_back(b == 1);
      if (IsAcceptingState(next_state)) {
        unsigned c = 0;
        for (unsigned i = 0; i < path.size(); i++) {
          if (path[i]) {
            c += (1 << i);
          }
        }
        constants.push_back(c);
      }
      if (not cycle_status[next_state]) {  // if next state is not in a cycle continue exploration
        GetConstants(next_state, cycle_status, path, constants);
      }
      path.pop_back();
    }
  }
}

/**
 * TODO that function does not catch all the constants because of automaton structure
 * Sets constant numbers accepted by this automaton
 * (constant numbers are reachable without involving any SCC except the ones with size 1)
 * @return true if automaton is cyclic, false otherwise
 */
//bool BinaryIntAutomaton::getConstants(std::vector<int>& constants) {
//  std::map<int, int> disc;
//  std::map<int, int> low;
//  std::map<int, bool> is_stack_member;
//  std::vector<int> st;
//  std::vector<bool> path;
//  int time = 0;
//  bool result = false;
//  int sink_state = getSinkState();
//
//  if (sink_state == this->dfa->s) {
//    return false;
//  }
//
//  disc[sink_state] = 0; // avoid exploring sink state
//  is_stack_member[sink_state] = false; // avoid looping to sink state
//
//  result = getConstants(this->dfa->s, disc, low, st, is_stack_member, path, constants, time);
//  DVLOG(VLOG_LEVEL) << result << " = [" << this->id << "]->getConstants(<constants>)";
//  return result;
//}
//
//bool BinaryIntAutomaton::getConstants(int state, std::map<int, int>& disc, std::map<int, int>& low, std::vector<int>& st,
//        std::map<int, bool>& is_stack_member, std::vector<bool>& path, std::vector<int>& constants, int& time) {
//
//  int next_state = 0;
//  std::vector<char> exception = {'0'};
//  int l, r;
//
////  std::cout << "visiting state: " << state << std::endl;
//  disc[state] = low[state] = time; time++;
//  st.push_back(state);
//  is_stack_member[state] = true;
//
//  l = getNextState(state, exception);
//  exception[0] = '1';
//  r = getNextState(state, exception);
//  bool is_cyclic = true; // TODO figure out that
//
//  for (int b = 0; b < 2; b++) {
//    next_state = (b == 0) ? l : r;
////    std::cout << "next state: " << next_state << std::endl;
//    if (disc.find(next_state) == disc.end()) {
//      path.push_back( b == 1);
//      is_cyclic = getConstants(next_state, disc, low, st, is_stack_member, path, constants, time);
//      low[state] = std::min(low[state], low[next_state]);
//      path.pop_back();
//    } else if (is_stack_member[next_state]) {
//      low[state] = std::min(low[state], disc[next_state]);
//    }
//
//  }
//
//  bool is_in_cycle = false;
//  if (low[state] == disc[state]) { // head of SCC
//    int current_state = st.back();
//    while (current_state != state) {
//      st.pop_back();
//      is_stack_member[current_state] = false;
//      current_state = st.back();
//      is_in_cycle = true;
//    }
//    is_stack_member[current_state] = false;
//    st.pop_back();
//
//    if (current_state == l or current_state == r) {
//      is_in_cycle = true;
//    }
//
//    if ((not is_in_cycle) and isAcceptingState(current_state)) {
//
//      unsigned c = 0;
//      for (unsigned i = 0; i < path.size(); i++) {
//        if (path[i]) {
//          c += (1 << i);
//        }
//      }
//      constants.push_back(c);
//    }
//  }
//
//  return is_in_cycle;
//}
void BinaryIntAutomaton::GetBaseConstants(std::vector<int>& constants, unsigned max_number_of_bit_limit) {
  unsigned char *is_visited = new unsigned char[this->dfa_->ns];
  std::vector<bool> path;

  for (int i = 0; i < this->dfa_->ns; i++) {
    is_visited[i] = false;
  }

  if (not IsSinkState(this->dfa_->s)) {
    GetBaseConstants(this->dfa_->s, is_visited, path, constants, max_number_of_bit_limit);
  }

  delete[] is_visited;

  DVLOG(VLOG_LEVEL) << "<void> = [" << this->id_ << "]->getBaseConstants(<base constants>)";

  return;
}

/**
 * @param is_visited to keep track of visited transition; 1st is for '0' transition, 2nd bit is for '1' transition
 * @returns populated constants, ignores the value of initial state whether is an accepted or not
 */
void BinaryIntAutomaton::GetBaseConstants(int state, unsigned char *is_visited, std::vector<bool>& path,
                                          std::vector<int>& constants, unsigned max_number_of_bit_limit) {
  int next_state = 0;
  std::vector<char> exception = { '0' };

  if (path.size() > max_number_of_bit_limit) {  // limit samples to integer length for now
    return;
  }

  if (IsAcceptingState(state)) {
    unsigned c = 0;
    for (unsigned i = 0; i < path.size(); i++) {
      if (path[i]) {
        c += (1 << i);
      }
    }
    constants.push_back(c);
  }

  next_state = getNextState(state, exception);  // taking transition 0

  if ((is_visited[state] & 1) == 0 and (not IsSinkState(next_state))) {
    is_visited[state] |= 1;
    path.push_back(false);
    GetBaseConstants(next_state, is_visited, path, constants, max_number_of_bit_limit);
    path.pop_back();
    is_visited[state] &= 2;
  }

  exception[0] = '1';
  next_state = getNextState(state, exception);  // taking transition 1

  if ((is_visited[state] & 2) == 0 and (not IsSinkState(next_state))) {
    is_visited[state] |= 2;
    path.push_back(true);
    GetBaseConstants(next_state, is_visited, path, constants, max_number_of_bit_limit);
    path.pop_back();
    is_visited[state] &= 1;
  }
}

//void BinaryIntAutomaton::getBaseConstants2(std::vector<int>& constants) {
//  bool *is_stack_member = new bool[this->dfa->ns];
//  std::vector<bool> path;
//
//  for (int i = 0; i < this->dfa->ns; i++) {
//    is_stack_member[i] = false;
//  }
//
//  if (not isSinkState(this->dfa->s)) {
//    getBaseConstants(this->dfa->s, is_stack_member, path, constants);
//  }
//
//  delete[] is_stack_member;
//
//  DVLOG(VLOG_LEVEL) << "<void> = [" << this->id << "]->getBaseConstants(<base constants>)";
//
//  return;
//}
//
///**
// * @returns populated constants, ignores the value of initial state whether is an accepted or not
// */
//void BinaryIntAutomaton::getBaseConstants(int state, bool *is_stack_member, std::vector<bool>& path, std::vector<int>& constants) {
//  int next_state = 0;
//  std::vector<char> exception = {'0'};
//  int l, r;
//
//  is_stack_member[state] = true;
//
//  if (path.size() > 31) { // limit samples to integer length for now
//    return;
//  }
//
//  l = getNextState(state, exception);
//  exception[0] = '1';
//  r = getNextState(state, exception);
//
//  // this case cannot happen in state other than sink (automaton does not have leading zeros)
//  if (state == l and state == r) {
//    LOG(FATAL)<< "Automaton cannot have leading zeros at this point, please debug the bug";
//  }
//
//  for (int b = 0; b < 2; b++) {
//    next_state = (b == 0) ? l : r;
//    // take simple paths
//    if ( (not is_stack_member[next_state]) and (not isSinkState(next_state)) ) {
//      path.push_back( b == 1);
//
//      if (isAcceptingState(next_state)) {
//        unsigned c = 0;
//        for (unsigned i = 0; i < path.size(); i++) {
//          if (path[i]) {
//            c += (1 << i);
//          }
//        }
//        constants.push_back(c);
//      }
//
//      getBaseConstants(next_state, is_stack_member, path, constants);
//      path.pop_back();
//    }
//  }
//  is_stack_member[state] = false;
//}

void BinaryIntAutomaton::add_print_label(std::ostream& out) {
  out << " subgraph cluster_0 {\n";
  out << "  style = invis;\n  center = true;\n  margin = 0;\n";
  out << "  node[shape=plaintext];\n";
  out << " \"\"[label=\"";
  for (auto& el : formula_->GetVariableCoefficientMap()) {
    out << el.first << "\n";
  }
  out << "\"]\n";
  out << " }";
}

} /* namespace Theory */
} /* namespace Vlab */
