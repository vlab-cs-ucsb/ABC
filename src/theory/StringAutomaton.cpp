/*
 * StringAutomaton.cpp
 *
 *  Created on: Aug 14, 2017
 *      Author: Baki,Will
 */

#include "StringAutomaton.h"

namespace Vlab {
namespace Theory {

const int StringAutomaton::VLOG_LEVEL = 8;
bool StringAutomaton::debug = false;

StringAutomaton::TransitionTable StringAutomaton::TRANSITION_TABLE;

StringAutomaton::StringAutomaton(const DFA_ptr dfa, const int number_of_bdd_variables)
		:	Automaton(Automaton::Type::MULTITRACK, dfa, number_of_bdd_variables),
			num_tracks_(number_of_bdd_variables > DEFAULT_NUM_OF_VARIABLES ? number_of_bdd_variables / VAR_PER_TRACK : 1),
			formula_(new StringFormula()) {

}

StringAutomaton::StringAutomaton(const DFA_ptr dfa, const int number_of_tracks, const int number_of_bdd_variables)
		:	Automaton(Automaton::Type::MULTITRACK, dfa, number_of_bdd_variables),
			num_tracks_(number_of_tracks),
			formula_(new StringFormula()) {

}

StringAutomaton::StringAutomaton(const DFA_ptr dfa, const int i_track, const int number_of_tracks, const int in_num_vars)
		:	Automaton(Automaton::Type::MULTITRACK, nullptr, number_of_tracks * VAR_PER_TRACK),
			num_tracks_(number_of_tracks),
			formula_(new StringFormula()) {
	DFA_ptr M = dfa, temp = nullptr, result = nullptr;
	trace_descr tp;
	paths state_paths, pp;
	std::vector<std::pair<std::vector<char>,int>> state_exeps;
	int sink;
	char* statuses;
	int* mindices;
	bool has_sink = true;
	int num_states = M->ns+1; // lambda state
	int lambda_state = num_states-1;
	int var = VAR_PER_TRACK;
	int len = (num_tracks_ * var)+1; // extrabit for nondeterminism
	mindices = GetBddVariableIndices(len);
	int *indices = GetBddVariableIndices(in_num_vars);
	sink = find_sink(M);
	if(sink < 0) {
		has_sink = false;
		sink = num_states;
		num_states++;
	}
	statuses = new char[num_states+1];
	// begin dfa building process
	// old transitions end in '0'
	// new transitions end in '1' (lambda transitions)

	dfaSetup(num_states, len, mindices);
	for(unsigned i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);

		// if state is final, add lambda transition to lambda state
		if(M->f[i] == 1) {
			std::vector<char> curr(len,'X');
			for(int k = 0; k < var; k++) {
				curr[i_track+num_tracks_*k] = '1';
			}
			curr[len-1] = '1'; // new transition, end with '1'
			curr.push_back('\0');
			state_exeps.push_back(std::make_pair(curr,lambda_state));
		}

		while(pp) {
			if(pp->to != sink) {
				std::vector<char> curr(len,'X');
				for(unsigned j = 0; j < in_num_vars; j++) {
					for(tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
					if(tp) {
						if(tp->value) curr[i_track+num_tracks_*j] = '1';
						else curr[i_track+num_tracks_*j] = '0';
					}
					else
						curr[i_track+num_tracks_*j] = 'X';
				}
				// if default_num_Var, make default_num_var+1 index '0' for non-lambda
				if(in_num_vars == DEFAULT_NUM_OF_VARIABLES) {
					curr[i_track+num_tracks_*(DEFAULT_NUM_OF_VARIABLES)] = '0';
				}
				curr[len-1] = '0'; // old transition, end with '0'
				curr.push_back('\0');
				state_exeps.push_back(std::make_pair(curr,pp->to));
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		dfaAllocExceptions(state_exeps.size());
		for(unsigned k = 0; k < state_exeps.size(); ++k) {
			dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
		}
		dfaStoreState(sink);
		state_exeps.clear();

		statuses[i] = '-';
	}
	// lambda state, loop de loop
	dfaAllocExceptions(1);
	std::vector<char> str(len,'X');
	for(int i = 0; i < var; i++) {
		str[i_track+num_tracks_*i] = '1';
	}
	str[len-1] = '1';
	str.push_back('\0');
	dfaStoreException(lambda_state,&str[0]);
	dfaStoreState(sink);
	statuses[lambda_state] = '+';
	// extra sink state, if needed
	if(!has_sink) {
		dfaAllocExceptions(0);
		dfaStoreState(sink);
		statuses[sink] = '-';
	}
	statuses[num_states] = '\0';
	result = dfaBuild(statuses);
	temp = dfaMinimize(result);
	dfaFree(result);
	// project away the extra bit
	result = dfaProject(temp,len-1);
	dfaFree(temp);
	temp = dfaMinimize(result);
	dfaFree(result);
	result = temp;

	delete[] statuses;
	this->dfa_ = result;
}

// TODO: Find better solution for figuring out num_tracks_
StringAutomaton::StringAutomaton(const DFA_ptr dfa, StringFormula_ptr formula, const int number_of_bdd_variables)
		:	Automaton(Automaton::Type::MULTITRACK, dfa, number_of_bdd_variables) {
	if(formula == nullptr) {
		LOG(FATAL) << "formula is nullptr!";
	}
	if(formula->GetNumberOfVariables() > 0) {
		this->num_tracks_ = formula->GetNumberOfVariables();
	} else {
		if(number_of_bdd_variables >= VAR_PER_TRACK) {
			this->num_tracks_ = number_of_bdd_variables/VAR_PER_TRACK;
		} else {
			this->num_tracks_ = 1;
		}
	}
	formula_ = formula;
}

StringAutomaton::StringAutomaton(const StringAutomaton& other)
		:	Automaton(other) {
	this->num_tracks_ = other.num_tracks_;
	if(other.formula_ != nullptr) {
		this->formula_ = other.formula_->clone();
	}
}

StringAutomaton::~StringAutomaton() {
	LOG(INFO) << "DELETING: " << id_;
	delete formula_;
}

StringAutomaton_ptr StringAutomaton::clone() const {
  StringAutomaton_ptr result_auto = new StringAutomaton(*this);
  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->clone()";
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakePhi(const int number_of_bdd_variables) {
  DFA_ptr non_accepting_string_dfa = Automaton::DFAMakePhi(number_of_bdd_variables);
  StringAutomaton_ptr non_accepting_string_auto = new StringAutomaton(non_accepting_string_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << non_accepting_string_auto->id_ << " = MakePhi(" << number_of_bdd_variables << ")";
  return non_accepting_string_auto;
}

StringAutomaton_ptr StringAutomaton::MakePhi(StringFormula_ptr formula) {
	int num_variables = formula->GetNumberOfVariables();
	int total_num_variables = 0;
	if(num_variables == 1) {
		total_num_variables = Theory::StringAutomaton::DEFAULT_NUM_OF_VARIABLES;
	} else if(num_variables > 1) {
		total_num_variables = num_variables * Theory::StringAutomaton::VAR_PER_TRACK;
	} else {
		LOG(FATAL) << "Can't make automaton with no bdd variables...";
	}
	DFA_ptr non_accepting_string_dfa = Automaton::DFAMakePhi(total_num_variables);
	StringAutomaton_ptr non_accepting_string_auto = new StringAutomaton(non_accepting_string_dfa, formula, total_num_variables);
	DVLOG(VLOG_LEVEL) << non_accepting_string_auto->id_ << " = MakePhi(" << total_num_variables << ")";
	return non_accepting_string_auto;
}

StringAutomaton_ptr StringAutomaton::MakeEmptyString(const int number_of_bdd_variables) {
  DFA_ptr empty_string_dfa = Automaton::DFAMakeEmpty(number_of_bdd_variables);
  StringAutomaton_ptr empty_string_auto = new StringAutomaton(empty_string_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << empty_string_auto->id_ << " = MakeEmptyString(" << number_of_bdd_variables << ")";
  return empty_string_auto;
}

StringAutomaton_ptr StringAutomaton::MakeString(const std::string str, const int number_of_bdd_variables) {
  if (str.empty()) {
    return StringAutomaton::MakeEmptyString();
  }

  const int str_length = str.length();
  const int number_of_states = str_length + 2;
  char* statuses = new char[number_of_states];

  dfaSetup(number_of_states, number_of_bdd_variables, GetBddVariableIndices(number_of_bdd_variables));

  for (int i = 0; i < str_length; i++) {
    dfaAllocExceptions(1);
    dfaStoreException(i + 1, const_cast<char*>(GetBinaryStringMSB((unsigned long) str[i], number_of_bdd_variables).data()));
    dfaStoreState(str_length + 1);
    statuses[i] = '-';
  }

  dfaAllocExceptions(0);
  dfaStoreState(str_length + 1);
  statuses[str_length] = '+';

  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(str_length + 1);
  statuses[str_length + 1] = '-';

  DFA_ptr temp_dfa = dfaBuild(statuses);
  DFA_ptr result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  StringAutomaton_ptr result_auto = new StringAutomaton(result_dfa, number_of_bdd_variables);
  delete[] statuses;

  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = MakeString(\"" << str << "\")";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyString(const int number_of_bdd_variables) {
  //char statuses[2] { '+', '\0' };
  int *variable_indices = GetBddVariableIndices(number_of_bdd_variables);
  dfaSetup(1, number_of_bdd_variables, variable_indices);
  dfaAllocExceptions(0);
  dfaStoreState(0);
  DFA_ptr any_string_dfa = dfaBuild("+");
  StringAutomaton_ptr any_string = new StringAutomaton(any_string_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << any_string->id_ << " = MakeAnyString()";
  return any_string;
}

StringAutomaton_ptr StringAutomaton::MakeAnyOtherString(const std::string str, const int num_of_variables) {
  StringAutomaton_ptr str_auto = MakeString(str);
  StringAutomaton_ptr not_contains_me_auto = str_auto->GetAnyStringNotContainsMe();
  delete str_auto; str_auto = nullptr;
  DVLOG(VLOG_LEVEL) << not_contains_me_auto->id_ << " = StringAutomaton::MakeAnyOtherString(" << str << ")";
  return not_contains_me_auto;
}

StringAutomaton_ptr StringAutomaton::MakeCharRange(const char from, const char to, const int number_of_bdd_variables) {
  unsigned long from_char = (unsigned long) from;
  unsigned long to_char = (unsigned long) to;
  if (from_char > to_char) {
    std::swap(from_char, to_char);
  }

  char statuses[3] { '-', '+', '-' };
  int* variable_indices = GetBddVariableIndices(number_of_bdd_variables);

  dfaSetup(3, number_of_bdd_variables, variable_indices);

  int initial_state = to_char - from_char;

  //state 0
  dfaAllocExceptions(initial_state + 1);
  for (unsigned long index = from_char; index <= to_char; index++) {
    std::vector<char> v = GetBinaryFormat(index,number_of_bdd_variables);
    dfaStoreException(1, const_cast<char*>(GetBinaryStringMSB(index, number_of_bdd_variables).data()));
  }
  dfaStoreState(2);

  //state 1
  dfaAllocExceptions(0);
  dfaStoreState(2);

  //state 2
  dfaAllocExceptions(0);
  dfaStoreState(2);

  DFA_ptr range_dfa = dfaBuild(statuses);
  StringAutomaton_ptr range_auto = new StringAutomaton(range_dfa, number_of_bdd_variables);

  DVLOG(VLOG_LEVEL) << range_auto->id_ << " = MakeCharRange('" << from << "', '" << to << "')";

  return range_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyChar(const int number_of_bdd_variables) {
  StringAutomaton_ptr any_char_auto = StringAutomaton::MakeAnyStringLengthEqualTo(1, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << any_char_auto->id_ << " = MakeAnyChar()";
  return any_char_auto;
}

StringAutomaton_ptr StringAutomaton::MakeRegexAuto(const std::string regex, const int number_of_bdd_variables) {
  Util::RegularExpression regular_expression (regex);
  StringAutomaton_ptr regex_auto = StringAutomaton::MakeRegexAuto(&regular_expression, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << regex_auto->id_ << " = MakeRegexAuto(" << regex << ")";

  return regex_auto;
}

StringAutomaton_ptr StringAutomaton::MakeRegexAuto(Util::RegularExpression_ptr regular_expression, const int number_of_bdd_variables) {
  StringAutomaton_ptr regex_auto = nullptr;
  StringAutomaton_ptr regex_expr1_auto = nullptr;
  StringAutomaton_ptr regex_expr2_auto = nullptr;

  switch (regular_expression->type()) {
  case Util::RegularExpression::Type::UNION:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_expr2_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr2(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Union(regex_expr2_auto);
    delete regex_expr1_auto;
    delete regex_expr2_auto;
    break;
  case Util::RegularExpression::Type::CONCATENATION:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_expr2_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr2(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Concat(regex_expr2_auto);
    delete regex_expr1_auto;
    delete regex_expr2_auto;
    break;
  case Util::RegularExpression::Type::INTERSECTION:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_expr2_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr2(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Intersect(regex_expr2_auto);
    delete regex_expr1_auto;
    delete regex_expr2_auto;
    break;
  case Util::RegularExpression::Type::OPTIONAL:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Optional();
    delete regex_expr1_auto;
    break;
  case Util::RegularExpression::Type::REPEAT_STAR:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->KleeneClosure();
    delete regex_expr1_auto;
    break;
  case Util::RegularExpression::Type::REPEAT_PLUS:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Closure();
    delete regex_expr1_auto;
    break;
  case Util::RegularExpression::Type::REPEAT_MIN:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Repeat(regular_expression->get_min());
    delete regex_expr1_auto;
    break;
  case Util::RegularExpression::Type::REPEAT_MINMAX:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Repeat(regular_expression->get_min(), regular_expression->get_max());
    delete regex_expr1_auto;
    break;
  case Util::RegularExpression::Type::COMPLEMENT:
    regex_expr1_auto = StringAutomaton::MakeRegexAuto(regular_expression->get_expr1(), number_of_bdd_variables);
    regex_auto = regex_expr1_auto->Complement();
    delete regex_expr1_auto;
    break;
  case Util::RegularExpression::Type::CHAR:
    regex_auto = StringAutomaton::MakeString(std::string(1, regular_expression->get_character()), number_of_bdd_variables);
    break;
  case Util::RegularExpression::Type::CHAR_RANGE:
    regex_auto = StringAutomaton::MakeCharRange(regular_expression->get_from_character(), regular_expression->get_to_character(), number_of_bdd_variables);
    break;
  case Util::RegularExpression::Type::ANYCHAR:
    regex_auto = StringAutomaton::MakeAnyChar(number_of_bdd_variables);
    break;
  case Util::RegularExpression::Type::EMPTY:
    regex_auto = StringAutomaton::MakePhi(number_of_bdd_variables);
    break;
  case Util::RegularExpression::Type::STRING:
    regex_auto = StringAutomaton::MakeString(regular_expression->get_string(), number_of_bdd_variables);
    break;
  case Util::RegularExpression::Type::ANYSTRING:
    regex_auto = StringAutomaton::MakeAnyString(number_of_bdd_variables);
    break;
  case Util::RegularExpression::Type::AUTOMATON:
    LOG(FATAL)<< "Unsupported regular expression" << *regular_expression;
    break;
  case Util::RegularExpression::Type::INTERVAL:
    LOG(FATAL) << "Unsupported regular expression" << *regular_expression;
    break;
  default:
    LOG(FATAL) << "Unsupported regular expression" << *regular_expression;
    break;
  }

  return regex_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringLengthEqualTo(const int length, const int number_of_bdd_variables) {
  DFA_ptr length_dfa = Automaton::DFAMakeAcceptingAnyWithInRange(length, length, number_of_bdd_variables);
  StringAutomaton_ptr length_auto = new StringAutomaton(length_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << length_auto->id_ << " = MakeAnyStringLengthEqualTo(" << length <<  ")";
  return length_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringLengthLessThan(const int length, const int number_of_bdd_variables){
  DFA_ptr length_dfa = Automaton::DFAMakeAcceptingAnyWithInRange(0, length-1, number_of_bdd_variables);
  StringAutomaton_ptr length_auto = new StringAutomaton(length_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << length_auto->id_ << " = MakeAnyStringLengthLessThan(" << length <<  ")";
  return length_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringLengthLessThanOrEqualTo(const int length, const int number_of_bdd_variables){
  DFA_ptr length_dfa = Automaton::DFAMakeAcceptingAnyWithInRange(0, length, number_of_bdd_variables);
  StringAutomaton_ptr length_auto = new StringAutomaton(length_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << length_auto->id_ << " = MakeAnyStringLengthLessThanOrEqualTo(" << length <<  ")";
  return length_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringLengthGreaterThan(const int length, const int number_of_bdd_variables) {
  DFA_ptr length_dfa = Automaton::DFAMakeAcceptingAnyAfterLength(length + 1, number_of_bdd_variables);
  StringAutomaton_ptr length_auto = new StringAutomaton(length_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << length_auto->id_ << " = MakeAnyStringLengthGreaterThan(" << length <<  ")";
  return length_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringLengthGreaterThanOrEqualTo(const int length, const int number_of_bdd_variables) {
  DFA_ptr length_dfa = Automaton::DFAMakeAcceptingAnyAfterLength(length, number_of_bdd_variables);
  StringAutomaton_ptr length_auto = new StringAutomaton(length_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << length_auto->id_ << " = MakeAnyStringLengthGreaterThanOrEqualTo(" << length <<  ")";
  return length_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringWithLengthInRange(const int start, const int end, const int number_of_bdd_variables) {
  DFA_ptr length_dfa = Automaton::DFAMakeAcceptingAnyWithInRange(start, end, number_of_bdd_variables);
  StringAutomaton_ptr length_auto = new StringAutomaton(length_dfa, number_of_bdd_variables);
  DVLOG(VLOG_LEVEL) << length_auto->id_ << " = MakeAnyStringWithLengthInRange(" << start << "," << end <<  ")";
  return length_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAutomaton(DFA_ptr dfa, Formula_ptr formula, const int number_of_variables) {
	auto string_formula = dynamic_cast<StringFormula_ptr>(formula);
	if(string_formula == nullptr) {
		LOG(FATAL) << "NOT STRING FORMULA";
	}
	return new StringAutomaton(dfa, string_formula, number_of_variables);
}

StringAutomaton_ptr StringAutomaton::MakeAutomaton(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr;

	switch(formula->GetType()) {
		case StringFormula::Type::EQ:
    case StringFormula::Type::EQ_CHARAT:
			result_auto = StringAutomaton::MakeEquality(formula);
			break;
		case StringFormula::Type::NOTEQ:
    case StringFormula::Type::NOTEQ_CHARAT:
			result_auto = StringAutomaton::MakeNotEquality(formula);
			break;
		case StringFormula::Type::GT:
		case StringFormula::Type::GT_CHARAT:
			result_auto = StringAutomaton::MakeGreaterThan(formula);
			break;
		case StringFormula::Type::GE:
		case StringFormula::Type::GE_CHARAT:
			result_auto = StringAutomaton::MakeGreaterThanOrEqual(formula);
			break;
		case StringFormula::Type::LT:
		case StringFormula::Type::LT_CHARAT:
			result_auto = StringAutomaton::MakeLessThan(formula);
			break;
		case StringFormula::Type::LE:
		case StringFormula::Type::LE_CHARAT:
			result_auto = StringAutomaton::MakeLessThanOrEqual(formula);
			break;
		case StringFormula::Type::BEGINS:
			result_auto = StringAutomaton::MakeBegins(formula);
			break;
		case StringFormula::Type::NOTBEGINS:
			result_auto = StringAutomaton::MakeNotBegins(formula);
			break;
		default:
			LOG(FATAL) << "StringFormula type not supported";
			break;
	}
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeBegins(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr;
	DFA_ptr temp_dfa, result_dfa;
	int num_tracks = formula->GetNumberOfVariables(),
			left_track,right_track;
	std::string left_data,right_data;
	TransitionVector tv;

	left_track = formula->GetVariableIndex(1);
	right_track = formula->GetVariableIndex(2);

	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = Automaton::GetBddVariableIndices(num_tracks*var);

	std::vector<char> exep_lambda(var,'1');
	tv = GenerateTransitionsForRelation(StringFormula::Type::EQ,var);
	dfaSetup(4,len,mindices);
	dfaAllocExceptions(2*tv.size() + 1); // 1 extra for lambda stuff below
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for(int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = tv[i].second[k];
		}
		str.push_back('\0');
		dfaStoreException(0,&str[0]);
	}

	// if right is lambda, left can be anything, but go to next state
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		str.push_back('\0');
		dfaStoreException(1,&str[0]);
	}

	// if both are lambda, go to next state
	std::vector<char> str(len,'X');
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(2,&str[0]);
	dfaStoreState(3);

	// left anything, right lambda, loop back here
	dfaAllocExceptions(tv.size()+1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		str.push_back('\0');
		dfaStoreException(1,&str[0]);
	}
	// if both lambda, goto 2
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(2,&str[0]);
	dfaStoreState(3);

	// lambda/lambda state, loop back on lambda
	dfaAllocExceptions(1);
	dfaStoreException(2,&str[0]);
	dfaStoreState(3);

	// sink
	dfaAllocExceptions(0);
	dfaStoreState(3);

	temp_dfa = dfaBuild("--+-");
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	result_auto = new StringAutomaton(result_dfa,formula,var*num_tracks);
	DVLOG(VLOG_LEVEL) << result_auto->id_ << " = MakeBegins(" << formula->str() << ")";
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeNotBegins(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr;
	DFA_ptr temp_dfa, result_dfa;
	int num_tracks = formula->GetNumberOfVariables(),
			left_track,right_track;
	std::string left_data,right_data;
	TransitionVector tv;

	left_track = formula->GetVariableIndex(1);
	right_track = formula->GetVariableIndex(2);

	int eq_eq = 0, lambda_star = 1, not_eq_eq = 2,
			lambda_lambda = 3, star_lambda = 4, sink = 5;
	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = Automaton::GetBddVariableIndices(num_tracks*var);
	std::vector<char> exep_lambda(var,'1');
	tv = GenerateTransitionsForRelation(StringFormula::Type::EQ,var);

	dfaSetup(6,len,mindices);
	// ------init/eq_eq state
	// if both the same, and not lambda, loop back
	dfaAllocExceptions(3*tv.size() + 1); // 1 extra for lambda stuff below
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for(int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = tv[i].second[k];
		}
		str.push_back('\0');
		dfaStoreException(eq_eq,&str[0]);
	}

	// if left is lambda, right can be anything, but go to lambda_star
	// but if right is lambda, goto sink
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep_lambda[k];
			str[right_track+num_tracks*k] = tv[i].first[k];
		}
		str.push_back('\0');
		dfaStoreException(lambda_star,&str[0]);

		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		dfaStoreException(sink,&str[0]);
	}

	// if both are lambda, go to sink
	std::vector<char> str(len,'X');
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(sink,&str[0]);
	// otherwise, go to not_eq_eq
	dfaStoreState(not_eq_eq);


	// ------ lambda_star state
	// left lambda, right star, loop back here
	dfaAllocExceptions(tv.size() + 1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep_lambda[k];
			str[right_track+num_tracks*k] = tv[i].first[k];
		}
		str.push_back('\0');
		dfaStoreException(lambda_star,&str[0]);
	}
	// if both lambda, goto lambda_lambda
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(lambda_lambda,&str[0]);
	// otherwise, goto sink
	dfaStoreState(sink);



	// ------ not_eq_eq state
	// on lambda_star goto lambda_star,
	// star_lambda goto star_lambda,
	// lambda_lambda goto lambda,
	// else loop back
	dfaAllocExceptions(tv.size()*2 + 1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep_lambda[k];
			str[right_track+num_tracks*k] = tv[i].first[k];
		}
		str.push_back('\0');
		dfaStoreException(lambda_star,&str[0]);

		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		dfaStoreException(star_lambda,&str[0]);
	}
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(not_eq_eq);




	// ------ lambda/lambda state, loop back on lambda
	dfaAllocExceptions(1);
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(sink);




	// ------ star/lambda state
	// loop back on star/lambda, goto lambda_lambda on lambda/lambda
	// if right is lambda, left can be anything, but go to next state
	dfaAllocExceptions(tv.size() + 1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		str.push_back('\0');
		dfaStoreException(star_lambda,&str[0]);
	}

	// if both are lambda, go to next state
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(sink);

	// sink
	dfaAllocExceptions(0);
	dfaStoreState(sink);

	temp_dfa = dfaBuild("---+--");
	result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	result_auto = new StringAutomaton(result_dfa,formula,var*num_tracks);
	DVLOG(VLOG_LEVEL) << result_auto->id_ << " = MakeNotBegins(" << formula->str() << ")";
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeEquality(StringFormula_ptr formula) {

  StringAutomaton_ptr equality_auto = nullptr;

  auto coeff_map = formula->GetVariableCoefficientMap();
	int num_vars = 0;
	for(auto it : coeff_map) {
		if(it.second != 0) {
			num_vars++;
		}
	}

	if(num_vars == 1) {
		int num_tracks = formula->GetNumberOfVariables();
		int left_track = formula->GetVariableIndex(1);
		StringAutomaton_ptr string_auto;
		string_auto = StringAutomaton::MakeRegexAuto(formula->GetConstant());

		formula->SetConstant("");
		if(num_tracks == 1) {
			equality_auto = new StringAutomaton(dfaCopy(string_auto->getDFA()),num_tracks,DEFAULT_NUM_OF_VARIABLES);
		} else {
			equality_auto = new StringAutomaton(string_auto->getDFA(),left_track,num_tracks,DEFAULT_NUM_OF_VARIABLES);
		}
		equality_auto->SetFormula(formula);
		delete string_auto;
		return equality_auto;
	}

	int num_tracks = formula->GetNumberOfVariables();
	int left_track = formula->GetVariableIndex(1); // variable on the left of equality
	int right_track = formula->GetVariableIndex(2); // variable on the right of equality


	if(formula->GetType() == StringFormula::Type::EQ_CHARAT) {
		// if charAt() == charAt() and constants are the same (such as charAt(X,0) == charAt(Y,0))
		auto equality_dfa = StringAutomaton::MakeRelationalCharAtDfa(formula,VAR_PER_TRACK,num_tracks,left_track,right_track);
		equality_auto = new StringAutomaton(equality_dfa,formula,num_tracks*VAR_PER_TRACK);
	} else if(formula->GetConstant() != "") {
		// if string is not empty, eq is of form X = Y.c
    int temp_left = num_tracks;
    int temp_right = right_track;
    int temp_num_tracks = num_tracks+1;

    StringAutomaton_ptr concat_auto = StringAutomaton::MakeConcatExtraTrack(temp_left,temp_right,temp_num_tracks,formula->GetConstant());
    DFA_ptr eq_dfa = StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type::EQ, VAR_PER_TRACK, num_tracks+1, left_track, temp_left);
    StringAutomaton_ptr eq_auto = new StringAutomaton(eq_dfa,num_tracks+1,(num_tracks+1)*VAR_PER_TRACK);
    auto temp_auto = concat_auto->Intersect(eq_auto);
    delete eq_auto;
    delete concat_auto;
    equality_auto = temp_auto->ProjectKTrack(num_tracks);
    delete temp_auto;
    equality_auto->SetFormula(formula);
  } else {
    auto equality_dfa = MakeBinaryRelationDfa(StringFormula::Type::EQ, VAR_PER_TRACK, num_tracks, left_track, right_track);
    equality_auto = new StringAutomaton(equality_dfa,formula,num_tracks*VAR_PER_TRACK);
  }

	DVLOG(VLOG_LEVEL) << equality_auto->id_ << " = MakeEquality(" << formula->str() << ")";
	return equality_auto;
}

StringAutomaton_ptr StringAutomaton::MakeNotEquality(	StringFormula_ptr formula) {
	StringAutomaton_ptr not_equality_auto = nullptr;

	auto coeff_map = formula->GetVariableCoefficientMap();
	int num_vars = 0;
	for(auto it : coeff_map) {
		if(it.second != 0) {
			num_vars++;
		}
	}

	if(num_vars == 1) {
		int num_tracks = formula->GetNumberOfVariables();
		int left_track = formula->GetVariableIndex(1);
		StringAutomaton_ptr string_auto,complement_auto;
		if(formula->GetConstant() == "") {
			complement_auto = StringAutomaton::MakeAnyStringLengthGreaterThan(0);
		} else {
			auto t1 = StringAutomaton::MakeAnyString();
			auto t2 = StringAutomaton::MakeString(formula->GetConstant());
			complement_auto = t1->Difference(t2);
			delete t1;
			delete t2;
		}

		formula->SetConstant("");
		if(num_tracks == 1) {
			not_equality_auto = new StringAutomaton(dfaCopy(complement_auto->getDFA()),num_tracks,DEFAULT_NUM_OF_VARIABLES);
		} else {
			not_equality_auto = new StringAutomaton(complement_auto->getDFA(),left_track,num_tracks,DEFAULT_NUM_OF_VARIABLES);
		}
		not_equality_auto->SetFormula(formula);
		delete complement_auto;
		return not_equality_auto;
	}

  int num_tracks = formula->GetNumberOfVariables();
  int left_track = formula->GetVariableIndex(1); // variable on the left of equality
	int right_track = formula->GetVariableIndex(2); // variable on the right of equality


	if(formula->GetType() == StringFormula::Type::NOTEQ_CHARAT) {
		// if charAt() == charAt() and constants are the same (such as charAt(X,0) == charAt(Y,0))
		auto not_equality_dfa = StringAutomaton::MakeRelationalCharAtDfa(formula,VAR_PER_TRACK,num_tracks,left_track,right_track);
		not_equality_auto = new StringAutomaton(not_equality_dfa,formula,num_tracks*VAR_PER_TRACK);
	} else if(formula->GetConstant() != "") {
		// if string is not empty, eq is of form X = Y.c
    int temp_left = num_tracks;
    int temp_right = right_track;
    int temp_num_tracks = num_tracks+1;

    StringAutomaton_ptr concat_auto = StringAutomaton::MakeConcatExtraTrack(temp_left,temp_right,temp_num_tracks,formula->GetConstant());
    DFA_ptr eq_dfa = StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type::NOTEQ, VAR_PER_TRACK, num_tracks+1, left_track, temp_left);
    StringAutomaton_ptr eq_auto = new StringAutomaton(eq_dfa,num_tracks+1,(num_tracks+1)*VAR_PER_TRACK);
    auto temp_auto = concat_auto->Intersect(eq_auto);
    delete eq_auto;
    delete concat_auto;
    not_equality_auto = temp_auto->ProjectKTrack(num_tracks);
    delete temp_auto;
    not_equality_auto->SetFormula(formula);
  } else {
    auto not_equality_dfa = MakeBinaryRelationDfa(StringFormula::Type::NOTEQ, VAR_PER_TRACK, num_tracks, left_track, right_track);
    not_equality_auto = new StringAutomaton(not_equality_dfa,formula,num_tracks*VAR_PER_TRACK);
  }

  DVLOG(VLOG_LEVEL) << not_equality_auto->id_ << " = MakeNotEquality(" << formula->str() << ")";
  return not_equality_auto;
}

StringAutomaton_ptr StringAutomaton::MakeLessThan(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr constant_string_auto = nullptr;
	DFA_ptr temp_dfa = nullptr, result_dfa = nullptr, temp2_dfa = nullptr;
	std::map<std::string,int> trackmap = formula->GetVariableCoefficientMap();

	auto coeff_map = formula->GetVariableCoefficientMap();
	int num_tracks = formula->GetNumberOfVariables();
	int left_track = -1, right_track = -1;
	int num_vars = 0;
	for(auto it : coeff_map) {
		if(it.second != 0) {
			num_vars++;
		}
	}

	if(num_vars == 1) {
		std::string var_name = formula->GetVariableAtIndex(0);
		int var_coeff = formula->GetVariableCoefficient(var_name);
		if(var_coeff == 1) {
			// var on left
			left_track = formula->GetVariableIndex(var_coeff);
			right_track = num_tracks;
		} else {
			// var on right
			left_track = num_tracks;
			right_track = formula->GetVariableIndex(var_coeff);
		}
		constant_string_auto = StringAutomaton::MakeString(formula->GetConstant());
		num_tracks++;
	} else {
		left_track = formula->GetVariableIndex(1);
		right_track = formula->GetVariableIndex(2);
	}


	if(formula->GetType() == StringFormula::Type::LT_CHARAT) {
		result_dfa = StringAutomaton::MakeRelationalCharAtDfa(formula,VAR_PER_TRACK,num_tracks,left_track,right_track);
	} else {
		result_dfa = StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type::LT,VAR_PER_TRACK,num_tracks,left_track,right_track);
	}

	if(constant_string_auto != nullptr) {
		StringAutomaton_ptr constant_multi_auto = new StringAutomaton(constant_string_auto->dfa_,num_tracks-1,num_tracks,DEFAULT_NUM_OF_VARIABLES);
		temp_dfa = DFAIntersect(result_dfa,constant_multi_auto->dfa_);
		temp_auto = new StringAutomaton(temp_dfa,num_tracks,num_tracks*VAR_PER_TRACK);
		dfaFree(result_dfa);
    result_dfa = temp_dfa;
    result_auto = temp_auto->ProjectKTrack(num_tracks-1);
    delete temp_auto;
    delete constant_multi_auto;
    delete constant_string_auto;
		result_auto->SetFormula(formula);
	} else {
		result_auto = new StringAutomaton(result_dfa,formula,num_tracks*VAR_PER_TRACK);
	}
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeLessThanOrEqual(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr constant_string_auto = nullptr;
	DFA_ptr temp_dfa = nullptr, result_dfa = nullptr, temp2_dfa = nullptr;
	auto coeff_map = formula->GetVariableCoefficientMap();
	int num_tracks = formula->GetNumberOfVariables();
	int left_track = -1, right_track = -1;
	int num_vars = 0;
	for(auto it : coeff_map) {
		if(it.second != 0) {
			num_vars++;
		}
	}

	if(num_vars == 1) {
		std::string var_name = formula->GetVariableAtIndex(0);
		int var_coeff = formula->GetVariableCoefficient(var_name);
		if(var_coeff == 1) {
			// var on left
			left_track = formula->GetVariableIndex(var_coeff);
			right_track = num_tracks;
		} else {
			// var on right
			left_track = num_tracks;
			right_track = formula->GetVariableIndex(var_coeff);
		}
		constant_string_auto = StringAutomaton::MakeString(formula->GetConstant());
		num_tracks++;
	} else {
		left_track = formula->GetVariableIndex(1);
		right_track = formula->GetVariableIndex(2);
	}


	if(formula->GetType() == StringFormula::Type::LE_CHARAT) {
		result_dfa = StringAutomaton::MakeRelationalCharAtDfa(formula,VAR_PER_TRACK,num_tracks,left_track,right_track);
	} else {
		result_dfa = StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type::LE,VAR_PER_TRACK,num_tracks,left_track,right_track);
	}

	if(constant_string_auto != nullptr) {
		StringAutomaton_ptr constant_multi_auto = new StringAutomaton(constant_string_auto->dfa_,num_tracks-1,num_tracks,DEFAULT_NUM_OF_VARIABLES);
		temp_dfa = DFAIntersect(result_dfa,constant_multi_auto->dfa_);
		temp_auto = new StringAutomaton(temp_dfa,num_tracks,num_tracks*VAR_PER_TRACK);
		dfaFree(result_dfa);
		result_dfa = temp_dfa;
		result_auto = temp_auto->ProjectKTrack(num_tracks-1);
		delete temp_auto;
		delete constant_multi_auto;
		delete constant_string_auto;
		result_auto->SetFormula(formula);
	} else {
		result_auto = new StringAutomaton(result_dfa,formula,num_tracks*VAR_PER_TRACK);
	}
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeGreaterThan(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr constant_string_auto = nullptr;
	DFA_ptr temp_dfa = nullptr, result_dfa = nullptr, temp2_dfa = nullptr;
	auto coeff_map = formula->GetVariableCoefficientMap();
	int num_tracks = formula->GetNumberOfVariables();
	int left_track = -1, right_track = -1;
	int num_vars = 0;
	for(auto it : coeff_map) {
		if(it.second != 0) {
			num_vars++;
		}
	}

	if(num_vars == 1) {
		std::string var_name = formula->GetVariableAtIndex(0);
		int var_coeff = formula->GetVariableCoefficient(var_name);
		if(var_coeff == 1) {
			// var on left
			left_track = formula->GetVariableIndex(var_coeff);
			right_track = num_tracks;
		} else {
			// var on right
			left_track = num_tracks;
			right_track = formula->GetVariableIndex(var_coeff);
		}
		constant_string_auto = StringAutomaton::MakeString(formula->GetConstant());
		num_tracks++;
	} else {
		left_track = formula->GetVariableIndex(1);
		right_track = formula->GetVariableIndex(2);
	}


	if(formula->GetType() == StringFormula::Type::GT_CHARAT) {
		result_dfa = StringAutomaton::MakeRelationalCharAtDfa(formula,VAR_PER_TRACK,num_tracks,left_track,right_track);
	} else {
		result_dfa = StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type::GT,VAR_PER_TRACK,num_tracks,left_track,right_track);
	}

	if(constant_string_auto != nullptr) {
		StringAutomaton_ptr constant_multi_auto = new StringAutomaton(constant_string_auto->dfa_,num_tracks-1,num_tracks,DEFAULT_NUM_OF_VARIABLES);
		temp_dfa = DFAIntersect(result_dfa,constant_multi_auto->dfa_);
		temp_auto = new StringAutomaton(temp_dfa,num_tracks,num_tracks*VAR_PER_TRACK);
		dfaFree(result_dfa);
		result_dfa = temp_dfa;
		result_auto = temp_auto->ProjectKTrack(num_tracks-1);
		delete temp_auto;
		delete constant_multi_auto;
		delete constant_string_auto;
		result_auto->SetFormula(formula);
	} else {
		result_auto = new StringAutomaton(result_dfa,formula,num_tracks*VAR_PER_TRACK);
	}


	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeGreaterThanOrEqual(StringFormula_ptr formula) {
	StringAutomaton_ptr result_auto = nullptr, temp_auto = nullptr;
	StringAutomaton_ptr constant_string_auto = nullptr;
	DFA_ptr temp_dfa = nullptr, result_dfa = nullptr, temp2_dfa = nullptr;
	auto coeff_map = formula->GetVariableCoefficientMap();
	int num_tracks = formula->GetNumberOfVariables();
	int left_track = -1, right_track = -1;
	int num_vars = 0;
	for(auto it : coeff_map) {
		if(it.second != 0) {
			num_vars++;
		}
	}

	if(num_vars == 1) {
		std::string var_name = formula->GetVariableAtIndex(0);
		int var_coeff = formula->GetVariableCoefficient(var_name);
		if(var_coeff == 1) {
			// var on left
			left_track = formula->GetVariableIndex(var_coeff);
			right_track = num_tracks;
		} else {
			// var on right
			left_track = num_tracks;
			right_track = formula->GetVariableIndex(var_coeff);
		}
		constant_string_auto = StringAutomaton::MakeString(formula->GetConstant());
		num_tracks++;
	} else {
		left_track = formula->GetVariableIndex(1);
		right_track = formula->GetVariableIndex(2);
	}


	if(formula->GetType() == StringFormula::Type::GE_CHARAT) {
		result_dfa = StringAutomaton::MakeRelationalCharAtDfa(formula,VAR_PER_TRACK,num_tracks,left_track,right_track);
	} else {
		result_dfa = StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type::GE,VAR_PER_TRACK,num_tracks,left_track,right_track);
	}

	if(constant_string_auto != nullptr) {
		StringAutomaton_ptr constant_multi_auto = new StringAutomaton(constant_string_auto->dfa_,num_tracks-1,num_tracks,DEFAULT_NUM_OF_VARIABLES);
		temp_dfa = DFAIntersect(result_dfa,constant_multi_auto->dfa_);
		temp_auto = new StringAutomaton(temp_dfa,num_tracks,num_tracks*VAR_PER_TRACK);
		dfaFree(result_dfa);
		result_dfa = temp_dfa;
		result_auto = temp_auto->ProjectKTrack(num_tracks-1);
		delete temp_auto;
		delete constant_multi_auto;
		delete constant_string_auto;
		result_auto->SetFormula(formula);
	} else {
		result_auto = new StringAutomaton(result_dfa,formula,num_tracks*VAR_PER_TRACK);
	}
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringUnaligned(StringFormula_ptr formula) {
  StringAutomaton_ptr result_auto = nullptr;

  // if only one variable, don't complicate with lambda transitions
  if(formula->GetNumberOfVariables() == 1) {
    result_auto = StringAutomaton::MakeAnyString();
    result_auto->SetFormula(formula);
    return result_auto;
  }

	DFA_ptr result, temp;
  int len = VAR_PER_TRACK * formula->GetNumberOfVariables();
  int *mindices = Automaton::GetBddVariableIndices(len);

  dfaSetup(1, len, mindices);
  dfaAllocExceptions(0);
  dfaStoreState(0);

  temp = dfaBuild("+");
  result = dfaMinimize(temp);
  dfaFree(temp);
  //delete[] mindices;
  result_auto = new StringAutomaton(result, formula,len);
  return result_auto;
}

StringAutomaton_ptr StringAutomaton::MakeAnyStringAligned(StringFormula_ptr formula) {
  StringAutomaton_ptr result_auto = nullptr;
  
  // if only one variable, don't complicate with lambda transitions
  if(formula->GetNumberOfVariables() == 1) {
    result_auto = StringAutomaton::MakeAnyString();
    result_auto->SetFormula(formula);
    return result_auto;
  }

  StringAutomaton_ptr aligned_auto = nullptr, any_auto = nullptr, temp_auto = nullptr;
  StringAutomaton_ptr any_string_auto = nullptr;

  aligned_auto = MakeAnyStringUnaligned(formula);
  any_string_auto = StringAutomaton::MakeAnyString();
  const int number_of_string_vars = formula->GetNumberOfVariables();
  for(unsigned i = 0; i < number_of_string_vars; i++) {
    any_auto = new StringAutomaton(any_string_auto->getDFA(), i, number_of_string_vars, DEFAULT_NUM_OF_VARIABLES);
    temp_auto = aligned_auto->Intersect(any_auto);
    delete aligned_auto;
    delete any_auto;
    aligned_auto = temp_auto;
  }
  result_auto = aligned_auto;
  delete any_string_auto;
  return result_auto;
}

StringAutomaton_ptr StringAutomaton::Complement() {
	auto complement_dfa = Automaton::DFAComplement(dfa_);
	auto temp_auto = new StringAutomaton(complement_dfa, formula_->Complement(),num_of_bdd_variables_);
	StringAutomaton_ptr complement_auto = temp_auto;

	if(num_tracks_ > 1) {
		auto aligned_universe_auto = MakeAnyStringAligned(formula_->clone());
		complement_auto = temp_auto->Intersect(aligned_universe_auto);
		delete temp_auto;
		delete aligned_universe_auto;
	}
  DVLOG(VLOG_LEVEL) << complement_auto->id_ << " = [" << this->id_ << "]->Complement()";
	return complement_auto;


//	DFA_ptr complement_dfa = nullptr, minimized_dfa = nullptr, current_dfa = dfaCopy(dfa_);
//	StringAutomaton_ptr complement_auto = nullptr;
//	StringAutomaton_ptr any_string = StringAutomaton::MakeAnyString();
//
//	dfaNegation(current_dfa);
//	complement_dfa = dfaProduct(any_string->dfa_, current_dfa, dfaAND); // this is to handle case where we complement an automaton that has empty language (/#/ in regex notation)
//	delete any_string; any_string = nullptr;
//	dfaFree(current_dfa); current_dfa = nullptr;
//
//	minimized_dfa = dfaMinimize(complement_dfa);
//	dfaFree(complement_dfa); complement_dfa = nullptr;
//
//	complement_auto = new StringAutomaton(minimized_dfa, num_of_bdd_variables_);
//
//	DVLOG(VLOG_LEVEL) << complement_auto->id_ << " = [" << this->id_ << "]->makeComplement()";
//
//	return complement_auto;
}

StringAutomaton_ptr StringAutomaton::Intersect(StringAutomaton_ptr other_auto) {
	// if both autos are same size, we're good. Otherwise, if one auto has one track
	// put it in a multi-track with the correct track.
  if(this->num_tracks_ != other_auto->num_tracks_) {
    StringAutomaton_ptr small_auto, big_auto;
		if(this->num_tracks_ == 1 && other_auto->num_tracks_ != 1 && !this->formula_->IsConstant()) {
			small_auto = this;
			big_auto = other_auto;
		} else if(other_auto->num_tracks_ == 1 && !other_auto->formula_->IsConstant()) {
			small_auto = other_auto;
			big_auto = this;
		} else {
			LOG(FATAL) << "Intersection between incompatible StringAutomata";
		}

		std::string variable_name = small_auto->formula_->GetVariableAtIndex(0);
    int index = big_auto->formula_->GetVariableIndex(variable_name);
    auto relation_other_auto = new StringAutomaton(small_auto->dfa_,index,big_auto->num_tracks_,small_auto->num_of_bdd_variables_);
    relation_other_auto->SetFormula(big_auto->GetFormula()->clone());
    auto intersect_auto = big_auto->Intersect(relation_other_auto);
    delete relation_other_auto;
    return intersect_auto;
  }
	auto intersect_dfa = Automaton::DFAIntersect(this->dfa_, other_auto->dfa_);
  StringFormula_ptr intersect_formula = nullptr;
  if(formula_ != nullptr && other_auto->formula_ != nullptr) {
    intersect_formula = formula_->Intersect(other_auto->formula_);
  } else if(formula_ != nullptr) {
    intersect_formula = formula_->clone();
  } else {
    intersect_formula = nullptr;
  }

	auto intersect_auto = new StringAutomaton(intersect_dfa,intersect_formula,this->num_of_bdd_variables_);

  DVLOG(VLOG_LEVEL) << intersect_auto->id_ << " = [" << this->id_ << "]->Intersect(" << other_auto->id_ << ")";
	return intersect_auto;
}

StringAutomaton_ptr StringAutomaton::Union(StringAutomaton_ptr other_auto) {
	CHECK_EQ(this->num_tracks_,other_auto->num_tracks_);
	auto union_dfa = Automaton::DFAUnion(this->dfa_, other_auto->dfa_);
	auto union_formula = this->formula_->Union(other_auto->formula_);
	auto union_auto = new StringAutomaton(union_dfa,union_formula,this->num_of_bdd_variables_);

	DVLOG(VLOG_LEVEL) << union_auto->id_ << " = [" << this->id_ << "]->union(" << other_auto->id_ << ")";
	return union_auto;
}

StringAutomaton_ptr StringAutomaton::Difference(StringAutomaton_ptr other_auto) {
  CHECK_EQ(this->num_tracks_,other_auto->num_tracks_);
	auto complement_auto = other_auto->Complement();
	auto difference_auto = this->Intersect(complement_auto);
	delete complement_auto;

	DVLOG(VLOG_LEVEL) << difference_auto->id_ << " = [" << this->id_ << "]->Difference(" << other_auto->id_ << ")";
	return difference_auto;
}

StringAutomaton_ptr StringAutomaton::Concat(StringAutomaton_ptr other_auto) {
  CHECK_EQ(this->num_tracks_,other_auto->num_tracks_);
//  this->Minimize();
//  other_auto->Minimize();
//  StringAutomaton_ptr concat_auto = static_cast<StringAutomaton_ptr>(Automaton::Concat(other_auto));
  auto concat_dfa = StringAutomaton::concat(dfa_, other_auto->dfa_,this->num_of_bdd_variables_);
  auto concat_auto = new StringAutomaton(concat_dfa,this->num_of_bdd_variables_);
  return concat_auto;
}

StringAutomaton_ptr StringAutomaton::Optional() {
	CHECK_EQ(this->num_tracks_,1);
	StringAutomaton_ptr optional_auto = nullptr, empty_string = nullptr;

	empty_string = StringAutomaton::MakeEmptyString();
	optional_auto = this->Union(empty_string);
	delete empty_string;

	DVLOG(VLOG_LEVEL) << optional_auto->id_ << " = [" << this->id_ << "]->optional()";

	return optional_auto;
}

StringAutomaton_ptr StringAutomaton::Closure() {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr result_auto = nullptr;
  DFA_ptr result_dfa = nullptr, temp_dfa = nullptr;
  paths state_paths, pp;
  trace_descr tp;
  int sink = GetSinkState();
  CHECK_GT(sink,-1);
  int var = DEFAULT_NUM_OF_VARIABLES;
  int len = var + 1; //one extra bit
  int *indices = GetBddVariableIndices(len);
  char *statuses = new char[dfa_->ns+1];
  std::vector<std::pair<int,std::vector<char>>> added_exeps, original_exeps;
  std::vector<char> exep;

  dfaSetup(dfa_->ns, len, indices);
  //construct the added paths
  state_paths = pp = make_paths(dfa_->bddm, dfa_->q[dfa_->s]);
  exep = std::vector<char>(len,'X');
  exep.push_back('\0');
  while (pp) {
    if (pp->to != sink) {
      for (int j = 0; j < var; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value)
            exep[j] = '1';
          else
            exep[j] = '0';
        } else
          exep[j] = 'X';
      }
      exep[len-1] = '1'; //new path
      added_exeps.push_back(std::make_pair(pp->to,exep));
    }
    pp = pp->next;
  }
  kill_paths(state_paths);

  exep = std::vector<char>(len,'X');
  exep.push_back('\0');
  for (int i = 0; i < dfa_->ns; i++) {
    state_paths = pp = make_paths(dfa_->bddm, dfa_->q[i]);
    while (pp) {
      if (pp->to != sink) {
        for (int j = 0; j < var; j++) {
          //the following for loop can be avoided if the indices are in order
          for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);

          if (tp) {
            if (tp->value)
              exep[j] = '1';
            else
              exep[j] = '0';
          } else
            exep[j] = 'X';
        }
        exep[len-1] = '0'; //old value
        original_exeps.push_back(std::make_pair(pp->to,exep));
      }
      pp = pp->next;
    }
    if (dfa_->f[i] == 1) { //add added paths
      dfaAllocExceptions(added_exeps.size() + original_exeps.size());
      for(int k = 0; k < added_exeps.size(); k++) {
        dfaStoreException(added_exeps[k].first,&added_exeps[k].second[0]);
      }
      for(int k = 0; k < original_exeps.size(); k++) {
        dfaStoreException(original_exeps[k].first,&original_exeps[k].second[0]);
      }
      statuses[i] = '+';
    } else {
      dfaAllocExceptions(original_exeps.size());
      for(int k = 0; k < original_exeps.size(); k++) {
        dfaStoreException(original_exeps[k].first,&original_exeps[k].second[0]);
      }
      if (dfa_->f[i] == -1)
        statuses[i] = '-';
      else
        statuses[i] = '0';
    }
    dfaStoreState(sink);
    kill_paths(state_paths);
    original_exeps.clear();
  }
  statuses[dfa_->ns] = '\0';
  temp_dfa = dfaBuild(statuses);
  result_dfa = dfaProject(temp_dfa, (unsigned) var); //var is the index of the extra bit
  dfaFree(temp_dfa);
  temp_dfa = result_dfa;
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);

  result_auto = new StringAutomaton(result_dfa, num_of_bdd_variables_);
  //delete[] indices;
  delete[] statuses;
  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->closure()";
  return result_auto;
}

StringAutomaton_ptr StringAutomaton::KleeneClosure() {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr kleene_closure_auto = nullptr, closure_auto = nullptr, empty_string = nullptr;

  closure_auto = this->Closure();
  empty_string = StringAutomaton::MakeEmptyString();
  kleene_closure_auto = closure_auto->Union(empty_string);
  delete closure_auto;
  delete empty_string;

  DVLOG(VLOG_LEVEL) << kleene_closure_auto->id_ << " = [" << this->id_ << "]->kleeneClosure()";

  return kleene_closure_auto;
}

StringAutomaton_ptr StringAutomaton::Repeat(unsigned min) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr repeated_auto = nullptr;

  if (min == 0) {
    repeated_auto = this->KleeneClosure();
  } else if (min == 1) {
    repeated_auto = this->Closure();
  } else {
    StringAutomaton_ptr closure_auto = this->Closure();
    StringAutomaton_ptr range_auto = StringAutomaton::MakeAnyStringLengthGreaterThanOrEqualTo(min);
    repeated_auto = closure_auto->Intersect(range_auto);
    delete range_auto; range_auto = nullptr;
    delete closure_auto; closure_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL) << repeated_auto->id_ << " = [" << this->id_ << "]->repeat(" << min << ")";

  return repeated_auto;
}

StringAutomaton_ptr StringAutomaton::Repeat(unsigned min, unsigned max) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr repeated_auto = nullptr;

  if (min == 0) {
    repeated_auto = this->KleeneClosure();
  } else {
    repeated_auto = this->Closure();
  }

  StringAutomaton_ptr range_auto = StringAutomaton::MakeAnyStringWithLengthInRange(min, max);
  StringAutomaton_ptr tmp_auto = repeated_auto;
  repeated_auto = tmp_auto->Intersect(range_auto);
  delete range_auto; range_auto = nullptr;
  delete tmp_auto; tmp_auto = nullptr;

  DVLOG(VLOG_LEVEL) << repeated_auto->id_ << " = [" << this->id_ << "]->repeat(" << min << ", " << max << ")";

  return repeated_auto;
}

StringAutomaton_ptr StringAutomaton::Suffixes() {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr suffixes_auto = nullptr;
  if (this->IsEmptyLanguage()) {
    suffixes_auto = StringAutomaton::MakePhi();
    DVLOG(VLOG_LEVEL) << suffixes_auto->id_ << " = [" << this->id_ << "]->suffixes()";
    return suffixes_auto;
  }
  int number_of_variables = this->num_of_bdd_variables_,
          number_of_states = this->dfa_->ns,
          sink_state = this->GetSinkState(),
          next_state = -1;
  unsigned max = number_of_states;
  if (sink_state != -1) {
    max = max - 1;
  }
  bool has_sink = true;
  if(sink_state == -1) {
  	has_sink = false;
  }
  // if number of variables are too large for mona, implement an algorithm that find suffixes by finding
  // sub suffixes and union them
  number_of_variables = this->num_of_bdd_variables_ + std::ceil(std::log2(max)); // number of variables required
  int* indices = GetBddVariableIndices(number_of_variables);

  unsigned extra_bits_value = 0;
  int number_of_extra_bits_needed = number_of_variables - this->num_of_bdd_variables_;

  std::vector<char>* current_exception = nullptr;
  std::map<int, std::map<std::vector<char>*, int>> exception_map;

  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;

  for (int s = 0; s < number_of_states; s++) {
    if (s != sink_state) {
      exception_map[s]; // initialize map entry
      state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[s]);
      while (pp) {
        if (pp->to != sink_state) {
          current_exception = new std::vector<char>();
          for (int j = 0; j < this->num_of_bdd_variables_; j++) {
            for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
            if (tp) {
              if (tp->value) {
                current_exception->push_back('1');
              } else {
                current_exception->push_back('0');
              }
            } else {
              current_exception->push_back('X');
            }
          }


          exception_map[s][current_exception] = pp->to;
          current_exception = nullptr;
        }
        tp = nullptr;
        pp = pp->next;
      }

      kill_paths(state_paths);
      state_paths = pp = nullptr;
      // add to start state by adding extra bits
      if (s != this->dfa_->s) {
        ++extra_bits_value;
        auto extra_bit_binary_format = GetBinaryFormat(extra_bits_value, number_of_extra_bits_needed);
        for (auto& exceptions : exception_map[s]) {
          current_exception = new std::vector<char>();
          current_exception->insert(current_exception->begin(), exceptions.first->begin(), exceptions.first->end());
          for (int i = 0; i < number_of_extra_bits_needed; i++) {
            current_exception->push_back(extra_bit_binary_format[i]); // new transitions for start state
            exceptions.first->push_back('0'); // default transitions have all zero's in extrabits
          }
          current_exception->push_back('\0');
          exceptions.first->push_back('\0');
          exception_map[this->dfa_->s][current_exception] = exceptions.second;
          current_exception = nullptr;
        }
      } else {
        // initial state default transitions' extra bits extended with all zeros
        for (auto& exceptions : exception_map[this->dfa_->s]) {
          for (int i = 0; i < number_of_extra_bits_needed; i++) {
            exceptions.first->push_back('0'); // default transitions have all zero's in extrabits
          }
          exceptions.first->push_back('\0');
        }
      }
    }
  }



  if(!has_sink) {
  	sink_state = number_of_states;
  	number_of_states++;
  }

  char* statuses = new char[number_of_states + 1];

  dfaSetup(number_of_states, number_of_variables, indices);
  for (int s = 0; s < number_of_states; s++) {
    statuses[s] = '-';
    if (s != sink_state) {
      statuses[s] = '-'; // initially
      dfaAllocExceptions(exception_map[s].size());
      for (auto it = exception_map[s].begin(); it != exception_map[s].end();) {
        dfaStoreException(it->second, &*it->first->begin());
        current_exception = it->first;
        it = exception_map[s].erase(it);
        delete current_exception;
      }
      dfaStoreState(sink_state);
      current_exception = nullptr;
      if (IsAcceptingState(s)) {
        statuses[s] = '+';
      }
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(s);
    }
  }

  statuses[number_of_states] = '\0';
  DFA_ptr result_dfa = dfaBuild(statuses);
  //delete[] indices;
  delete[] statuses;
  suffixes_auto = new StringAutomaton(dfaMinimize(result_dfa), number_of_variables);
  dfaFree(result_dfa); result_dfa = nullptr;

  while (number_of_extra_bits_needed > 0) {
    suffixes_auto->ProjectAway((unsigned)(suffixes_auto->num_of_bdd_variables_ - 1));
    suffixes_auto->Minimize();
    number_of_extra_bits_needed--;
  }

  DVLOG(VLOG_LEVEL) << suffixes_auto->id_ << " = [" << this->id_ << "]->suffixes()";
  return suffixes_auto;
}

StringAutomaton_ptr StringAutomaton::SuffixesAtIndex(int index) {
	CHECK_EQ(this->num_tracks_,1);
  return SuffixesFromTo(index, index);
}

StringAutomaton_ptr StringAutomaton::SuffixesFromIndex(int start) {
	CHECK_EQ(this->num_tracks_,1);
  return SuffixesFromTo(start, this->dfa_->ns);
}

StringAutomaton_ptr StringAutomaton::SuffixesFromTo(int start, int end) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr suffixes_auto = nullptr;

  if (this->IsEmptyLanguage()) {
    suffixes_auto = StringAutomaton::MakePhi();
    DVLOG(VLOG_LEVEL) << suffixes_auto->id_ << " = [" << this->id_ << "]->suffixes(" << start << ", " << end << ")";
    return suffixes_auto;
  }

  std::set<int> suffixes_from = getStatesReachableBy(start, end);
  unsigned max = suffixes_from.size();
  if (max == 0) {
    suffixes_auto = StringAutomaton::MakePhi();
    DVLOG(VLOG_LEVEL) << suffixes_auto->id_ << " = [" << this->id_ << "]->suffixes(" << start << ", " << end << ")";
    return suffixes_auto;
  } else if (max == 1) {
    max = 2; // that will increase the number_of_variables by 1, by doing so we get a perfectly minimized auto at the end
  }

  // if number of variables are too large for mona, implement an algorithm that find suffixes by finding
  // sub suffixes and union them
  const int number_of_variables = this->num_of_bdd_variables_ + std::ceil(std::log2(max)), // number of variables required
          number_of_states = this->dfa_->ns + 1; // one extra start for the new start state
  int sink_state = this->GetSinkState();

  int* indices = GetBddVariableIndices(number_of_variables);
  char* statuses = new char[number_of_states + 1];
  unsigned extra_bits_value = 0;

  const int number_of_extra_bits_needed = number_of_variables - this->num_of_bdd_variables_;

  std::vector<char>* current_exception = nullptr;
  std::map<int, std::map<std::vector<char>*, int>> exception_map;

  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;
  for (int s = 0; s < this->dfa_->ns; s++) {
    if (s != sink_state) {
      int state_id = s + 1; // new states are off by one
      exception_map[state_id]; // initialize map entry
      state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[s]);
      while (pp) {
        if (pp->to != (unsigned)sink_state) {
          current_exception = new std::vector<char>();
          for (int j = 0; j < this->num_of_bdd_variables_; j++) {
            for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
            if (tp) {
              if (tp->value) {
                current_exception->push_back('1');
              } else {
                current_exception->push_back('0');
              }
            } else {
              current_exception->push_back('X');
            }
          }

          exception_map[state_id][current_exception] = pp->to + 1; // there is a new start state, old states are off by one
          current_exception = nullptr;
        }
        tp = nullptr;
        pp = pp->next;
      }

      kill_paths(state_paths);
      state_paths = pp = nullptr;
      // add to start state by adding extra bits
      if (suffixes_from.find(s) != suffixes_from.end()) {
        auto extra_bit_binary_format = GetBinaryFormat(extra_bits_value, number_of_extra_bits_needed);
        for (auto& exceptions : exception_map[state_id]) {
          current_exception = new std::vector<char>();
          current_exception->insert(current_exception->begin(), exceptions.first->begin(), exceptions.first->end());
          for (int i = 0; i < number_of_extra_bits_needed; i++) {
            current_exception->push_back(extra_bit_binary_format[i]); // new transitions for start state
            exceptions.first->push_back('0');                         // default transitions have all zero's in extrabits
          }
          current_exception->push_back('\0');
          exceptions.first->push_back('\0');
          exception_map[0][current_exception] = exceptions.second; // new start state
          current_exception = nullptr;
        }
        ++extra_bits_value;
      } else {
        // default transitions' extra bits extended with all zeros
        for (auto& exceptions : exception_map[s]) {
          for (int i = 0; i < number_of_extra_bits_needed; i++) {
            exceptions.first->push_back('0'); // default transitions have all zero's in extrabits
          }
          exceptions.first->push_back('\0');
        }
      }
    }
  }

  if (sink_state != -1) {
    ++sink_state; // old states are off by one
  }

  dfaSetup(number_of_states, number_of_variables, indices);
  for (int s = 0; s < number_of_states; s++) {
    statuses[s] = '-';
    if (s != sink_state) {
      int old_state = s - 1;
      statuses[s] = '-'; // initially
      dfaAllocExceptions(exception_map[s].size());
      for (auto it = exception_map[s].begin(); it != exception_map[s].end();) {
        dfaStoreException(it->second, &*it->first->begin());
        current_exception = it->first;
        it = exception_map[s].erase(it);
        delete current_exception;
      }
      dfaStoreState(sink_state);
      current_exception = nullptr;
      if (old_state > -1 and IsAcceptingState(old_state)) {
        statuses[s] = '+';
      }
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(s);
    }
  }

  statuses[number_of_states] = '\0';
  DFA_ptr result_dfa = dfaBuild(statuses);
  //delete[] indices;
  delete[] statuses;
  suffixes_auto = new StringAutomaton(dfaMinimize(result_dfa), number_of_variables);
  dfaFree(result_dfa); result_dfa = nullptr;

  for ( int i = 0; i < number_of_extra_bits_needed; ++i) {
    suffixes_auto->ProjectAway((unsigned)(suffixes_auto->num_of_bdd_variables_ - 1));
    suffixes_auto->Minimize();
  }

  DVLOG(VLOG_LEVEL) << suffixes_auto->id_ << " = [" << this->id_ << "]->suffixes(" << start << ", " << end << ")";
  return suffixes_auto;
}

StringAutomaton_ptr StringAutomaton::Prefixes() {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr prefix_auto = this->clone();
  int sink_state = prefix_auto->GetSinkState();


  for (int s = 0; s < prefix_auto->dfa_->ns; s++) {
    if(s != sink_state){
      prefix_auto->dfa_->f[s] = 1;
    }
  }

  prefix_auto->Minimize();

  DVLOG(VLOG_LEVEL) << prefix_auto->id_ << " = [" << this->id_ << "]->prefixes()";
  return prefix_auto;
}

StringAutomaton_ptr StringAutomaton::PrefixesUntilIndex(int index) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr prefixes_auto = nullptr;
  StringAutomaton_ptr length_auto = nullptr;
  StringAutomaton_ptr prefixesUntil_auto = nullptr;

  prefixes_auto = this->Prefixes();
  length_auto = MakeAnyStringLengthLessThan(index);

  prefixesUntil_auto = prefixes_auto->Intersect(length_auto);
  DVLOG(VLOG_LEVEL) << prefixesUntil_auto->id_ << " = [" << this->id_ << "]->prefixesUntilIndex("<<index<<")";
  return prefixesUntil_auto;
}

StringAutomaton_ptr StringAutomaton::PrefixesAtIndex(int index) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr length_auto = nullptr;
  auto prefixes_auto = this->Prefixes();
  if (index == 0 and this->HasEmptyString()) {
    // when index is 0, result should also accept empty string if subject automaton accepts empty string
    length_auto = StringAutomaton::MakeAnyStringLengthLessThanOrEqualTo(1);
  } else {
    length_auto = MakeAnyStringLengthEqualTo(index + 1);
  }
  auto prefixesAt_auto = prefixes_auto->Intersect(length_auto);
  delete prefixes_auto; prefixes_auto = nullptr;
  delete length_auto; length_auto = nullptr;
  DVLOG(VLOG_LEVEL) << prefixesAt_auto->id_ << " = [" << this->id_ << "]->prefixesAtIndex("<<index<<")";
  return prefixesAt_auto;
}

StringAutomaton_ptr StringAutomaton::SubStrings() {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr suffixes_auto = nullptr, sub_strings_auto = nullptr;

  suffixes_auto = this->Suffixes();
  sub_strings_auto = suffixes_auto->Prefixes();
  delete suffixes_auto; suffixes_auto = nullptr;

  DVLOG(VLOG_LEVEL) << sub_strings_auto->id_ << " = [" << this->id_ << "]->subStrings()";
  return sub_strings_auto;
}

StringAutomaton_ptr StringAutomaton::CharAt(const int index) {
  CHECK_EQ(this->num_tracks_,1);
  if (this->IsEmptyLanguage()) {
    auto charat_auto = StringAutomaton::MakePhi();
    DVLOG(VLOG_LEVEL) << charat_auto->id_ << " = [" << this->id_ << "]->charAt(" << index << ")";
    return charat_auto;
  }

  std::set<int> states_at_index = getStatesReachableBy(index);
  unsigned max = states_at_index.size();
  if (max == 0) {
    auto charat_auto = StringAutomaton::MakePhi();
    DVLOG(VLOG_LEVEL) << charat_auto->id_ << " = [" << this->id_ << "]->charAt(" << index << ")";
    return charat_auto;
  }

  // if number of variables are too large for mona, implement an algorithm that find suffixes by finding
  // sub suffixes and union them
  const int number_of_variables = this->num_of_bdd_variables_ + std::ceil(std::log2(max)), // number of variables required
          sink_state = this->GetSinkState();
  int* indices = GetBddVariableIndices(number_of_variables);

  unsigned extra_bits_value = 0;

  const int number_of_extra_bits_needed = number_of_variables - this->num_of_bdd_variables_;

  std::vector<char>* current_exception = nullptr;
  std::set<std::vector<char>*> exceptions;

  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;
  for (int s : states_at_index) {
    state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[s]);
    while (pp) {
      if (pp->to != (unsigned)sink_state) {
        current_exception = new std::vector<char>();
        for (int j = 0; j < this->num_of_bdd_variables_; j++) {
          for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
          if (tp) {
            if (tp->value) {
              current_exception->push_back('1');
            } else {
              current_exception->push_back('0');
            }
          } else {
            current_exception->push_back('X');
          }
        }

        auto extra_bit_binary_format = GetBinaryFormat(extra_bits_value, number_of_extra_bits_needed);
        for (int i = 0; i < number_of_extra_bits_needed; i++) {
          current_exception->push_back(extra_bit_binary_format[i]); // collected transition
        }
        current_exception->push_back('\0');
        exceptions.insert(current_exception);
        current_exception = nullptr;
      }
      tp = nullptr;
      pp = pp->next;
    }
    ++extra_bits_value;
    kill_paths(state_paths);
    state_paths = pp = nullptr;
  }

  char statuses[3] = {'-', '+', '-'};
  dfaSetup(3, number_of_variables, indices);
  // 0 -> 1
  dfaAllocExceptions(exceptions.size());
  for (auto it = exceptions.begin(); it != exceptions.end();) {
    auto ex = *it;
    dfaStoreException(1, &(*ex->begin()));
    it = exceptions.erase(it);
    delete ex;
  }
  dfaStoreState(2); // 0 -> 2

  dfaAllocExceptions(0);
  dfaStoreState(2); // 1 -> 2

  dfaAllocExceptions(0);
  dfaStoreState(2); // 2 -> 2

  DFA_ptr result_dfa = dfaBuild(statuses);
  //delete[] indices;
  auto charat_auto = new StringAutomaton(dfaMinimize(result_dfa), number_of_variables);
  dfaFree(result_dfa); result_dfa = nullptr;

  for ( int i = 0; i < number_of_extra_bits_needed; ++i) {
    charat_auto->ProjectAway((unsigned)(charat_auto->num_of_bdd_variables_ - 1));
    charat_auto->Minimize();
  }

  DVLOG(VLOG_LEVEL) << charat_auto->id_ << " = [" << this->id_ << "]->CharAt(" << index << ")";
  return charat_auto;
}

StringAutomaton_ptr StringAutomaton::CharAt(IntAutomaton_ptr index_auto) {
  CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr prefixes_auto = this->Prefixes();
  StringAutomaton_ptr string_length_auto = new StringAutomaton(index_auto->getDFA(),index_auto->get_number_of_bdd_variables());
  StringAutomaton_ptr any_char_auto = StringAutomaton::MakeAnyChar();
  StringAutomaton_ptr tmp_length_auto = string_length_auto->Concat(any_char_auto);
  string_length_auto->dfa_ = nullptr; //TODO avoid this in the future by better using unary auto instead of int auto
  delete string_length_auto;
  delete any_char_auto;
  StringAutomaton_ptr charat_indexes_auto = prefixes_auto->Intersect(tmp_length_auto);
  delete prefixes_auto;
  delete tmp_length_auto;

  const int number_of_variables = charat_indexes_auto->num_of_bdd_variables_;

  std::set<std::string> exceptions;
  for (int s = 0; s < charat_indexes_auto->dfa_->ns; ++s) {
    for (int next : charat_indexes_auto->getNextStates(s)) {
      if (charat_indexes_auto->IsAcceptingState(next)) {
        // extract transitions
        auto transitions = Automaton::DFAGetTransitionsFromTo(charat_indexes_auto->dfa_, s, next, number_of_variables);
        exceptions.insert(transitions.begin(), transitions.end());
      }
    }
  }

  const int number_of_exceptions = exceptions.size();
  dfaSetup(3, number_of_variables, GetBddVariableIndices(number_of_variables));
  char statuses[3] { '-', '+', '-' };
  //state 0
  dfaAllocExceptions(number_of_exceptions);
  for (std::string exception : exceptions) {
    dfaStoreException(1, &exception[0]);
  }
  dfaStoreState(2);

  //state 1
  dfaAllocExceptions(0);
  dfaStoreState(2);

  //state 2
  dfaAllocExceptions(0);
  dfaStoreState(2);

  DFA_ptr result_dfa = dfaBuild(statuses);

  StringAutomaton_ptr charat_auto = new StringAutomaton(dfaMinimize(result_dfa), number_of_variables);
  dfaFree(result_dfa); result_dfa = nullptr;


  DVLOG(VLOG_LEVEL) << charat_auto->id_ << " = [" << this->id_ << "]->CharAt(" << index_auto->getId() << ")";
  return charat_auto;
}

StringAutomaton_ptr StringAutomaton::SubString(const int start) {
  CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr substring_auto = nullptr;
  substring_auto = this->SuffixesAtIndex(start);
  DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subString(" << start << ")";
  return substring_auto;
}

/**
 * TODO decide on substring second param; which one is better:
 * end index, or length of substring
 * subString returns empty when start == end, start is inclusive, end is exclusive
 */
StringAutomaton_ptr StringAutomaton::SubString(const int start, const int end) {
  CHECK_EQ(this->num_tracks_,1);
  if (start == end) {
    auto substring_auto = StringAutomaton::MakeEmptyString();
    DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subString(" << start << "," << end << ")";
    return substring_auto;
  }

  int adjusted_end = end;
  if (start < end) {
    --adjusted_end;
  }

  auto suffixes_auto = this->SuffixesAtIndex(start);
  auto substring_auto = suffixes_auto->PrefixesAtIndex(adjusted_end - start);
  delete suffixes_auto;
  DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subString(" << start << "," << end << ")";
  return substring_auto;
}

/**
 * @param length_auto is the length of the substring
 * @param search_auto is the strings that cannot appear in the result
 * TODO if search auto contains empty string handle it as a special case
 */
StringAutomaton_ptr StringAutomaton::SubString(IntAutomaton_ptr length_auto, StringAutomaton_ptr search_auto) {
  CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr substring_auto = nullptr;

  auto prefix_does_not_contain_search_auto = this->IndexOfHelper(search_auto);
  substring_auto = prefix_does_not_contain_search_auto->RestrictLengthTo(length_auto);
  delete prefix_does_not_contain_search_auto;

  DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subString(" << length_auto->getId() << "," << search_auto->id_ << ")";
  return substring_auto;
}

StringAutomaton_ptr StringAutomaton::SubString(int start,
		IntAutomaton_ptr end_auto) {
	CHECK_EQ(this->num_tracks_,1);
  IntAutomaton_ptr valid_indexes = IntAutomaton::makeIntGreaterThan(start);
  IntAutomaton_ptr valid_end_indexes = static_cast<IntAutomaton_ptr>(end_auto->Intersect(valid_indexes));
  delete valid_indexes;
  if (valid_end_indexes->IsEmptyLanguage()) {
    return StringAutomaton::MakePhi();
  } else if (valid_end_indexes->isAcceptingSingleInt()) {
    return SubString(start, valid_end_indexes->getAnAcceptingInt());
  }
  LOG (FATAL) << "Fully implement substring with symbolic ints";
  return nullptr;
}

/**
 * A specialized substring operation that works with char or string search
 */
StringAutomaton_ptr StringAutomaton::SubStringLastOf(
		StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr substring_auto = nullptr, contains_auto = nullptr,
          last_index_of_auto = nullptr, right_auto = nullptr,
          search_param_auto = search_auto;

  bool search_has_empty_string = false;

  if (search_param_auto->HasEmptyString()) {
    StringAutomaton_ptr non_empty_string = MakeAnyStringLengthGreaterThan(0);
    search_param_auto = search_param_auto->Intersect(non_empty_string);
    delete non_empty_string; non_empty_string = nullptr;
    search_has_empty_string = true;
  }

  contains_auto = this->Contains(search_param_auto);
  if (contains_auto->IsEmptyLanguage()) {
    delete contains_auto; contains_auto = nullptr;
    if (search_has_empty_string) {
      substring_auto = StringAutomaton::MakeEmptyString();
      delete search_param_auto; search_param_auto = nullptr;
    } else {
      substring_auto = StringAutomaton::MakePhi();
    }
    DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subStringLastOf(" << search_auto->id_  << ")";
    return substring_auto;
  }

  last_index_of_auto = contains_auto->LastIndexOfHelper(search_param_auto);

  // Get substring automaton using preConcatRight
  right_auto = contains_auto->PreConcatRight(last_index_of_auto);
  delete last_index_of_auto; last_index_of_auto = nullptr;
  delete contains_auto; contains_auto = nullptr;
  substring_auto = right_auto->RestrictLastOccuranceOf(search_param_auto);
  delete right_auto; right_auto = nullptr;

  if (search_has_empty_string) {
    StringAutomaton_ptr tmp_auto = substring_auto;
    StringAutomaton_ptr empty_string = StringAutomaton::MakeEmptyString();
    substring_auto = tmp_auto->Union(empty_string);
    delete tmp_auto; tmp_auto = nullptr;
    delete empty_string; empty_string = nullptr;
  }

  DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subStringLastOf(" << search_auto->id_ << ")";
  return substring_auto;
}

/**
 * A specialized substring operation that works with char or string search
 */
StringAutomaton_ptr StringAutomaton::SubStringFirstOf(
		StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr substring_auto = nullptr, contains_auto = nullptr,
          index_of_auto = nullptr, right_auto = nullptr,
          search_param_auto = search_auto;

  bool search_has_empty_string = false;

  if (search_param_auto->HasEmptyString()) {
    StringAutomaton_ptr non_empty_string = MakeAnyStringLengthGreaterThan(0);
    search_param_auto = search_param_auto->Intersect(non_empty_string);
    delete non_empty_string; non_empty_string = nullptr;
    search_has_empty_string = true;
  }

  contains_auto = this->Contains(search_param_auto);
  if (contains_auto->IsEmptyLanguage()) {
    delete contains_auto; contains_auto = nullptr;
    if (search_has_empty_string) {
      substring_auto = this->clone();
      delete search_param_auto; search_param_auto = nullptr;
    } else {
      substring_auto = StringAutomaton::MakePhi();
    }
    DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subStringFirstOf(" << search_auto->id_  << ")";
    return substring_auto;
  }

  index_of_auto = contains_auto->IndexOfHelper(search_param_auto);

  // Get substring automaton using preConcatRight
  right_auto = contains_auto->PreConcatRight(index_of_auto);
  delete index_of_auto; index_of_auto = nullptr;
  delete contains_auto; contains_auto = nullptr;

  substring_auto = right_auto->Begins(search_auto);

  delete right_auto; right_auto = nullptr;

  if (search_has_empty_string) {
    StringAutomaton_ptr tmp_auto = substring_auto;
    substring_auto = tmp_auto->Union(this);
    delete tmp_auto; tmp_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL) << substring_auto->id_ << " = [" << this->id_ << "]->subStringFirstOf(" << search_auto->id_ << ")";

  return substring_auto;
}

/**
 * TODO check if any 255 transition goes to a valid state at the end
 * TODO Add support when search auto is not a singleton
 */
IntAutomaton_ptr StringAutomaton::IndexOf(StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr contains_auto = nullptr, difference_auto = nullptr,
      index_of_auto = nullptr, search_param_auto = search_auto;
  IntAutomaton_ptr length_auto = nullptr;

  bool has_negative_1 = false;
  bool search_has_empty_string = false;

  if (search_param_auto->HasEmptyString()) {
    StringAutomaton_ptr non_empty_string = MakeAnyStringLengthGreaterThan(0);
    search_param_auto = search_param_auto->Intersect(non_empty_string);
    delete non_empty_string; non_empty_string = nullptr;
    search_has_empty_string = true;
  }

  contains_auto = this->Contains(search_param_auto);
  if (contains_auto->IsEmptyLanguage()) {
    delete contains_auto;
    // if search has empty string indexOf also returns 0
    if (search_has_empty_string) {
      length_auto = IntAutomaton::makeZero();
      length_auto->setMinus1(true);
      delete search_param_auto; search_param_auto = nullptr; // search_param_auto auto is not the parameter search auto, it is updated, delete it
    } else {
      length_auto = IntAutomaton::makeInt(-1);
    }

    DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id_ << "]->indexOf(" << search_auto->id_  << ")";
    return length_auto;
  }

  // check for the cases where string does not contain the search char, return -1 in that case
  difference_auto = this->Difference(contains_auto);
  if (not difference_auto->IsEmptyLanguage()) {
    has_negative_1 = true;
  }
  delete difference_auto;
  index_of_auto = contains_auto->IndexOfHelper(search_param_auto);
  delete contains_auto; contains_auto = nullptr;

  length_auto = index_of_auto->Length();
  length_auto->setMinus1(has_negative_1);
  delete index_of_auto; index_of_auto = nullptr;

  // if search has empty string indexOf also returns 0
  if (search_has_empty_string) {
    if (not length_auto->hasZero()) {
      IntAutomaton_ptr tmp = length_auto;
      IntAutomaton_ptr zero_int = IntAutomaton::makeZero();
      length_auto = static_cast<IntAutomaton_ptr>(tmp->Union(zero_int));
      delete tmp; tmp = nullptr;
      delete zero_int;
    }
    delete search_param_auto; search_param_auto = nullptr; // search_param_auto auto is not the parameter search auto, it is updated, delete it
  }

  DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id_ << "]->indexOf(" << search_auto->id_  << ")";
  return length_auto;
}

/**
 *
 * TODO Add support when search auto is not a singleton, see test case 09
 */
IntAutomaton_ptr StringAutomaton::LastIndexOf(StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr contains_auto = nullptr, difference_auto = nullptr,
      last_index_of_auto = nullptr, search_param_auto = search_auto;
  IntAutomaton_ptr length_auto = nullptr;

  bool has_negative_1 = false;
  bool search_has_empty_string = false;

  if (search_param_auto->HasEmptyString()) {
    StringAutomaton_ptr non_empty_string = MakeAnyStringLengthGreaterThan(0);
    search_param_auto = search_param_auto->Intersect(non_empty_string);
    delete non_empty_string; non_empty_string = nullptr;
    search_has_empty_string = true;
  }

  contains_auto = this->Contains(search_param_auto);
  if (contains_auto->IsEmptyLanguage()) {
    delete contains_auto;
    if (search_has_empty_string) {
      length_auto = this->Length();
      length_auto->setMinus1(true);
      delete search_param_auto; search_param_auto = nullptr; // search_param_auto auto is not the parameter search auto, it is updated, delete it
    } else {
      length_auto = IntAutomaton::makeInt(-1);
    }
    DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id_ << "]->lastIndexOf(" << search_auto->id_  << ")";
    return length_auto;
  }

  difference_auto = this->Difference(contains_auto);
  if (not difference_auto->IsEmptyLanguage()) {
    has_negative_1 = true;
  }
  delete difference_auto;

  last_index_of_auto = contains_auto->LastIndexOfHelper(search_param_auto);
  delete contains_auto; contains_auto = nullptr;

  length_auto = last_index_of_auto->Length();
  length_auto->setMinus1(has_negative_1);
  delete last_index_of_auto; last_index_of_auto = nullptr;

  // if search has empty string lastIndexOf also returns all string lengths
  if (search_has_empty_string) {
    IntAutomaton_ptr string_lengths = this->Length();
    IntAutomaton_ptr tmp = length_auto;
    length_auto = static_cast<IntAutomaton_ptr>(tmp->Union(string_lengths));
    delete string_lengths; string_lengths = nullptr;
    delete tmp; tmp = nullptr;
    delete search_param_auto; search_param_auto = nullptr; // search_param_auto auto is not the parameter search auto, it is updated, delete it
  }

  DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id_ << "]->lastIndexOf(" << search_auto->id_ << ")";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::Contains(StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr contains_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr, tmp_auto_2 = nullptr;

  any_string_auto = StringAutomaton::MakeAnyString();
  tmp_auto_1 = any_string_auto->Concat(search_auto);
  tmp_auto_2 = tmp_auto_1->Concat(any_string_auto);

  contains_auto = this->Intersect(tmp_auto_2);
  delete any_string_auto;
  delete tmp_auto_1; delete tmp_auto_2;

  DVLOG(VLOG_LEVEL) << contains_auto->id_ << " = [" << this->id_ << "]->contains(" << search_auto->id_ << ")";

  return contains_auto;
}

StringAutomaton_ptr StringAutomaton::Begins(StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr begins_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr;

  any_string_auto = StringAutomaton::MakeAnyString();
  tmp_auto_1 = search_auto->Concat(any_string_auto);

  begins_auto = this->Intersect(tmp_auto_1);

  DVLOG(VLOG_LEVEL) << begins_auto->id_ << " = [" << this->id_ << "]->begins(" << search_auto->id_ << ")";

  return begins_auto;
}

StringAutomaton_ptr StringAutomaton::Ends(StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr ends_auto = nullptr, any_string_auto = nullptr,
          tmp_auto_1 = nullptr;

  any_string_auto = StringAutomaton::MakeAnyString();
  tmp_auto_1 = any_string_auto->Concat(search_auto);

  ends_auto = this->Intersect(tmp_auto_1);

  DVLOG(VLOG_LEVEL) << ends_auto->id_ << " = [" << this->id_ << "]->ends(" << search_auto->id_ << ")";

  return ends_auto;
}

StringAutomaton_ptr StringAutomaton::ToUpperCase() {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr upper_case_dfa = nullptr;
  StringAutomaton_ptr upper_case_auto = nullptr;

  int var = this->num_of_bdd_variables_;
	int nvar = var+1;

	// dfa1 will have var+1 indices, with all valid transitions having extrabit=0
	DFA_ptr dfa1 = Automaton::DFAExtendExtrabit(this->dfa_,var);
	int *indices = Automaton::GetBddVariableIndices(nvar);

  upper_case_dfa = Automaton::dfaToUpperCase(dfa1, nvar, indices);
  DFA_ptr temp_dfa = Automaton::DFAProjectAway(upper_case_dfa,var);
  dfaFree(upper_case_dfa);

  upper_case_auto = new StringAutomaton(temp_dfa,var);


  DVLOG(VLOG_LEVEL) << upper_case_auto->id_ << " = [" << this->id_ << "]->toUpperCase()";

  return upper_case_auto;
}

StringAutomaton_ptr StringAutomaton::ToLowerCase() {
  CHECK_EQ(this->num_tracks_,1);
  DFA_ptr lower_case_dfa = nullptr;
  StringAutomaton_ptr lower_case_auto = nullptr;

  int var = this->num_of_bdd_variables_;
	int nvar = var+1;

	// dfa1 will have var+1 indices, with all valid transitions having extrabit=0
	DFA_ptr dfa1 = Automaton::DFAExtendExtrabit(this->dfa_,var);
	int *indices = Automaton::GetBddVariableIndices(nvar);

	lower_case_dfa = Automaton::dfaToLowerCase(dfa1, nvar, indices);

	DFA_ptr temp_dfa = Automaton::DFAProjectAway(lower_case_dfa,var);
	dfaFree(lower_case_dfa);
	lower_case_auto = new StringAutomaton(temp_dfa, var);

  DVLOG(VLOG_LEVEL) << lower_case_auto->id_ << " = [" << this->id_ << "]->toLowerCase()";

  return lower_case_auto;
}

StringAutomaton_ptr StringAutomaton::Trim() {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr trimmed_prefix_dfa = nullptr, trimmed_dfa = nullptr;
  StringAutomaton_ptr trimmed_auto = nullptr, trim_auto = nullptr;

  std::string trim_regex = "' '*";
  trim_auto = StringAutomaton::MakeRegexAuto(trim_regex, num_of_bdd_variables_);
  trimmed_prefix_dfa = StringAutomaton::TrimPrefix(this->dfa_,trim_auto->getDFA(),num_of_bdd_variables_);
  trimmed_dfa = StringAutomaton::TrimSuffix(trimmed_prefix_dfa, trim_auto->getDFA(), num_of_bdd_variables_);
  delete trim_auto;
  dfaFree(trimmed_prefix_dfa);

  trimmed_auto = new StringAutomaton(trimmed_dfa, num_of_bdd_variables_);

  DVLOG(VLOG_LEVEL) << trimmed_auto->id_ << " = [" << this->id_ << "]->trim()";

  return trimmed_auto;
}

StringAutomaton_ptr StringAutomaton::Replace(StringAutomaton_ptr search_auto,
		StringAutomaton_ptr replace_auto) {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr result_dfa = nullptr, temp_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr,temp_auto = nullptr;
  //LOG(FATAL) << "implement me";
  int var = this->num_of_bdd_variables_;
  int nvar = var+1;

	// dfa1 will have var+1 indices, with all valid transitions having extrabit=0
	DFA_ptr dfa1 = Automaton::DFAExtendExtrabit(this->dfa_,var);
	DFA_ptr dfa2 = Automaton::DFAExtendExtrabit(search_auto->dfa_,var);
	DFA_ptr dfa3 = Automaton::DFAExtendExtrabit(replace_auto->dfa_,var);

	int *indices = Automaton::GetBddVariableIndices(nvar+1);
  temp_dfa = dfa_general_replace_extrabit(dfa1, dfa2, dfa3,
          nvar, indices);
  dfaFree(dfa1);
  dfaFree(dfa2);
  dfaFree(dfa3);

  result_dfa = Automaton::DFAProjectAway(temp_dfa,var);
  dfaFree(temp_dfa);

  result_auto = new StringAutomaton(result_dfa, var);
  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->replace(" << search_auto->id_ << ", " << replace_auto->id_ << ")";
  return result_auto;
}

StringAutomaton_ptr StringAutomaton::GetAnyStringNotContainsMe() {
	CHECK_EQ(this->num_tracks_,1);
	StringAutomaton_ptr not_contains_auto = nullptr, any_string_auto = nullptr,
					contains_auto = nullptr, tmp_auto_1 = nullptr;

	any_string_auto = StringAutomaton::MakeAnyString();
	tmp_auto_1 = any_string_auto->Concat(this);
	contains_auto = tmp_auto_1->Concat(any_string_auto);
	delete tmp_auto_1; tmp_auto_1 = nullptr;
	delete any_string_auto; any_string_auto = nullptr;
	not_contains_auto = contains_auto->Complement();
	delete contains_auto; contains_auto = nullptr;

	DVLOG(VLOG_LEVEL) << not_contains_auto->id_ << " = [" << this->id_ << "]->getAnyStringNotContainsMe()";

	return not_contains_auto;
}

UnaryAutomaton_ptr StringAutomaton::ToUnaryAutomaton() {
	CHECK_EQ(this->num_tracks_,1);
  UnaryAutomaton_ptr unary_auto = nullptr;
  DFA_ptr unary_dfa = nullptr, tmp_dfa = nullptr;

  int sink_state = this->GetSinkState(),
          number_of_variables = num_of_bdd_variables_ + 1, // one extra bit
          to_state = 0;
  bool has_sink = true;
  int original_num_states = dfa_->ns;
  if(sink_state < 0) {
    has_sink = false;
    sink_state = 0;
  }

  int* indices = GetBddVariableIndices(number_of_variables);
  char* statuses = new char[original_num_states + 1];
  std::map<std::vector<char>*, int> exceptions;
  std::vector<char>* current_exception = nullptr;

  paths state_paths = nullptr, pp = nullptr;
  trace_descr tp = nullptr;


  dfaSetup(original_num_states, number_of_variables, indices);

  for (int i = 0; i < original_num_states; i++) {

    if(i == sink_state && has_sink) {
      dfaAllocExceptions(0);
      dfaStoreState(sink_state);
      statuses[sink_state] = '-';
      continue;
    }

    state_paths = pp = make_paths(dfa_->bddm, dfa_->q[i]);
    while (pp) {
      if (!has_sink || pp->to != (unsigned)sink_state) {
        to_state = pp->to;
        current_exception = new std::vector<char>();
        for (int j = 0; j < number_of_variables - 1; j++) {
          //the following for loop can be avoided if the indices are in order
          for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp= tp->next);

          if (tp) {
            if (tp->value){
              current_exception->push_back('1');
            } else{
              current_exception->push_back('0');
            }
          } else {
            current_exception->push_back('X');
          }
        }

        current_exception->push_back('1');
        current_exception->push_back('\0');
        exceptions[current_exception] = to_state;
      }
      current_exception = nullptr;
      tp = nullptr;
      pp = pp->next;
    }

    dfaAllocExceptions(exceptions.size());
    for (auto it = exceptions.begin(); it != exceptions.end();) {
      dfaStoreException(it->second, &*it->first->begin());
      current_exception = it->first;
      it = exceptions.erase(it);
      delete current_exception;
    }
    dfaStoreState(sink_state);
    current_exception = nullptr;
    exceptions.clear();

    if (dfa_->f[i] == 1) {
      statuses[i] = '+';
    } else if (dfa_->f[i] == -1) {
      statuses[i] = '-';
    } else {
      statuses[i] = '0';
    }

    kill_paths(state_paths);
    state_paths = pp = nullptr;
  }
  statuses[this->dfa_->ns] = '\0';
  unary_dfa = dfaBuild(statuses);
  //delete[] indices; indices = nullptr;
  delete[] statuses; statuses = nullptr;

  for (int i = 0; i < number_of_variables - 1; i++) { // project away all bits
    tmp_dfa = unary_dfa;
    unary_dfa = dfaProject(tmp_dfa,  (unsigned)i);
    dfaFree(tmp_dfa);
    tmp_dfa = unary_dfa;
    unary_dfa = dfaMinimize(tmp_dfa);
    dfaFree(tmp_dfa);
  }

  int* indices_map = CreateBddVariableIndices(number_of_variables);
  indices_map[number_of_variables - 1] = 0;
  dfaReplaceIndices(unary_dfa, indices_map);
  delete[] indices_map;

  // make sure no "dont care" states
  for(int i = 0; i < unary_dfa->ns; i++) {
    if(unary_dfa->f[i] == 0) {
      unary_dfa->f[i] = -1;
    }
  }

  unary_auto = new UnaryAutomaton(unary_dfa);
  DVLOG(VLOG_LEVEL) << unary_auto->getId() << " = [" << this->id_ << "]->toUnaryAutomaton()";
  return unary_auto;
}

IntAutomaton_ptr StringAutomaton::ParseToIntAutomaton() {
	CHECK_EQ(this->num_tracks_,1);
  IntAutomaton_ptr int_auto = nullptr;
  if (this->isCyclic()) {
    int_auto = IntAutomaton::makeIntGreaterThanOrEqual(0);
  } else if (this->IsEmptyLanguage()) {
    int_auto = IntAutomaton::makePhi();
  } else {
    using StatePaths = std::pair<int, std::vector<std::string>>;
    std::vector<std::string> paths_to_state;
    paths_to_state.push_back("");

    std::stack<StatePaths> dfs_stack;
    dfs_stack.push(std::make_pair(this->dfa_->s, paths_to_state));

    paths state_paths = nullptr, pp = nullptr;
    trace_descr tp = nullptr;
    int current_state;
    int sink_state = this->GetSinkState();


    std::map<int, std::vector<std::string>> current_paths_to_state; // <to state, paths>
    std::vector<char> current_exception;
    std::vector<char> decoded_exception;
    std::vector<int> int_values;

    if (IsAcceptingState(this->dfa_->s)) {
      int_values.push_back(0);
    }

    const int *indices = GetBddVariableIndices(num_of_bdd_variables_);

    while (not dfs_stack.empty()) {
      auto current_state_info = dfs_stack.top(); dfs_stack.pop();
      current_state = current_state_info.first;
      paths_to_state = current_state_info.second;

      state_paths = pp = make_paths(dfa_->bddm, dfa_->q[current_state]);
      while (pp) {
        if (pp->to != (unsigned)sink_state) {
          for (int j = 0; j < num_of_bdd_variables_; j++) {
            for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp= tp->next);
              if (tp) {
                if (tp->value){
                  current_exception.push_back('1');
                } else{
                  current_exception.push_back('0');
                }
              } else {
                current_exception.push_back('X');
              }
          }
          // update path
          decoded_exception = decodeException(current_exception);
          for (auto ch : decoded_exception) {
            for (auto p : paths_to_state) {
              current_paths_to_state[pp->to].push_back(p + ch);
            }
          }
        }
        current_exception.clear();
        tp = nullptr;
        pp = pp->next;
      }

      for (auto& entry : current_paths_to_state) {
        if (IsAcceptingState(entry.first)) {
          for (auto str_value : entry.second) {
            int_values.push_back(std::stoi(str_value));
          }
        }
        dfs_stack.push(std::make_pair(entry.first, entry.second));
      }

      kill_paths(state_paths);
      state_paths = pp = nullptr;
      current_paths_to_state.clear();
    }

    int_auto = IntAutomaton::makeInts(int_values);
  }

  DVLOG(VLOG_LEVEL) << int_auto->getId() << " = [" << this->id_ << "]->parseToIntAutomaton()";
  return int_auto;
}

IntAutomaton_ptr StringAutomaton::Length() {
	CHECK_EQ(this->num_tracks_,1);
  IntAutomaton_ptr length_auto = nullptr;
  if (this->IsEmptyLanguage()) {
    length_auto = IntAutomaton::makePhi(num_of_bdd_variables_);
  } else if (this->IsAcceptingSingleString()) {
    std::string example = this->GetAnAcceptingString();
    length_auto = IntAutomaton::makeInt(example.length(), num_of_bdd_variables_);
  } else {
    UnaryAutomaton_ptr unary_auto = this->ToUnaryAutomaton();
    length_auto = unary_auto->toIntAutomaton(num_of_bdd_variables_);
    delete unary_auto; unary_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL) << length_auto->getId() << " = [" << this->id_ << "]->length()";

  return length_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictLengthTo(int length) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr;
  StringAutomaton_ptr length_string_auto = StringAutomaton::MakeAnyStringLengthEqualTo(length);

  restricted_auto = this->Intersect(length_string_auto);
  delete length_string_auto; length_string_auto = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictLengthTo(" << length << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictLengthTo(IntAutomaton_ptr length_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(length_auto->getDFA(),length_auto->get_number_of_bdd_variables());

  restricted_auto = this->Intersect(length_string_auto);
  length_string_auto->dfa_ = nullptr;
  delete length_string_auto; length_string_auto = nullptr;
  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictLengthTo(" << length_auto->getId() << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictIndexOfTo(int index,StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->RestrictIndexOfTo(index_auto, search_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictIndexOfTo(IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr, contains_auto = nullptr,
          not_contains_length_auto = nullptr, not_contains_subject_auto = nullptr,
          tmp_auto_1 = nullptr, tmp_auto_2 = nullptr;

  bool has_negative_1 = index_auto->hasNegative1();

  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA(),index_auto->get_number_of_bdd_variables());
//  UnaryAutomaton_ptr unary_auto = index_auto->toUnaryAutomaton();
//	StringAutomaton_ptr length_string_auto = unary_auto->toStringAutomaton();
//	delete unary_auto;
  StringAutomaton_ptr any_string = StringAutomaton::MakeAnyString();

  contains_auto = any_string->Contains(search_auto);
  if (index_auto->hasNegative1()) {
    not_contains_subject_auto = this->Difference(contains_auto);
  }

  not_contains_length_auto = length_string_auto->Difference(contains_auto);
  delete contains_auto; contains_auto = nullptr;
  length_string_auto->dfa_ = nullptr;
  delete length_string_auto; length_string_auto = nullptr;

  tmp_auto_1 = not_contains_length_auto->Concat(search_auto);
  tmp_auto_2 = tmp_auto_1->Concat(any_string);
  delete not_contains_length_auto; not_contains_length_auto = nullptr;
  delete tmp_auto_1; tmp_auto_1 = nullptr;
  delete any_string; any_string = nullptr;

  restricted_auto = this->Intersect(tmp_auto_2);
  delete tmp_auto_2; tmp_auto_2 = nullptr;

  if (not_contains_subject_auto not_eq nullptr) {
    tmp_auto_1 = restricted_auto;
    restricted_auto = tmp_auto_1->Union(not_contains_subject_auto);
    delete tmp_auto_1; tmp_auto_1 = nullptr;
    delete not_contains_subject_auto; not_contains_subject_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictIndexOfTo(" << index_auto->getId() << ", " << search_auto->id_ << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictLastIndexOfTo(int index,
		StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->RestrictLastIndexOfTo(index_auto, search_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictLastIndexOfTo(
		IntAutomaton_ptr index_auto, StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr, contains_auto = nullptr,
          not_contains_auto = nullptr, not_contains_subject_auto = nullptr,
          tmp_auto_1 = nullptr, tmp_auto_2 = nullptr;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA(),index_auto->get_number_of_bdd_variables());
  //UnaryAutomaton_ptr unary_auto = index_auto->toUnaryAutomaton();
	//StringAutomaton_ptr length_string_auto = unary_auto->toStringAutomaton();
	//delete unary_auto;
  StringAutomaton_ptr any_string = StringAutomaton::MakeAnyString();

  contains_auto = any_string->Contains(search_auto);
  if (index_auto->hasNegative1()) {
    not_contains_subject_auto = this->Difference(contains_auto);
  }
  not_contains_auto = any_string->Difference(contains_auto);

  delete contains_auto; contains_auto = nullptr;
  delete any_string; any_string = nullptr;

  tmp_auto_1 = length_string_auto->Concat(search_auto);
  tmp_auto_2 = tmp_auto_1->Concat(not_contains_auto);
  length_string_auto->dfa_ = nullptr;
  delete length_string_auto; length_string_auto = nullptr;
  delete tmp_auto_1; tmp_auto_1 = nullptr;
  delete not_contains_auto; not_contains_auto = nullptr;

  restricted_auto = this->Intersect(tmp_auto_2);
  delete tmp_auto_2; tmp_auto_2 = nullptr;

  if (not_contains_subject_auto not_eq nullptr) {
    tmp_auto_1 = restricted_auto;
    restricted_auto = tmp_auto_1->Union(not_contains_subject_auto);
    delete tmp_auto_1; tmp_auto_1 = nullptr;
    delete not_contains_subject_auto; not_contains_subject_auto = nullptr;
  }

  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictLastIndexOfTo(" << index_auto->getId() << ", " << search_auto->id_ << ")";

  return restricted_auto;
}

/**
 * Given search auto s, finds Intersection with
 * s . (Sigma - s)*
 *
 */
StringAutomaton_ptr StringAutomaton::RestrictLastOccuranceOf(
		StringAutomaton_ptr search_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr, contains_auto = nullptr,
          not_contains_auto = nullptr, tmp_auto_1 = nullptr;
  StringAutomaton_ptr any_string = StringAutomaton::MakeAnyString();

  contains_auto = any_string->Contains(search_auto);
  not_contains_auto = any_string->Difference(contains_auto);

  delete contains_auto; contains_auto = nullptr;
  delete any_string; any_string = nullptr;


  tmp_auto_1 = search_auto->Concat(not_contains_auto);
  delete not_contains_auto; not_contains_auto = nullptr;
  delete any_string; any_string = nullptr;

  restricted_auto = this->Intersect(tmp_auto_1);
  delete tmp_auto_1; tmp_auto_1 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictLastOccuranceTo(" << search_auto->id_ << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictFromIndexToEndTo(int index,
		StringAutomaton_ptr sub_string_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->RestrictFromIndexToEndTo(index_auto, sub_string_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictFromIndexToEndTo(
		IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr, tmp_auto_1 = nullptr, tmp_auto_2;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA(),index_auto->get_number_of_bdd_variables());
//  UnaryAutomaton_ptr unary_auto = index_auto->toUnaryAutomaton();
//	StringAutomaton_ptr length_string_auto = unary_auto->toStringAutomaton();
//	delete unary_auto;

  tmp_auto_1 = length_string_auto->Concat(sub_string_auto);
  length_string_auto->dfa_ = nullptr;
  delete length_string_auto; length_string_auto = nullptr;

  restricted_auto = this->Intersect(tmp_auto_1);
  delete tmp_auto_1; tmp_auto_1 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictFromIndexToEndTo(" << index_auto->getId() << ", " << sub_string_auto->id_ << ")";

  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictAtIndexTo(int index,
		StringAutomaton_ptr sub_string_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr;
  IntAutomaton_ptr index_auto = nullptr;
  index_auto = IntAutomaton::makeInt(index);
  restricted_auto = this->RestrictAtIndexTo(index_auto, sub_string_auto);
  delete index_auto; index_auto = nullptr;
  return restricted_auto;
}

StringAutomaton_ptr StringAutomaton::RestrictAtIndexTo(
		IntAutomaton_ptr index_auto, StringAutomaton_ptr sub_string_auto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr restricted_auto = nullptr, tmp_auto_1 = nullptr, tmp_auto_2;
  StringAutomaton_ptr length_string_auto = new StringAutomaton(index_auto->getDFA(),index_auto->get_number_of_bdd_variables());
//  UnaryAutomaton_ptr unary_auto = index_auto->toUnaryAutomaton();
//  StringAutomaton_ptr length_string_auto = unary_auto->toStringAutomaton();
//  delete unary_auto;
  StringAutomaton_ptr any_string = StringAutomaton::MakeAnyString();

  tmp_auto_1 = length_string_auto->Concat(sub_string_auto);
  if (tmp_auto_1->IsEmptyString()) {
    // restricting string to be an empty string, a special case for index 0 and sub_string_auto is empty
    tmp_auto_2 = tmp_auto_1->clone();
  } else {
    tmp_auto_2 = tmp_auto_1->Concat(any_string);
  }
  length_string_auto->dfa_ = nullptr; // it is index_auto's dfa

  delete length_string_auto; length_string_auto = nullptr;
  delete tmp_auto_1; tmp_auto_1 = nullptr;
  delete any_string; any_string = nullptr;
  restricted_auto = this->Intersect(tmp_auto_2);
  delete tmp_auto_2; tmp_auto_2 = nullptr;

  DVLOG(VLOG_LEVEL) << restricted_auto->id_ << " = [" << this->id_ << "]->restrictIndexTo(" << index_auto->getId() << ", " << sub_string_auto->id_ << ")";

  return restricted_auto;
}

/**
 * TODO Efficiency of the pre image computations can be improved
 * if they are guided by the post image values
 */
StringAutomaton_ptr StringAutomaton::PreToUpperCase(StringAutomaton_ptr rangeAuto) {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  int var = this->num_of_bdd_variables_;
	int nvar = var+1;

	// dfa1 will have var+1 indices, with all valid transitions having extrabit=0
	DFA_ptr dfa1 = Automaton::DFAExtendExtrabit(this->dfa_,var);
	int *indices = Automaton::GetBddVariableIndices(nvar);

  result_dfa = Automaton::dfaPreToUpperCase(dfa1,nvar,indices);
	DFA_ptr temp_dfa = Automaton::DFAProjectAway(result_dfa,var);
	dfaFree(result_dfa);


  result_auto = new StringAutomaton(temp_dfa,var);

  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->Intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->preToUpperCase()";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::PreToLowerCase(StringAutomaton_ptr rangeAuto) {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr result_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  int var = this->num_of_bdd_variables_;
	int nvar = var+1;
  DFA_ptr dfa1 = Automaton::DFAExtendExtrabit(this->dfa_,var);
	int *indices = Automaton::GetBddVariableIndices(nvar);

  result_dfa = dfaPreToLowerCase(dfa1,nvar,indices);


	DFA_ptr temp_dfa = Automaton::DFAProjectAway(result_dfa,var);
	dfaFree(result_dfa);

  result_auto = new StringAutomaton(temp_dfa,var);

  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->Intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->preToLowerCase()";

  return result_auto;
}

// CHECK WITH BAKI
// may be wrong
StringAutomaton_ptr StringAutomaton::PreTrim(StringAutomaton_ptr rangeAuto) {
	CHECK_EQ(this->num_tracks_,1);
  StringAutomaton_ptr result_auto = nullptr, trim_auto = nullptr, temp_auto = nullptr;

  std::string trim_regex = "' '*";
  trim_auto = StringAutomaton::MakeRegexAuto(trim_regex);

  result_auto = this->Concat(trim_auto);
  temp_auto = trim_auto->Concat(result_auto);
  delete result_auto;
  result_auto = temp_auto->Intersect(rangeAuto);
  delete trim_auto;
  delete temp_auto;

  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->preTrim()";
  return result_auto;
}

StringAutomaton_ptr StringAutomaton::PreConcatLeft(
		StringAutomaton_ptr right_auto) {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr d1,d2,d3;
  d1 = this->dfa_;
  d2 = right_auto->getDFA();
  d3 = StringAutomaton::PreConcatPrefix(d1,d2,8);
  return new StringAutomaton(d3,DEFAULT_NUM_OF_VARIABLES);
}

/**
 * Fix preconcat issue for rectangle start state representation in to dot
 */
StringAutomaton_ptr StringAutomaton::PreConcatRight(
		StringAutomaton_ptr left_auto) {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr d1,d2,d3;
  d1 = this->dfa_;
  d2 = left_auto->getDFA();
  d3 = StringAutomaton::PreConcatSuffix(d1,d2,8);
  return new StringAutomaton(d3,DEFAULT_NUM_OF_VARIABLES);
}

StringAutomaton_ptr StringAutomaton::PreReplace(StringAutomaton_ptr searchAuto,
		std::string replaceString, StringAutomaton_ptr rangeAuto) {
	CHECK_EQ(this->num_tracks_,1);
  DFA_ptr result_dfa = nullptr, temp_dfa = nullptr;
  StringAutomaton_ptr result_auto = nullptr;

  std::vector<char> replaceStringVector(replaceString.begin(), replaceString.end());
  replaceStringVector.push_back('\0');

  int var = this->num_of_bdd_variables_;
  int nvar = var+1;

  DFA_ptr dfa1 = Automaton::DFAExtendExtrabit(this->dfa_,var);
	DFA_ptr dfa2 = Automaton::DFAExtendExtrabit(searchAuto->dfa_,var);
  int *indices = GetBddVariableIndices(nvar+1); // +1 for libstranger stuff
  temp_dfa = dfa_pre_replace_str(dfa1,dfa2, &replaceStringVector[0],
      nvar, indices);

  dfaFree(dfa1);
  dfaFree(dfa2);
  // project away the extra bit
  result_dfa = DFAProjectAway(temp_dfa,var);
  dfaFree(temp_dfa);
  result_auto = new StringAutomaton(result_dfa,1,var);
  if (rangeAuto not_eq nullptr) {
    StringAutomaton_ptr tmp_auto = result_auto;
    result_auto = tmp_auto->Intersect(rangeAuto);
    delete tmp_auto;
  }

  DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->preReplace(" << searchAuto->id_ << ", " << replaceString << ")";

  return result_auto;
}

StringAutomaton_ptr StringAutomaton::GetAutomatonForVariable(std::string var_name) {
	if(formula_ == nullptr) {
		LOG(FATAL) << "No String formula!";
	}

	int track = formula_->GetVariableIndex(var_name);
	StringAutomaton_ptr result_auto = GetKTrack(track);
	auto result_formula = new StringFormula();
	result_formula->SetType(StringFormula::Type::VAR);
	result_formula->AddVariable(var_name,1);
	result_auto->SetFormula(result_formula);
	DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->GetAutomatonForVariable(" << var_name << ")";
	return result_auto;
}

// handle case where only 1 track, but make sure correct # of variables
StringAutomaton_ptr StringAutomaton::GetKTrack(int k_track) {
  DFA_ptr res = this->dfa_, temp;
	StringAutomaton_ptr result_auto = nullptr;

	if(k_track >= this->num_tracks_) {
		LOG(FATAL) << "error in StringAutomaton::GetKTrack; k_track,num_tracks = " << k_track << "," << this->num_tracks_;
	} else if(this->num_tracks_ == 1) {
		// TODO baki: added below for charat example
		if(this->num_of_bdd_variables_ > DEFAULT_NUM_OF_VARIABLES) {
			temp = TrimLambdaSuffix(res,VAR_PER_TRACK,false);
      res = temp;
      temp = TrimLambdaPrefix(res, VAR_PER_TRACK);
      dfaFree(res);
      res = temp;
      result_auto = new StringAutomaton(res,DEFAULT_NUM_OF_VARIABLES);
		} else {
			result_auto = this->clone();
		}
		return result_auto;
	}

	// k_track needs to be mapped to indices 0-(VAR_PER_TRACK-1)
	// while all others need to be pushed back by VAR_PER_TRACK, then
	// interleaved with 1 less than current number of tracks
  
  
	int* map = CreateBddVariableIndices(this->num_tracks_*VAR_PER_TRACK);
	std::vector<int> indices;
	for(int i = 0; i < this->num_tracks_; i++) {
		int shift = (i > k_track ? i-1 : i);
		if(i == k_track) {
			for(int k = 0; k < VAR_PER_TRACK; k++) {
				map[i+this->num_tracks_*k] = k;
			}
		} else {
			for(int k = 0; k < VAR_PER_TRACK; k++) {
				map[i+this->num_tracks_*k] = VAR_PER_TRACK + shift +(this->num_tracks_-1)*k;
			}
		}
	}

	for(int i = 0; i < this->num_tracks_; ++i) {
		if(i != k_track) {
			for(int j = 0; j < VAR_PER_TRACK; ++j) {
				indices.push_back(i+this->num_tracks_*j);
			}
		}
	}

	std::vector<int> _map;
	for(int i = 0; i < this->num_tracks_*VAR_PER_TRACK; i++) {
		_map.push_back(map[i]);
	}

  auto result = Automaton::DFAProjectAway(res,_map,indices);

  if(find_sink(result) != -1) {
		// trim prefix first, then suffix
		temp = TrimLambdaSuffix(result,VAR_PER_TRACK,false);
		dfaFree(result);
		result = temp;
		temp = TrimLambdaPrefix(result, VAR_PER_TRACK);
		dfaFree(result);
		result = temp;
    result_auto = new StringAutomaton(result,DEFAULT_NUM_OF_VARIABLES);
	} else {
		DVLOG(VLOG_LEVEL) << "No sink found while getting single track from multi-track, returning any string";
		dfaFree(result);
		result_auto = StringAutomaton::MakeAnyString();
	}

  //LOG(INFO) << "Done";
	delete[] map;
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::ProjectAwayVariable(std::string var_name) {
	if(formula_ == nullptr) {
		LOG(FATAL) << "No String formula!";
	}
	int track = formula_->GetVariableIndex(var_name);
	StringAutomaton_ptr result_auto = ProjectKTrack(track);
	auto result_formula = formula_->clone();
	result_formula->RemoveVariable(var_name);
	result_auto->SetFormula(result_formula);
	DVLOG(VLOG_LEVEL) << result_auto->id_ << " = [" << this->id_ << "]->ProjectAwayVariable(" << var_name << ")";
	return result_auto;
}

StringAutomaton_ptr StringAutomaton::ProjectKTrack(int k_track) {
  /*
   * If there are only two tracks, use GetKTrack instead,
   * since it takes care of lambdas
   */
  if(num_tracks_ == 2) {
    StringAutomaton_ptr result = nullptr;
    if(k_track == 0) {
      result = GetKTrack(1);
    } else {
      result = GetKTrack(0);
    }
    return result;
  }
  std::vector<int> indices;
  int *map = CreateBddVariableIndices(this->num_tracks_*VAR_PER_TRACK);
  for(int i = 0,k=0,l=0; i < this->num_of_bdd_variables_; i++) {
    if(i == k_track+l*this->num_tracks_) {
        map[i] = (this->num_tracks_-1)*VAR_PER_TRACK+l;
        l++;
        continue;
    }
    map[i] = k++;
  }

  std::vector<int> _map;
  for(int i = 0; i < this->num_tracks_*VAR_PER_TRACK; i++) {
  	_map.push_back(map[i]);
  }
  for(int i = 0; i < VAR_PER_TRACK; i++) {
  	indices.push_back(k_track+num_tracks_*i);
  }

  auto result_dfa = Automaton::DFAProjectAway(dfa_,_map,indices);
  auto result_auto = new StringAutomaton(result_dfa,num_tracks_-1,(num_tracks_-1)*VAR_PER_TRACK);
  if(formula_ != nullptr) {
  	result_auto->SetFormula(formula_->clone());
  }
  delete[] map;
  return result_auto;
}

void StringAutomaton::SetSymbolicCounter() {
	// normal symbolic counter for single-track
	if(num_tracks_ == 1) {
		Automaton::SetSymbolicCounter();
		return;
	}


	// remove last lambda loop
	DFA_ptr original_dfa = nullptr, temp_dfa = nullptr,trimmed_dfa = nullptr;
	original_dfa = this->dfa_;
	trace_descr tp;
	paths state_paths,pp;
	int sink = find_sink(original_dfa);
	if(sink < 0) {
		LOG(FATAL) << "Cant count, no sink!";
	}
	int var = VAR_PER_TRACK;
	int len = var * num_tracks_;
	int* mindices = GetBddVariableIndices(len);
	char* statuses = new char[original_dfa->ns+1];
	std::vector<std::pair<std::vector<char>,int>> state_exeps;
	std::vector<bool> lambda_states(original_dfa->ns,false);
	dfaSetup(original_dfa->ns,len,mindices);
	for(int i = 0; i < original_dfa->ns; i++) {
		statuses[i] = '-';
		state_paths = pp = make_paths(original_dfa->bddm, original_dfa->q[i]);
		while(pp) {
			if(pp->to == sink) {
				pp = pp->next;
				continue;
			}

			std::vector<char> exep(len,'X');
			for(int j = 0; j < len; j++) {
				for(tp = pp->trace; tp && (tp->index != mindices[j]); tp= tp->next);
				if(tp) {
					if(tp->value) exep[j] = '1';
					else exep[j] = '0';
				}
				else exep[j] = 'X';
			}

			// if lambda and loops back, dont add it
			bool is_lambda = true;
			for(int k = 0; k < len; k++) {
				if(exep[k] != '1' && exep[k] != 'X') {
					is_lambda = false;
					break;
				}
			}

			if(is_lambda) {
				lambda_states[pp->to] = true;
				if(!lambda_states[i] || i == pp->to) {
					statuses[i] = '+';
				} 
			} else {
				exep.push_back('\0');
				state_exeps.push_back(std::make_pair(exep,pp->to));
			}
			pp = pp->next;
		}
		kill_paths(state_paths);
		dfaAllocExceptions(state_exeps.size());
		for(int k = 0; k < state_exeps.size(); k++) {
			dfaStoreException(state_exeps[k].second, &state_exeps[k].first[0]);
		}
		dfaStoreState(sink);
		state_exeps.clear();
	}
	statuses[original_dfa->ns] = '\0';
	temp_dfa = dfaBuild(statuses);
	trimmed_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);
	//delete[] mindices;
	delete[] statuses;

	this->dfa_ = trimmed_dfa;
	Automaton::SetSymbolicCounter();
	this->dfa_ = original_dfa;
	dfaFree(trimmed_dfa);
}

std::vector<std::string> StringAutomaton::GetAnAcceptingStringForEachTrack() {
	LOG(FATAL) << "IMPLEMENT ME";
//  std::vector<std::string> strings(num_tracks_, "");
//  std::vector<bool>* example = getAnAcceptingWord();
//  unsigned char c = 0;
//  unsigned num_transitions = example->size() / num_of_bdd_variables_;
//  bool bit;
//  unsigned sharp1 = 254, sharp2 = 255;
//
//  for(int t = 0; t < num_transitions; t++) {
//    unsigned offset = t*num_of_bdd_variables_;
//    for (int i = 0; i < num_tracks_; i++) {
//      for (int j = 0; j < VAR_PER_TRACK; j++) {
//        bit = (*example)[offset+i+num_tracks_*j];
//        if(bit) {
//          c |= 1;
//        } else {
//          c |= 0;
//        }
//        if(j != VAR_PER_TRACK-1) {
//          c <<= 1;
//        }
//      }
//      if(c != sharp1 && c != sharp2) strings[i] += c;
//      c = 0;
//    }
//  }
//  delete example;
//  return strings;
}

std::map<std::string,std::vector<std::string>> StringAutomaton::GetModelsWithinBound(int num_models, int bound) {
	// if not multitrack, use parent automaton version
	if(this->num_tracks_ == 1) {
		return Automaton::GetModelsWithinBound(num_models,bound);
	}

	if(bound == -1 and num_models == -1) {
		LOG(FATAL) << "both bound and num_models cant be -1";
	} else if(bound == -1) {
		auto counter = GetSymbolicCounter();
		bound = counter.GetMinBound(num_models);
	}

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
			distances[final]--; // account for lambda/lambda transition
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
  //LOG(INFO) << "Done computing shortest paths to final state";

  // assume num_tracks > 1; Otherwise, juse call normal version
  int models_so_far = 0;
  int num_tracks = this->num_tracks_;
  int var_per_track = this->num_of_bdd_variables_ / num_tracks;

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
				// put loops first, other states at back
				if(to_state != current_state) {
					next_states_matrix[i].push_back(std::make_pair(to_state, current_transition));
				} else {
					next_states_matrix[i].insert(next_states_matrix[i].begin(),std::make_pair(to_state,current_transition));
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

      // check if its final state
      // since we're assuming we have lambda transitions, transitions to final states must be all lambda transitions
      // therefor, if to_state is a final state, and the current_length is <= bound, then we record the previous track_characters
      // and don't new transitions!
      if(this->dfa_->f[to_state] == 1) {
        if((count_bound_exact_ and length == bound) or (not count_bound_exact_ and length <= bound)) {
          
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
            max_x += num_x;
          }

          // for each 'X', there are 2 possible transitions
          models_so_far += (1 << max_x);
          unfinished_models.insert(current_model.second);
          // set finish condition if necessary
          if(num_models != -1 and models_so_far >= num_models) {
            get_more_models = false;
          }
        }
      } else if(to_state != sink and (length < bound or bound == -1)) {
        std::vector<char> transition = iter.second;
        
        // transition is in second position
        track_characters = current_model.second;
        for(int i = 0; i < num_tracks; i++) {
          for(int k = 0; k < var_per_track; k++) {
            // since tracks are interleaved, track i's characters don't lie in order in the transition we got
            track_characters[i].push_back(transition[i+num_tracks*k]);
          }
        }
        
        models_to_process.push(std::make_pair(to_state,track_characters));
      }
    }
  }


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

  std::set<std::vector<std::string>> printable_models;
  for(auto iter : finished_models) {

  	std::vector<std::string> model(iter.size());
  	for(int i = 0; i < iter.size(); i++) {
  		std::string s;
			unsigned int length = iter[i].size() / var_per_track;
			for(int k = 0; k < length; k++) {
				// if lambda, go on
				if(iter[i][((k+1)*var_per_track)-1] == true) {
					continue;
				}
				unsigned char c = 0;
				// var_per_track-1 since we dont' care about the last bit, which is used for lambda
				for(int j = 0; j < var_per_track-1; j++) {
					if(iter[i][(k*var_per_track)+j]) {
						c |= 1;
					} else {
						c |= 0;
					}
					if(j != 7) {
						c <<= 1;
					}
				}
//				char c_arr[4];
//				charToAscii(c_arr,c);
//				s += c_arr;
				s += std::to_string((int)c);
				s += " ";

			}
			model[i] = s;
  	}
  	printable_models.insert(model);
  }

  auto formula = this->formula_;
  if(formula == nullptr) {
  	LOG(FATAL) << "Formula not set!";
  }
  auto var_coeffs = formula->GetVariableCoefficientMap();
  std::map<std::string,std::vector<std::string>> variable_values;
//  for(auto iter : var_coeffs) {
//  	variable_values[iter.first] = std::vector<std::string>();
//  }
  variable_values["var_8"] = std::vector<std::string>();
  variable_values["var_7"] = std::vector<std::string>();
  variable_values["var_6"] = std::vector<std::string>();



  for(auto iter : printable_models) {
  	for(int i = 0; i < iter.size(); i++) {
  		// i corresponds to track, iter[i] is track value (string)
  		std::string var_name;
  		if(i == 0) {
  			var_name = "var_8";
  		} else if(i == 2) {
  			var_name = "var_7";
  		} else if(i == 1) {
  			var_name = "var_6";
  		}


  		//std::string var_name = formula->GetVariableAtIndex(i);
  		variable_values[var_name].push_back(iter[i]);
  	}
  }



  return variable_values;
}

int StringAutomaton::GetNumTracks() const {
  return num_tracks_;
}

bool StringAutomaton::HasEmptyString() {
  CHECK_EQ(this->num_tracks_,1);
  return IsInitialStateAccepting();
}

bool StringAutomaton::IsEmptyString() {
  CHECK_EQ(this->num_tracks_,1);
  return IsOnlyAcceptingEmptyInput();
}

bool StringAutomaton::IsAcceptingSingleString() {
  CHECK_EQ(this->num_tracks_,1);
  return isAcceptingSingleWord();
}

std::string StringAutomaton::GetAnAcceptingString() {
  CHECK_EQ(this->num_tracks_,1);
  std::stringstream ss;

  auto readable_ascii_heuristic = [](unsigned& index) -> bool {
    switch (index) {
      case 1:
      case 2:
      case 6:
        return true;
      default:
        return false;
    }
  };
  std::vector<bool>* example = getAnAcceptingWord(readable_ascii_heuristic);
  unsigned char c = 0;
  unsigned bit_range = num_of_bdd_variables_ - 1;
  unsigned read_count = 0;
  for (auto bit: *example) {
    if (bit) {
      c |= 1;
    } else {
      c |= 0;
    }

    if (read_count < (bit_range)) {
      c <<= 1;
    }
    if (read_count == bit_range) {
      ss << c;
      c = 0;
      read_count = 0;
    } else {
      read_count++;
    }
  }
  delete example;
  return ss.str();
}

StringFormula_ptr StringAutomaton::GetFormula() {
  return formula_;
}

void StringAutomaton::SetFormula(StringFormula_ptr formula) {
  if(formula_ != nullptr) {
    delete formula_;
  }
  formula_ = formula;
}

const StringAutomaton::TransitionVector& StringAutomaton::GenerateTransitionsForRelation(StringFormula::Type type, int bits_per_var) {
  bits_per_var--;
  // check table for precomputed value first
  std::pair<int,StringFormula::Type> key(bits_per_var,type);
  if(TRANSITION_TABLE.find(key) != TRANSITION_TABLE.end()) {
    return TRANSITION_TABLE[key];
  }

  // not previously computed; compute now and cache for later.
  bool final_states[3] = {false,false,false};
  switch(type) {
    case StringFormula::Type::EQ:
    case StringFormula::Type::EQ_CHARAT:
      final_states[0] = true;
      break;
    case StringFormula::Type::NOTEQ:
    case StringFormula::Type::NOTEQ_CHARAT:
    	final_states[1] = true;
      final_states[2] = true;
      break;
    case StringFormula::Type::LT:
    case StringFormula::Type::LT_CHARAT:
      final_states[1] = true;
      break;
    case StringFormula::Type::LE:
    case StringFormula::Type::LE_CHARAT:
      final_states[0] = true;
      final_states[1] = true;
      break;
    case StringFormula::Type::GT:
    case StringFormula::Type::GT_CHARAT:
      final_states[2] = true;
      break;
    case StringFormula::Type::GE:
    case StringFormula::Type::GE_CHARAT:
      final_states[0] = true;
      final_states[2] = true;
      break;
    default:
      LOG(FATAL) << "Invalid relation ordering type";
      break;
  }

  std::vector<std::map<std::string,int>> states(3, std::map<std::string, int>());
  states[0]["00"] = 0;
  states[0]["01"] = 1;
  states[0]["10"] = 2;
  states[0]["11"] = 0;

  states[1]["XX"] = 1;
  states[2]["XX"] = 2;

  TransitionVector good_trans;
  std::queue<std::pair<int,std::pair<std::string,std::string>>> next;
  next.push(std::make_pair(0,std::make_pair("","")));

  while(!next.empty()) {
    std::pair<int,std::pair<std::string,std::string>> curr = next.front();
    if(curr.second.first.size() >= bits_per_var) {
      if(final_states[curr.first]) {
        // append lambda bit for multitrack lambda
        curr.second.first += '0';
        curr.second.second += '0';
        good_trans.push_back(curr.second);
      }
    } else {
      for(auto& t : states[curr.first]) {
        next.push(std::make_pair(
            t.second,
            std::make_pair(
                curr.second.first + std::string(1,t.first[0]),
                curr.second.second + std::string(1,t.first[1]))));
      }
    }
    next.pop();
  }

  // cache the transitions for later
  TRANSITION_TABLE[key] = good_trans;

  return TRANSITION_TABLE[key];
}

DFA_ptr StringAutomaton::MakeBinaryRelationDfa(StringFormula::Type type, int bits_per_var, int num_tracks, int left_track, int right_track) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr, aligned_dfa = nullptr;
  int var = bits_per_var;
  int len = num_tracks * var;
  int *mindices = GetBddVariableIndices(num_tracks*var);
  int eq = 0,
      left = 1,
      right = 2,
      sink = 3;
  char statuses[5] = {"----"};
  std::vector<std::pair<std::vector<char>,int>> exeps;
  TransitionVector tv_eq, tv_left, tv_right;
  tv_eq = GenerateTransitionsForRelation(StringFormula::Type::EQ,bits_per_var);
  tv_left = GenerateTransitionsForRelation(StringFormula::Type::LT,bits_per_var);
  tv_right = GenerateTransitionsForRelation(StringFormula::Type::GT,bits_per_var);

  switch(type) {
    case StringFormula::Type::EQ:
      statuses[eq] = '+';
      break;
    case StringFormula::Type::NOTEQ:
      statuses[left] = '+';
      statuses[right] = '+';
      break;
    case StringFormula::Type::LT:
      statuses[left] = '+';
      break;
    case StringFormula::Type::LE:
      statuses[eq] = '+';
      statuses[left] = '+';
      break;
    case StringFormula::Type::GT:
      statuses[right] = '+';
      break;
    case StringFormula::Type::GE:
      statuses[eq] = '+';
      statuses[right] = '+';
      break;
    default:
      LOG(FATAL) << "Invalid stringrelation type! can't make dfa...";
      return nullptr;
  }

  for(auto& t : tv_eq) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = t.first[k];
      str[right_track+num_tracks*k] = t.second[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,eq));
  }

  for(auto& t : tv_left) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = t.first[k];
      str[right_track+num_tracks*k] = t.second[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,left));
  }

  for(auto& t : tv_right) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = t.first[k];
      str[right_track+num_tracks*k] = t.second[k];
    }
    str.push_back('\0');
    exeps.push_back(std::make_pair(str,right));
  }

  std::vector<char> str(len,'X');
  for(int k = 0; k < var; k++) {
    str[left_track+num_tracks*k] = '1';
    str[right_track+num_tracks*k] = '1';
  }
  str.push_back('\0');
  exeps.push_back(std::make_pair(str,eq));

  for(int k = 0; k < var-1; k++) {
    str[left_track + num_tracks * k] = 'X';
    str[right_track+ num_tracks * k] = '1';
  }
  str[left_track+num_tracks*(var-1)] = '0';
  str[right_track+num_tracks*(var-1)] = '1';
  exeps.push_back(std::make_pair(str,right));

  for(int k = 0; k < var-1; k++) {
    str[left_track + num_tracks * k] = '1';
    str[right_track+ num_tracks * k] = 'X';
  }
  str[left_track+num_tracks*(var-1)] = '1';
  str[right_track+num_tracks*(var-1)] = '0';
  exeps.push_back(std::make_pair(str,left));


  dfaSetup(4,len,mindices);
  dfaAllocExceptions(exeps.size());
  for(int i = 0; i < exeps.size(); i++) {
    dfaStoreException(exeps[i].second, &(exeps[i].first)[0]);
  }
  dfaStoreState(sink);
  exeps.clear();

  dfaAllocExceptions(0);
  dfaStoreState(left);

  dfaAllocExceptions(0);
  dfaStoreState(right);

  // sink
  dfaAllocExceptions(0);
  dfaStoreState(sink);

  // build it!
  temp_dfa = dfaBuild(statuses);
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);

  aligned_dfa = MakeBinaryAlignedDfa(left_track,right_track,num_tracks);
  temp_dfa = dfaProduct(result_dfa,aligned_dfa,dfaAND);

  dfaFree(result_dfa);
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  dfaFree(aligned_dfa);

  return result_dfa;
}

DFA_ptr StringAutomaton::MakeBinaryAlignedDfa(int left_track, int right_track, int num_tracks) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  TransitionVector tv;
  int init = 0,lambda_star = 1, lambda_lambda = 2,
      star_lambda = 3, sink = 4;
  int var = VAR_PER_TRACK;
  int len = num_tracks * var;
  int *mindices = GetBddVariableIndices(num_tracks*var);
  std::vector<char> exep_lambda(var,'1');
  std::vector<char> exep_dont_care(var,'X');
  exep_dont_care[var-1] = '0';
  tv = GenerateTransitionsForRelation(StringFormula::Type::EQ,var);

  dfaSetup(5,len,mindices);

  // ---- init state
  // if lambda/star goto lambda_star,
  // if star/lambda goto star_lambda,
  // if lambda_lambda goto lambda_lambda,
  // if star/star, loop
  // else, sink

  std::vector<char> str(len,'X');
  str.push_back('\0');

  dfaAllocExceptions(4);
  // x,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_dont_care[i];
    str[right_track+num_tracks*i] = exep_dont_care[i];
  }
  dfaStoreException(init, &str[0]);

  // x,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_dont_care[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(star_lambda, &str[0]);

  // lambda,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_dont_care[i];
  }
  dfaStoreException(lambda_star, &str[0]);

  //lambda,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- lambda_star state ----

  dfaAllocExceptions(2);
  // lambda,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_dont_care[i];
  }
  dfaStoreException(lambda_star, &str[0]);
  //lambda,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- lambda_lambda state ----

  dfaAllocExceptions(1);
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- star_lambda state ----

  dfaAllocExceptions(2);
  // lambda,x
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_dont_care[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(star_lambda, &str[0]);
  //lambda,lambda
  for(int i = 0; i < var; i++) {
    str[left_track+num_tracks*i] = exep_lambda[i];
    str[right_track+num_tracks*i] = exep_lambda[i];
  }
  dfaStoreException(lambda_lambda, &str[0]);
  dfaStoreState(sink);

  // ---- sink state -----

  dfaAllocExceptions(0);
  dfaStoreState(sink);

  temp_dfa = dfaBuild("--+--");
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);

  return result_dfa;
}

// Only supports charAt(x,i) OP charAt(y,i) where i is constant integer,
// OP in {<,>,<=,>=,=,!=}
DFA_ptr StringAutomaton::MakeRelationalCharAtDfa(StringFormula_ptr formula, int bits_per_var, int num_tracks, int left_track, int right_track) {
	int index = std::stoi(formula->GetConstant()); // will be string version of integer
	int ns = index+6;
	int sink = ns-1;
	char *statuses = new char[ns+1];
	int var = VAR_PER_TRACK;
	int len = num_tracks * var;
	int *mindices = Automaton::GetBddVariableIndices(len);
	std::vector<char> exep_lambda(var,'1');
	TransitionVector tv = GenerateTransitionsForRelation(formula->GetType(),VAR_PER_TRACK);

	dfaSetup(ns,len,mindices);
	// till index state, dont care
	for(int i = 0; i < index; i++) {
		dfaAllocExceptions(0);
		dfaStoreState(i+1);
		statuses[i] = '-';
	}
	// index state
	dfaAllocExceptions(tv.size());
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for(int k = 0; k < VAR_PER_TRACK; k++ ){
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = tv[i].second[k];
		}
		str.push_back('\0');
		dfaStoreException(index+1,&str[0]);
	}
	dfaStoreState(sink);
	statuses[index] = '-';

	int lambda_star = index+2;
	int star_lambda = index+3;
	int lambda_lambda = index+4;
	//lambda_star -> state = index+2
	//star_lambda -> state = index+3
	//lambda_lambda -> state = index+4
	//sink -> state = index+5

	// index+1 -> lambda_star,
	//         -> star_lambda,
	//         -> lambda_lambda

	dfaAllocExceptions(tv.size()*2+1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str(len,'X');
		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = exep_lambda[k];
			str[right_track+num_tracks*k] = tv[i].first[k];
		}
		str.push_back('\0');
		dfaStoreException(lambda_star,&str[0]);

		for (int k = 0; k < var; k++) {
			str[left_track+num_tracks*k] = tv[i].first[k];
			str[right_track+num_tracks*k] = exep_lambda[k];
		}
		dfaStoreException(star_lambda,&str[0]);
	}

	// if both are lambda, go to sink
	std::vector<char> str(len,'X');
	str = std::vector<char>(len,'X');
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	str.push_back('\0');
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(index+1);
	statuses[index+1] = '-';

	// lambda_star state
	dfaAllocExceptions(tv.size()+1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str2(len,'X');
		for (int k = 0; k < var; k++) {
			str2[left_track+num_tracks*k] = exep_lambda[k];
			str2[right_track+num_tracks*k] = tv[i].first[k];
		}
		str2.push_back('\0');
		dfaStoreException(lambda_star,&str2[0]);
	}

	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(sink);
	statuses[lambda_star] = '-';

	// star_lambda state
	dfaAllocExceptions(tv.size()+1);
	for(int i = 0; i < tv.size(); i++) {
		std::vector<char> str2(len,'X');
		for (int k = 0; k < var; k++) {
			str2[left_track+num_tracks*k] = tv[i].first[k];
			str2[right_track+num_tracks*k] = exep_lambda[k];
		}
		str2.push_back('\0');
		dfaStoreException(star_lambda,&str2[0]);
	}
	for(int k = 0; k < var; k++) {
		str[left_track+num_tracks*k] = exep_lambda[k];
		str[right_track+num_tracks*k] = exep_lambda[k];
	}
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(sink);
	statuses[star_lambda] = '-';

	// lambda_lambda state
	dfaAllocExceptions(1);
	dfaStoreException(lambda_lambda,&str[0]);
	dfaStoreState(sink);
	statuses[lambda_lambda] = '+';

	// sink state
	dfaAllocExceptions(0);
	dfaStoreState(sink);
	statuses[sink] = '-';
	statuses[ns] = '\0';

	DFA_ptr temp_dfa = dfaBuild(statuses);
	DFA_ptr result_dfa = dfaMinimize(temp_dfa);
	dfaFree(temp_dfa);

	temp_dfa = MakeBinaryAlignedDfa(left_track,right_track,num_tracks);
	result_dfa = DFAIntersect(result_dfa,temp_dfa);
	dfaFree(temp_dfa);

	delete[] statuses;
	return result_dfa;
}

StringAutomaton_ptr StringAutomaton::MakePrefixSuffix(int left_track, int prefix_track, int suffix_track, int num_tracks) {
	StringAutomaton_ptr result_auto = nullptr;
  DFA_ptr temp_dfa, result_dfa;
  TransitionVector tv;

  int var = VAR_PER_TRACK;
  int len = num_tracks * var;
  int *mindices = GetBddVariableIndices(num_tracks*var);

  std::vector<char> exep_lambda(var,'1');
  tv = GenerateTransitionsForRelation(StringFormula::Type::EQ, var);
  dfaSetup(4,len,mindices);
  dfaAllocExceptions(2*tv.size() + 1); // 1 extra for lambda stuff below
  for(int i = 0; i < tv.size(); i++) {
    std::vector<char> str(len,'X');
    for(int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = tv[i].first[k];
      str[prefix_track+num_tracks*k] = tv[i].first[k];
      str[suffix_track+num_tracks*k] = exep_lambda[k];
    }
    str.push_back('\0');
    dfaStoreException(0,&str[0]);
  }

  // if prefix is lambda, left  and suffix same
  for(int i = 0; i < tv.size(); i++) {
    std::vector<char> str(len,'X');
    for (int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = tv[i].first[k];
      str[prefix_track+num_tracks*k] = exep_lambda[k];
      str[suffix_track+num_tracks*k] = tv[i].first[k];
    }
    str.push_back('\0');
    dfaStoreException(1,&str[0]);
  }

  // if all 3 are lambda, go to next state
  std::vector<char> str(len,'X');
  str = std::vector<char>(len,'X');
  for(int k = 0; k < var; k++) {
    str[left_track+num_tracks*k] = exep_lambda[k];
    str[prefix_track+num_tracks*k] = exep_lambda[k];
    str[suffix_track+num_tracks*k] = exep_lambda[k];
  }
  str.push_back('\0');
  dfaStoreException(2,&str[0]);
  dfaStoreState(3);

  // left = suffix, prefix lambda, loop back here
  dfaAllocExceptions(tv.size() + 1);
  for(int i = 0; i < tv.size(); i++) {
    std::vector<char> str(len,'X');
    for (int k = 0; k < var; k++) {
      str[left_track+num_tracks*k] = tv[i].first[k];
      str[prefix_track+num_tracks*k] = exep_lambda[k];
      str[suffix_track+num_tracks*k] = tv[i].first[k];
    }
    str.push_back('\0');
    dfaStoreException(1,&str[0]);
  }

  // if all 3 lambda, goto 2
  str = std::vector<char>(len,'X');
  for(int k = 0; k < var; k++) {
    str[left_track+num_tracks*k] = exep_lambda[k];
    str[prefix_track+num_tracks*k] = exep_lambda[k];
    str[suffix_track+num_tracks*k] = exep_lambda[k];
  }
  str.push_back('\0');
  dfaStoreException(2,&str[0]);
  dfaStoreState(3);

  // lambda/lambda state, loop back on lambda
  dfaAllocExceptions(1);
  dfaStoreException(2,&str[0]);
  dfaStoreState(3);

  // sink
  dfaAllocExceptions(0);
  dfaStoreState(3);

  temp_dfa = dfaBuild("--+-");
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  result_auto = new StringAutomaton(result_dfa,num_tracks,num_tracks*VAR_PER_TRACK);

  return result_auto;
}

// TODO: Formulas and intersection? What do?
StringAutomaton_ptr StringAutomaton::MakeConcatExtraTrack(int left_track, int right_track, int num_tracks, std::string str_constant) {
  StringAutomaton_ptr any_string_auto = StringAutomaton::MakeAnyString();
  StringAutomaton_ptr const_string_auto = StringAutomaton::MakeString(str_constant);
  auto temp_dfa = StringAutomaton::PrependLambda(const_string_auto->getDFA(),DEFAULT_NUM_OF_VARIABLES);

  delete const_string_auto;
  // has string constant on last track (prepended with lambda)
  auto temp_auto = new StringAutomaton(temp_dfa,num_tracks,num_tracks+1,VAR_PER_TRACK);
  delete temp_dfa;
  // has any-string on correct track
  auto any_string_extended_auto = new StringAutomaton(any_string_auto->getDFA(),right_track,num_tracks+1,DEFAULT_NUM_OF_VARIABLES);
  delete any_string_auto;
  auto prefix_suffix_auto = StringAutomaton::MakePrefixSuffix(left_track,right_track,num_tracks,num_tracks+1);

  //auto intersect_auto = prefix_suffix_auto;
  auto intersect_auto = prefix_suffix_auto->Intersect(any_string_extended_auto);
  delete prefix_suffix_auto;
  delete any_string_extended_auto;

  auto result_auto = intersect_auto->Intersect(temp_auto);
  delete intersect_auto;
  delete temp_auto;
  temp_auto = result_auto;
  // project away temporary track used for constant
  result_auto = temp_auto->ProjectKTrack(num_tracks);
  delete temp_auto;

  return result_auto;
}


bool StringAutomaton::IsExepEqualChar(std::vector<char> exep, std::vector<char> cvec, int var) {
  for(int i = 0; i < var; i++) {
    if(exep[i] != cvec[i])
      return false;
  }
  return true;
}

bool StringAutomaton::IsExepIncludeChar(std::vector<char> exep, std::vector<char> cvec, int var) {
  for(int i = 0; i < var; i++) {
    if(exep[i] != 'X' && exep[i] != cvec[i])
      return false;
  }
  return true;
}

// resulting dfa has 1 more bit for lambda stuff
DFA_ptr StringAutomaton::PrependLambda(DFA_ptr dfa, int var) {
  if(var != DEFAULT_NUM_OF_VARIABLES) {
    LOG(FATAL) << "mismatched incoming var";
  }
  DFA_ptr M = dfa, temp = nullptr, result = nullptr;
  trace_descr tp;
  paths state_paths, pp;
  std::vector<std::pair<std::vector<char>,int>> state_exeps;
  int num_states = M->ns+1;
  int sink = Automaton::find_sink(M);
  bool has_sink = true;

  if(sink < 0) {
    has_sink = false;
    sink = num_states;
    num_states++;
  } else {
    sink++; // +1 for new state
  }

  char* statuses;
  int* mindices;
  int len = VAR_PER_TRACK; // 1 more than default_num_var

  mindices = GetBddVariableIndices(len);
  statuses = new char[num_states+1];

  // begin dfa building process
  dfaSetup(num_states, len, mindices);

  // setup for initial state
  state_paths = pp = make_paths(M->bddm, M->q[0]);
  while(pp) {
    if(pp->to != sink-1) {
      std::vector<char> curr(len,'0');
      for(unsigned j = 0; j < var; j++) {
        for(tp = pp->trace; tp && (tp->index != mindices[j]); tp = tp->next);
        if(tp) {
          if(tp->value) curr[j] = '1';
          else curr[j] = '0';
        }
        else
          curr[j] = 'X';
      }
      curr.push_back('\0');
      state_exeps.push_back(std::make_pair(curr,pp->to+1));
    }
    pp = pp->next;
  }
  kill_paths(state_paths);

  // add lambda loop to self
  std::vector<char> str(len,'1');
  str.push_back('\0');
  state_exeps.push_back(std::make_pair(str,0));
  dfaAllocExceptions(state_exeps.size());
  for(unsigned k = 0; k < state_exeps.size(); ++k) {
    dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
  }
  dfaStoreState(sink);

  state_exeps.clear();
  if(M->f[0] == 1) {
    statuses[0] = '+';
  } else {
    statuses[0] = '-';
  }

  // rest of states (shift 1)
  for(unsigned i = 0; i < M->ns; i++) {
    state_paths = pp = make_paths(M->bddm, M->q[i]);

    while(pp) {
      if(pp->to != sink-1) {
        std::vector<char> curr(len,'0');
        for(unsigned j = 0; j < var; j++) {
          for(tp = pp->trace; tp && (tp->index != mindices[j]); tp = tp->next);
          if(tp) {
            if(tp->value) curr[j] = '1';
            else curr[j] = '0';
          }
          else
            curr[j] = 'X';
        }
        curr.push_back('\0');
        state_exeps.push_back(std::make_pair(curr,pp->to+1));
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    dfaAllocExceptions(state_exeps.size());
    for(unsigned k = 0; k < state_exeps.size(); ++k) {
      dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
    }
    dfaStoreState(sink);
    state_exeps.clear();

    if(M->f[i] == 1) {
      statuses[i+1] = '+';
    } else if(M->f[i] == -1) {
      statuses[i+1] = '-';
    } else {
      statuses[i+1] = '0';
    }
  }

  if(!has_sink) {
    dfaAllocExceptions(0);
    dfaStoreState(sink);
    statuses[sink] = '-';
  }

  statuses[num_states] = '\0';
  temp = dfaBuild(statuses);
  result = dfaMinimize(temp);
  dfaFree(temp);

  delete[] statuses;

  return result;
}

// incoming dfa has extrabit for lambda
// remove lambda transitions and project away extra bit
DFA_ptr StringAutomaton::TrimLambdaPrefix(DFA_ptr dfa, int var, bool project_bit) {
  if(var != VAR_PER_TRACK) {
    LOG(FATAL) << "not correct var";
  }
  DFA_ptr result_dfa = nullptr, temp_dfa = nullptr;
  paths state_paths, pp;
  trace_descr tp;
  char* statuses;
  int *indices = Automaton::GetBddVariableIndices(var);
  int sink = find_sink(dfa);
  CHECK_GT(sink,-1);
  std::vector<char> lambda_vec(var,'1');
  // start at start-state
  // if transition is lambda, we need to add that "to" state to the
  // pool of possible start states
  std::vector<bool> states_visited(dfa->ns,false);
  std::vector<int> reachable;
  std::queue<int> states_to_visit;

  states_to_visit.push(dfa->s);
  states_visited[dfa->s] = true;
  reachable.push_back(dfa->s);

  while(!states_to_visit.empty()) {
    int state = states_to_visit.front();
    states_to_visit.pop();
    state_paths = pp = make_paths(dfa->bddm, dfa->q[state]);
    std::vector<char> exep(var,'X');
    while(pp) {
      if(pp->to == sink) {
        pp = pp->next;
        continue;
      }

      for(int j = 0; j < var; j++) {
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) exep[j] = '1';
          else exep[j] = '0';
        }
        else
          exep[j] = 'X';
      }

      if (IsExepEqualChar(exep, lambda_vec,var) ) {
        if(states_visited[pp->to]) {
          pp = pp->next;
          continue;
        }
        states_to_visit.push(pp->to);
        states_visited[pp->to] = true;
        reachable.push_back(pp->to);
      }
      pp = pp->next;
    }
    kill_paths(state_paths);
  }

  int num_initial = reachable.size();
  int num_bits = std::ceil(std::log2(num_initial));
  int len = var + num_bits;

  // one new "initial" state, which encompasses all reachable states
  // by lambda
  int num_states = dfa->ns+1;
  std::vector<std::pair<std::vector<char>,int>> state_exeps;
  indices = GetBddVariableIndices(len);
  statuses = new char[num_states+1];

  // if any of the reachable states are final, then the new
  // initial state is final
  statuses[0] = '-';
  for(int i = 0; i < reachable.size(); i++) {
    if(dfa->f[reachable[i]] == 1) {
      statuses[0] = '+';
    }
  }

  dfaSetup(num_states,len,indices);
  // setup new "initial" state first
  for(int i = 0; i < reachable.size(); i++) {
    state_paths = pp = make_paths(dfa->bddm, dfa->q[reachable[i]]);
    std::vector<char> exep(var,'X');
    while(pp) {
      if(pp->to == sink) {
        pp = pp->next;
        continue;
      }
      for(int j = 0; j < var; j++) {
        for(tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if(tp) {
          if(tp->value) {
            exep[j] = '1';
          } else {
            exep[j] = '0';
          }
        } else {
          exep[j] = 'X';
        }
      }

      if (!IsExepEqualChar(exep, lambda_vec,var)) {
        std::vector<char> extra_bit_value = GetBinaryFormat(i, num_bits); // i = current state
        std::vector<char> v = exep;
        v.insert(v.end(), extra_bit_value.begin(), extra_bit_value.end());
        state_exeps.push_back(std::make_pair(v, pp->to + 1));
      }
      pp = pp->next;
    }
    kill_paths(state_paths);
  }

  dfaAllocExceptions(state_exeps.size());
  for(int i = 0; i < state_exeps.size(); i++) {
    dfaStoreException(state_exeps[i].second,&state_exeps[i].first[0]);
  }
  dfaStoreState(sink+1);
  state_exeps.clear();

  // continue with rest of states
  for(int i = 0; i < dfa->ns; i++) {
    statuses[i+1] = '-';
    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
    while(pp) {
      if (pp->to == sink) {
        pp = pp->next;
        continue;
      }
      std::vector<char> exep(var,'X');
      for (int j = 0; j < var; j++) {
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
        if (tp) {
          if (tp->value) exep[j] = '1';
          else exep[j] = '0';
        }
        else
          exep[j] = 'X';
      }
      // if not lambda, then add transition, with 0s padded on end
      if (!IsExepEqualChar(exep, lambda_vec,var)) {
        for (int k = 0; k < num_bits; k++) {
          exep.push_back('0');
        }
        exep.push_back('\0');
        state_exeps.push_back(std::make_pair(exep,pp->to+1));
      } else if(dfa->f[pp->to == 1]) {
        statuses[i+1] = '+';
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    dfaAllocExceptions(state_exeps.size());
    for(int j = 0; j < state_exeps.size(); j++) {
      dfaStoreException(state_exeps[j].second, &state_exeps[j].first[0]);
    }
    dfaStoreState(sink+1);
    state_exeps.clear();

    if(dfa->f[i] == 1) {
      statuses[i+1] = '+';
    }
  }

  statuses[num_states] = '\0';

  temp_dfa = dfaBuild(statuses);
  result_dfa = dfaMinimize(temp_dfa);
  dfaFree(temp_dfa);
  if(project_bit) {
    // project away the last bit as well
    num_bits++;
  }

  for(int i = 0; i < num_bits; i++) {
    int bit = len-i-1;
    temp_dfa = dfaProject(result_dfa,(unsigned)bit);
    dfaFree(result_dfa);
    result_dfa = dfaMinimize(temp_dfa);
    dfaFree(temp_dfa);
  }

  delete[] statuses;

  return result_dfa;
}

// var should be 9
DFA_ptr StringAutomaton::TrimLambdaSuffix(DFA_ptr dfa, int var, bool project_bit) {
  if(var != VAR_PER_TRACK) {
    LOG(FATAL) << "Bad nuber o bits!";
  }

  DFA_ptr result_dfa = nullptr, temp = nullptr;
  paths state_paths, pp;
  trace_descr tp;
  char* statuses = new char[dfa->ns+1];
  int *indices = Automaton::GetBddVariableIndices(var);
  int sink = find_sink(dfa);
  CHECK_GT(sink,-1);

  std::vector<std::pair<std::vector<char>,int>> state_exeps;
  std::vector<char> lambda_vec(var,'1');
  dfaSetup(dfa->ns, var, indices);
  for(int i = 0; i < dfa->ns; i++) {
    state_paths = pp = make_paths(dfa->bddm, dfa->q[i]);
    statuses[i] = '-';
    while (pp) {
      if (pp->to != sink) {
        std::vector<char> exep(var,'X');
        for (unsigned j = 0; j < var; j++) {
          for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);

          if (tp) {
            if (tp->value) exep[j] = '1';
            else exep[j] = '0';
          }
          else
            exep[j] = 'X';
        }

        bool is_lam = IsExepEqualChar(exep,lambda_vec,var);
        if (is_lam && i == pp->to) {

        }
        else {
          exep.push_back('\0');
          state_exeps.push_back(std::make_pair(exep, pp->to));
          if(is_lam && dfa->f[pp->to] == 1) {
            statuses[i] = '+';
          }
        }
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    dfaAllocExceptions(state_exeps.size());
    for (unsigned k = 0; k < state_exeps.size(); k++) {
      dfaStoreException(state_exeps[k].second,&state_exeps[k].first[0]);
    }
    dfaStoreState(sink);
    state_exeps.clear();
  }
  statuses[dfa->ns] = '\0';
  temp = dfaBuild(statuses);
  result_dfa = dfaMinimize(temp);
  dfaFree(temp);

  if(project_bit) {
    // project away extra bit
    temp = dfaProject(result_dfa, var - 1);
    dfaFree(result_dfa);
    result_dfa = dfaMinimize(temp);
    dfaFree(temp);
  }

  delete[] statuses;

  return result_dfa;
}

DFA_ptr StringAutomaton::TrimPrefix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  StringAutomaton_ptr temp_multi = nullptr, subject_multi = nullptr,
                          trim_multi = nullptr, intersect_multi = nullptr;
  StringAutomaton_ptr result_string_auto = nullptr;

  // (x,x,lambda) until track 2 is lambda
  // (x,lambda,x) until end
  temp_multi = MakePrefixSuffix(0,1,2,3);
  subject_multi = new StringAutomaton(subject_dfa,0,3, DEFAULT_NUM_OF_VARIABLES);
  trim_multi = new StringAutomaton(trim_dfa,1,3, DEFAULT_NUM_OF_VARIABLES);

  intersect_multi = temp_multi->Intersect(subject_multi);
  delete temp_multi;
  delete subject_multi;

  temp_multi = intersect_multi;
  intersect_multi = temp_multi->Intersect(trim_multi);
  delete temp_multi;
  delete trim_multi;

  // 3rd track has lambda prefix, so get it (automatically removes lambda prefix/suffix)
  result_string_auto = intersect_multi->GetKTrack(2);
  result_dfa = dfaCopy(result_string_auto->getDFA());
  delete intersect_multi;
  delete result_string_auto;

  return result_dfa;
}

DFA_ptr StringAutomaton::TrimSuffix(DFA_ptr subject_dfa, DFA_ptr trim_dfa, int var) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  StringAutomaton_ptr temp_multi = nullptr, subject_multi = nullptr,
                          trim_multi = nullptr, intersect_multi = nullptr;
  StringAutomaton_ptr result_string_auto = nullptr;

  // (x,x,lambda) until track 2 is lambda
  // (x,lambda,x) until end
  temp_multi = MakePrefixSuffix(0,1,2,3);
  subject_multi = new StringAutomaton(subject_dfa,0,3,DEFAULT_NUM_OF_VARIABLES);
  // gotta prepend trim_dfa first, to go on track 3
  temp_dfa = PrependLambda(trim_dfa,var);
  trim_multi = new StringAutomaton(temp_dfa,2,3,VAR_PER_TRACK);
  dfaFree(temp_dfa);

  intersect_multi = temp_multi->Intersect(subject_multi);
  delete temp_multi;
  delete subject_multi;

  temp_multi = intersect_multi;
  intersect_multi = temp_multi->Intersect(trim_multi);
  delete temp_multi;
  delete trim_multi;

  result_string_auto = intersect_multi->GetKTrack(1);
  result_dfa = dfaCopy(result_string_auto->getDFA());
  delete intersect_multi;
  delete result_string_auto;

  return result_dfa;
}

DFA_ptr StringAutomaton::concat(DFA_ptr prefix_dfa, DFA_ptr suffix_dfa, int var) {
  DFA_ptr temp_dfa = nullptr, result_dfa = nullptr;
  StringAutomaton_ptr temp_multi = nullptr, prefix_multi = nullptr,
                          suffix_multi = nullptr, intersect_multi = nullptr;
  StringAutomaton_ptr result_string_auto = nullptr;

  // (x,x,lambda) until track 2 is lambda
  // (x,lambda,x) until end
//  LOG(FATAL) << "HERE";

  temp_multi = MakePrefixSuffix(0,1,2,3);
  prefix_multi = new StringAutomaton(prefix_dfa,1,3,var);
  temp_dfa = PrependLambda(suffix_dfa,var);
  suffix_multi = new StringAutomaton(temp_dfa,2,3,VAR_PER_TRACK);
  dfaFree(temp_dfa);
  intersect_multi = temp_multi->Intersect(prefix_multi);
  delete temp_multi;
  delete prefix_multi;
  temp_multi = intersect_multi;
  intersect_multi = temp_multi->Intersect(suffix_multi);
  delete temp_multi;
  delete suffix_multi;
	result_string_auto = intersect_multi->GetKTrack(0);
	result_dfa = dfaCopy(result_string_auto->getDFA());

  delete intersect_multi;
  delete result_string_auto;
  return result_dfa;
}

DFA_ptr StringAutomaton::PreConcatPrefix(DFA_ptr concat_dfa, DFA_ptr suffix_dfa, int var) {
  return TrimSuffix(concat_dfa,suffix_dfa,var);
}

DFA_ptr StringAutomaton::PreConcatSuffix(DFA_ptr concat_dfa, DFA_ptr prefix_dfa, int var) {
  return TrimPrefix(concat_dfa,prefix_dfa,var);
}

bool StringAutomaton::HasExceptionToValidStateFrom(int state, std::vector<char>& exception) {
	int sink_state = this->GetSinkState();
	return (sink_state != this->getNextState(state, exception));
}

std::vector<int> StringAutomaton::GetAcceptingStates() {
	std::vector<int> final_states;
	for (int s = 0; s < this->dfa_->ns; s++) {
		if (this->IsAcceptingState(s)) {
			final_states.push_back(s);
		}
	}
	return final_states;
}

/**
 * @param search automaton is an automaton that does not accept empty string
 * @this is an automaton that is known to be contains search automaton
 */
StringAutomaton_ptr StringAutomaton::IndexOfHelper(StringAutomaton_ptr search_auto) {
	StringAutomaton_ptr index_of_auto = nullptr;
	index_of_auto = this->Search(search_auto);
	int sink_state = index_of_auto->GetSinkState();
	int current_state = -1;
	int next_state = -1;
	std::vector<char> flag = {'1', '1', '1', '1', '1', '1', '1', '1', '1'}; // 255 (+1 extrabit)
	std::set<int> next_states;
	std::stack<int> state_work_list;
	std::map<int, bool> visited;

	for (int s = 0; s < index_of_auto->dfa_->ns; s++) {
		index_of_auto->dfa_->f[s] = -1;
	}
	visited[sink_state] = true;
	state_work_list.push(index_of_auto->dfa_->s);
	while (not state_work_list.empty()) {
		current_state = state_work_list.top(); state_work_list.pop();
		visited[current_state] = true;

		next_states = index_of_auto->getNextStates(current_state);

		if (sink_state != (next_state = index_of_auto->getNextState(current_state, flag))) {
			index_of_auto->dfa_->f[current_state] = 1; // mark final state for beginning of a match
			next_states.erase(next_state);
		}

		for (auto n : next_states) {
			if (not visited[n]) {
				state_work_list.push(n);
			}
		}
	}
	index_of_auto->Minimize();

	// remove extra bit used
	index_of_auto->ProjectAway((unsigned)(index_of_auto->num_of_bdd_variables_ - 1));
	index_of_auto->Minimize();

	DVLOG(VLOG_LEVEL) << index_of_auto->id_ << " = [" << this->id_ << "]->indexOfHelper(" << search_auto->id_  << ")";
	return index_of_auto;
}

/**
 * @param search automaton is an automaton that does not accept empty string
 * @this is an automaton that is known to be contains search automaton
 */
StringAutomaton_ptr StringAutomaton::LastIndexOfHelper(StringAutomaton_ptr search_auto) {
	StringAutomaton_ptr lastIndexOf_auto = nullptr, search_result_auto = nullptr;

	DFA_ptr lastIndexOf_dfa = nullptr, minimized_dfa = nullptr;

	search_result_auto = this->Search(search_auto);

	Graph_ptr graph = search_result_auto->toGraph();
	// Mark start state of a match
	std::vector<char> flag_1_exception = {'1', '1', '1', '1', '1', '1', '1', '1', '1'}; // 255
	GraphNode_ptr node = nullptr;
	int sink_state = search_result_auto->GetSinkState();
	int next_state = -1;
	for (int s = 0; s < search_result_auto->dfa_->ns; s++) {
		node = graph->getNode(s);
		if (sink_state != (next_state = search_result_auto->getNextState(s, flag_1_exception))) {
			node->addEdgeFlag(1, graph->getNode(next_state)); // flag 1 is to mark for beginning of a match
		}
	}

	// BEGIN find new final states using reverse DFS traversal
	for (auto final_node : graph->getFinalNodes()) {
		std::stack<GraphNode_ptr> node_stack;
		std::map<GraphNode_ptr, bool> is_visited; // by default bool is initialized as false
		GraphNode_ptr curr_node = nullptr;
		node_stack.push(final_node);
		while (not node_stack.empty()) {
			curr_node = node_stack.top(); node_stack.pop();
			is_visited[curr_node] = true;
			for (auto& prev_node : curr_node->getPrevNodes()) {
				if (prev_node->hasEdgeFlag(1, curr_node)) { // a match state found
					prev_node->removeEdgeFlag(1, curr_node);
					prev_node->addEdgeFlag(3, curr_node); // 3 is for new final state
				} else {
					if (is_visited.find(prev_node) == is_visited.end()) {
						node_stack.push(prev_node);
					}
				}
			}
		}
	}

	// END find new final states using reverse DFS traversal
	graph->resetFinalNodesToFlag(3);

	// BEGIN generate automaton
	for (int s = 0; s < search_result_auto->dfa_->ns; s++) {
		GraphNode_ptr node = graph->getNode(s);
		if (graph->isFinalNode(node)) {
			search_result_auto->dfa_->f[s] = 1;
		} else {
			search_result_auto->dfa_->f[s] = -1;
		}
	}

	search_result_auto->Minimize();

	lastIndexOf_auto = search_result_auto->RemoveReservedWords();
	delete search_result_auto;

	// remove extra bit
	lastIndexOf_auto->ProjectAway((unsigned)(lastIndexOf_auto->num_of_bdd_variables_ - 1));
	lastIndexOf_auto->Minimize();

	DVLOG(VLOG_LEVEL) << lastIndexOf_auto->id_ << " = [" << this->id_ << "]->lastIndexOf(" << search_auto->id_ << ")";

	return lastIndexOf_auto;
}

/**
 * Duplicates each state in the automaton using extra bit,
 * Special words 1111 1111 1, 1111 11110 1 used for the transitions between duplicated states
 *
 * Output M so that L(M)={w|w=x0#1\bar{x1}#2.., where x0x1... \in L(M1)} (usage with extra bit)
 * @param use_extra_bit decides on whether to use extra bit or not.
 *
 */
StringAutomaton_ptr StringAutomaton::GetDuplicateStateAutomaton() {
	StringAutomaton_ptr duplicated_auto = nullptr;
	DFA_ptr result_dfa = nullptr;
	paths state_paths = nullptr, pp = nullptr;
	trace_descr tp = nullptr;

	// sharp1: 1111 1111 1
	// sharp0: 1111 1110 1
	std::vector<char> sharp1 = Automaton::getReservedWord('1', num_of_bdd_variables_, true);
	std::vector<char> sharp0 = Automaton::getReservedWord('0', num_of_bdd_variables_, true);

	int number_of_variables = this->num_of_bdd_variables_ + 1,
					sink_state = this->GetSinkState(),
					to_state = 0,
					to_duplicate_state = 0,
					mapped_state_id = 0,
					duplicated_state_id = 0;

	bool has_sink = (sink_state != -1);
	// take precautions as there might not be a sink state...
	int original_num_states = this->dfa_->ns;
	if(sink_state < 0) {
		sink_state = this->dfa_->ns;
		original_num_states++;
	}
	int number_of_states = original_num_states * 2 - 1; // no duplicate sink state

	int* indices = GetBddVariableIndices(number_of_variables);
	std::map<std::vector<char>*, int> exceptions;
	std::vector<char>* current_exception = nullptr;
	char *statuses = new char[number_of_states + 1];
	bool sink_state_allocated = false;

	dfaSetup(number_of_states, number_of_variables, indices);
	for (int s = 0; s < original_num_states; s++) {
		if (s != sink_state) {
			state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[s]);
			while (pp) {
				if (pp->to != (unsigned)sink_state) {

					// figure out new state id and collect transitions to that state, (avoid modifying sink state)
					to_state = 2  * pp->to;
					if (pp->to > (unsigned)sink_state) {
						to_state--;
					} else if (to_state >= sink_state) {
						to_state++;
					}

					current_exception = new std::vector<char>();
					for (int j = 0; j < this->num_of_bdd_variables_; j++) {
						for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
						if (tp) {
							if (tp->value) {
								current_exception->push_back('1');
							} else {
								current_exception->push_back('0');
							}
						} else {
							current_exception->push_back('X');
						}
					}
					current_exception->push_back('0'); // sharpbit 0 for non-sharp uses
					current_exception->push_back('\0');
					exceptions[current_exception] = to_state;
				}
				current_exception = nullptr;
				tp = nullptr;
				pp = pp->next;
			}
			// figure out new state id for the current state, duplicate state will id will be new_state_id + 1 ( + 2 in case it is a sink)
			mapped_state_id = 2 * s;
			if (s > sink_state) {
				mapped_state_id--;
			} else if (mapped_state_id >= sink_state) {
				mapped_state_id++;
			}

			duplicated_state_id = mapped_state_id + 1;
			if (duplicated_state_id == sink_state) {
				duplicated_state_id++;
			}
			// do allocation for current states
			dfaAllocExceptions(exceptions.size() + 1);
			for (auto entry : exceptions) {
				dfaStoreException(entry.second, &*entry.first->begin());
			}
			dfaStoreException(duplicated_state_id, &*sharp1.begin()); // to duplicated state
			dfaStoreState(sink_state);
			// sink state id is between map_state_id and duplicate_state_id allocate sink state first;
			if ((not sink_state_allocated) and (duplicated_state_id - 1) == sink_state ) {
				dfaAllocExceptions(0);
				dfaStoreState(sink_state);
				statuses[sink_state] = '-';
				sink_state_allocated = true;
			}
			// do allocation for duplicated states
			dfaAllocExceptions(exceptions.size() + 1);
			for (auto it = exceptions.begin(); it != exceptions.end();) {
				to_duplicate_state = it->second + 1;
				if (to_duplicate_state == sink_state) {
					to_duplicate_state++;
				}
				dfaStoreException(to_duplicate_state, &*it->first->begin());
				current_exception = it->first;
				it = exceptions.erase(it);
				delete current_exception;
			}
			dfaStoreException(mapped_state_id, &*sharp0.begin()); // to original state
			dfaStoreState(sink_state);
			// update final states
			if (this->dfa_->f[s] == 1) {
				statuses[mapped_state_id] = '+';
//        statuses[duplicated_state_id] = '0';  // decide on don't care or reject
				statuses[duplicated_state_id] = '-';
			}
			else {
				statuses[mapped_state_id] = '-';
				statuses[duplicated_state_id] = '-';
			}

			kill_paths(state_paths);
			state_paths = pp = nullptr;
			exceptions.clear();
			current_exception = nullptr;
		} else if (not sink_state_allocated) {
			dfaAllocExceptions(0);
			dfaStoreState(sink_state);
			statuses[sink_state] = '-';
			sink_state_allocated = true;
		}
	}

	statuses[number_of_states] = '\0';
	result_dfa = dfaBuild(statuses);

	duplicated_auto = new StringAutomaton(result_dfa, number_of_variables);
	delete[] statuses;
	//delete[] indices;

	DVLOG(VLOG_LEVEL) << duplicated_auto->id_ << " = [" << this->id_ << "]->getDuplicateStateAutomaton()";
	return duplicated_auto;
}

/**
 * TODO Discussion: Don't care states can be used for old final state
 * of search automaton, it will force to read one more word, however this time it
 * takes more space, we can use reject if we are sure that we have always have correct
 * ending in our search query automaton.
 * Generates a contains automaton an complements it,
 * Then connects complemented auto with self using
 * reserved keywords 1111 1111 1, 1111 1110 1.
 * Output M so that L(M)={w|w=x0#1\bar{x1}#2.., where \bar{x_i} \in L(M), x_i is \in the complement of L(S*MS*)} (usage with extrabit)
 * @param use_extra_bit decides on whether to use extra bit or not.
 */
StringAutomaton_ptr StringAutomaton::ToQueryAutomaton() {
	StringAutomaton_ptr query_auto = nullptr, not_contains_auto = nullptr,
						empty_string_auto = nullptr, tmp_auto_1 = nullptr;

	DFA_ptr result_dfa = nullptr;
	paths state_paths = nullptr, pp = nullptr;
	trace_descr tp = nullptr;

	// sharp1: 1111 1111 1
	// sharp0: 1111 1110 1
	std::vector<char> sharp1 = Automaton::getReservedWord('1', num_of_bdd_variables_, true);
	std::vector<char> sharp0 = Automaton::getReservedWord('0', num_of_bdd_variables_, true);

	int number_of_variables = num_of_bdd_variables_ + 1,
					shift = 0,
					number_of_states = 0,
					sink_state = this->GetSinkState(),
					not_contains_sink_state = -1,
					to_state = 0;

	int* indices = GetBddVariableIndices(number_of_variables);

	std::map<std::vector<char>*, int> exceptions;
	std::vector<char>* current_exception = nullptr;
	char *statuses = nullptr;

	not_contains_auto = this->GetAnyStringNotContainsMe();

	// TODO check union with empty works correct
	// union with empty string, so that initial state is accepting
	empty_string_auto = StringAutomaton::MakeEmptyString();
	tmp_auto_1 = not_contains_auto;
	not_contains_auto = tmp_auto_1->Union(empty_string_auto);
	delete empty_string_auto; empty_string_auto = nullptr;
	delete tmp_auto_1; tmp_auto_1 = nullptr;

	not_contains_sink_state = not_contains_auto->GetSinkState();
	if (not_contains_sink_state < 0) {
		shift = not_contains_auto->dfa_->ns;
	} else {
		shift = not_contains_auto->dfa_->ns - 1;
	}

	number_of_states = this->dfa_->ns + shift;
	sink_state += shift;
	statuses = new char[number_of_states + 1];

	dfaSetup(number_of_states, number_of_variables, indices);

	// Construct not contains automaton part
	for (int s = 0, new_state_id = 0; s < not_contains_auto->dfa_->ns; s++) {
		if (s != not_contains_sink_state) {
			state_paths = pp = make_paths(not_contains_auto->dfa_->bddm, not_contains_auto->dfa_->q[s]);
			while (pp) {
				if (pp->to != (unsigned)not_contains_sink_state) {
					if (pp->to > (unsigned)not_contains_sink_state) {
						to_state = pp->to - 1;
					} else {
						to_state = pp->to;
					}

					current_exception = new std::vector<char>();
					for (int j = 0; j < not_contains_auto->num_of_bdd_variables_; j++) {
						for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
						if (tp) {
							if (tp->value) {
								current_exception->push_back('1');
							} else {
								current_exception->push_back('0');
							}
						} else {
							current_exception->push_back('X');
						}
					}
					current_exception->push_back('0'); // sharpbit 0
					current_exception->push_back('\0');
					exceptions[current_exception] = to_state;
				}
				current_exception = nullptr;
				tp = nullptr;
				pp = pp->next;
			}

			if (not_contains_auto->dfa_->f[s] == 1) {
				dfaAllocExceptions(exceptions.size() + 1);
				for (auto it = exceptions.begin(); it != exceptions.end();) {
					dfaStoreException(it->second, &*it->first->begin());
					current_exception = it->first;
					it = exceptions.erase(it);
					delete current_exception;
				}
				dfaStoreException(shift, &*sharp1.begin());
				dfaStoreState(sink_state);
				statuses[new_state_id] = '+';
			} else {
				dfaAllocExceptions(exceptions.size());
				for (auto it = exceptions.begin(); it != exceptions.end();) {
					dfaStoreException(it->second, &*it->first->begin());
					current_exception = it->first;
					it = exceptions.erase(it);
					delete current_exception;
				}
				dfaStoreState(sink_state);
				statuses[new_state_id] = '-';
			}

			kill_paths(state_paths);
			state_paths = pp = nullptr;
			current_exception = nullptr;
			exceptions.clear();
			new_state_id++;
		}
	}

	delete not_contains_auto; not_contains_auto = nullptr;

	// construct search automaton part (this)
	for (int s = 0; s < this->dfa_->ns; s++) {
		if (s != sink_state - shift) {
			state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[s]);
			while (pp) {
				if (pp->to != (unsigned)(sink_state - shift)) {
					to_state = pp->to + shift;
					current_exception = new std::vector<char>();
					for (int j = 0; j < number_of_variables-1; j++) {
						for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
						if (tp) {
							if (tp->value) {
								current_exception->push_back('1');
							} else {
								current_exception->push_back('0');
							}
						} else {
							current_exception->push_back('X');
						}
					}
					current_exception->push_back('0'); // sharpbit 0
					current_exception->push_back('\0');
					exceptions[current_exception] = to_state;
				}
				tp = nullptr;
				pp = pp->next;
			}

			if (this->dfa_->f[s] == 1) {
				dfaAllocExceptions(exceptions.size() + 1);
				for (auto it = exceptions.begin(); it != exceptions.end();) {
					dfaStoreException(it->second, &*it->first->begin());
					current_exception = it->first;
					it = exceptions.erase(it);
					delete current_exception;
				}
				dfaStoreException(0, &*sharp0.begin()); // add sharp0 to the initial state of not_contains auto
				dfaStoreState(sink_state);
//        statuses[s + shift] = '0'; // TODO decide on don't care or reject
				statuses[s + shift] = '-';
			} else {
				dfaAllocExceptions(exceptions.size());
				for (auto it = exceptions.begin(); it != exceptions.end();) {
					dfaStoreException(it->second, &*it->first->begin());
					current_exception = it->first;
					it = exceptions.erase(it);
					delete current_exception;
				}
				dfaStoreState(sink_state);
				statuses[s + shift] = '-';
			}
			kill_paths(state_paths);
			state_paths = pp = nullptr;
			exceptions.clear();
		} else {
			dfaAllocExceptions(0);
			dfaStoreState(sink_state);
			statuses[sink_state] = '-';
		}
	}

	statuses[number_of_states] = '\0';
	result_dfa = dfaBuild(statuses);
	delete[] statuses;
	//delete[] indices;

	query_auto = new StringAutomaton(result_dfa, number_of_variables);
	DVLOG(VLOG_LEVEL) << query_auto->id_ << " = [" << this->id_ << "]->toQueryAutomaton()";

	return query_auto;
}

/**
 * TODO fix the issue when there is empty string accepted by search auto,
 * handle empty string on the caller site
 */
StringAutomaton_ptr StringAutomaton::Search(StringAutomaton_ptr search_auto) {
	StringAutomaton_ptr search_result_auto = nullptr, duplicate_auto = nullptr,
					search_query_auto = nullptr;

	duplicate_auto = this->GetDuplicateStateAutomaton();
	search_query_auto = search_auto->ToQueryAutomaton();
	search_result_auto = duplicate_auto->Intersect(search_query_auto);
	delete duplicate_auto; duplicate_auto = nullptr;
	delete search_query_auto; search_query_auto = nullptr;
	DVLOG(VLOG_LEVEL) << search_result_auto->id_ << " = [" << this->id_ << "]->search(" << search_auto->id_ << ")";
	return search_result_auto;
}

/**
 * Removes special transitions from automaton
 * Can be generalize to general replace algorithm
 */
StringAutomaton_ptr StringAutomaton::RemoveReservedWords() {
	if(this->num_of_bdd_variables_ < 9) {
		LOG(FATAL) << "can't remove reserved words without first having extra bit";
	}
	StringAutomaton_ptr string_auto = nullptr;
	DFA_ptr result_dfa = nullptr;
	paths state_paths = nullptr, pp = nullptr;
	trace_descr tp = nullptr;

	std::vector<char> flag_1 = {'1', '1', '1', '1', '1', '1', '1', '1', '1'}; // 255
	std::vector<char> flag_2 = {'1', '1', '1', '1', '1', '1', '1', '0', '1'}; // 254

	std::map<int, std::set<int>> merged_states_via_reserved_words;
	std::map<int, int> state_id_map;
	std::map<std::vector<char>*, int> exceptions;

	int number_of_variables = this->num_of_bdd_variables_,
					number_of_states = this->dfa_->ns,
					sink_state = this->GetSinkState(),
					next_state = -1;

	// collect information about automaton
	for (int s = 0; s < this->dfa_->ns; s++) {
		if ( (sink_state != (next_state = this->getNextState(s, flag_1))) or
						(sink_state != (next_state = this->getNextState(s, flag_2))) ) {

			auto it_1 = state_id_map.find(next_state);
			if (it_1 != state_id_map.end()) {
				state_id_map[s] = it_1->second;
			} else {
				state_id_map[s] = next_state;
			}

			merged_states_via_reserved_words[state_id_map[s]].insert(s);

			// update old mappings
			auto it_2 = merged_states_via_reserved_words.find(s);
			if (it_2 != merged_states_via_reserved_words.end()) {
				merged_states_via_reserved_words[state_id_map[s]].insert(it_2->second.begin(), it_2->second.end());
				for (auto merged_state : it_2->second) {
					state_id_map[merged_state] = state_id_map[s];
				}
				merged_states_via_reserved_words.erase(it_2);
			}

		} else {
			state_id_map[s] = s;
			merged_states_via_reserved_words[s].insert(s); // mapped to itself or adds itself
		}
	}

	// keep initial state same
	if (state_id_map[this->dfa_->s] != this->dfa_->s) {
		int old_mapping = state_id_map[this->dfa_->s];
		auto it_2 = merged_states_via_reserved_words.find(old_mapping);
		if (it_2 != merged_states_via_reserved_words.end()) {
			merged_states_via_reserved_words[this->dfa_->s].insert(it_2->second.begin(), it_2->second.end());
			for (auto merged_state : it_2->second) {
				state_id_map[merged_state] = this->dfa_->s;
			}
			merged_states_via_reserved_words.erase(it_2);
		}
	}

	// decide on required number of variables to handle non-determinism
	unsigned max = 0;
	for (auto entry : merged_states_via_reserved_words) {
		if (entry.second.size() > max) {
			max = entry.second.size();
		}
	}

	CHECK_NE(0, max) << "Automaton [" << this->id_ << "] does not include reserved keywords";

	number_of_variables = this->num_of_bdd_variables_ + std::ceil(std::log2(max)); // number of variables required
	int* indices = GetBddVariableIndices(number_of_variables);
	char* statuses = new char[number_of_states + 1];
	unsigned extra_bits_value = 0;
	int number_of_extra_bits_needed = number_of_variables - this->num_of_bdd_variables_;
	std::vector<char>* current_exception = nullptr;

	dfaSetup(number_of_states, number_of_variables, indices);
	for (int s = 0; s < number_of_states; s++) {
		if (merged_states_via_reserved_words.find(s) != merged_states_via_reserved_words.end()) {
			statuses[s] = '-'; // initially
			for(auto merge_state : merged_states_via_reserved_words[s]) {
				auto extra_bit_binary_format = GetBinaryFormat(extra_bits_value, number_of_extra_bits_needed);
				state_paths = pp = make_paths(this->dfa_->bddm, this->dfa_->q[merge_state]);
				while (pp) {
					if (pp->to != (unsigned)sink_state) {
						current_exception = new std::vector<char>();
						for (int j = 0; j < this->num_of_bdd_variables_; j++) {
							for (tp = pp->trace; tp && (tp->index != (unsigned)indices[j]); tp = tp->next);
							if (tp) {
								if (tp->value) {
									current_exception->push_back('1');
								} else {
									current_exception->push_back('0');
								}
							} else {
								current_exception->push_back('X');
							}
						}

						// do not add reserved transition, it will be only transition between states if it exists
						if (*current_exception == flag_1 or *current_exception == flag_2) {
							delete current_exception;
						} else {
							for (int i = 0; i < number_of_extra_bits_needed; i++) {
								current_exception->push_back(extra_bit_binary_format[i]);
							}
							current_exception->push_back('\0');
							exceptions[current_exception] = state_id_map[pp->to];
						}
						current_exception = nullptr;
					}

					tp = nullptr;
					pp = pp->next;
				}

				if (this->IsAcceptingState(merge_state)) {
					statuses[s] = '+';
				}

				kill_paths(state_paths);
				state_paths = pp = nullptr;
				extra_bits_value++;
			}
//       do allocation for merged states
			dfaAllocExceptions(exceptions.size());
			for (auto it = exceptions.begin(); it != exceptions.end();) {
				dfaStoreException(it->second, &*it->first->begin());
				current_exception = it->first;
				it = exceptions.erase(it);
				delete current_exception;
			}
			current_exception = nullptr;
			dfaStoreState(sink_state);
			current_exception = nullptr;
			extra_bits_value = 0;
		} else {
			// a state to remove
			dfaAllocExceptions(0);
			dfaStoreState(s);
			statuses[s] = '-';
		}
	}

	statuses[number_of_states] = '\0';
	result_dfa = dfaBuild(statuses);
	//delete[] indices;
	delete[] statuses;
	string_auto = new StringAutomaton(dfaMinimize(result_dfa), number_of_variables);
	dfaFree(result_dfa); result_dfa = nullptr;

	while (number_of_extra_bits_needed > 0) {
		string_auto->ProjectAway((unsigned)(string_auto->num_of_bdd_variables_ - 1));
		string_auto->Minimize();
		number_of_extra_bits_needed--;
	}

	DVLOG(VLOG_LEVEL) << string_auto->id_ << " = [" << this->id_ << "]->removeReservedWords()";
	return string_auto;
}

void StringAutomaton::AddPrintLabel(std::ostream& out) {
	out << " subgraph cluster_0 {\n";
	out << "  style = invis;\n  center = true;\n  margin = 0;\n";
	out << "  node[shape=plaintext];\n";
	out << " \"\"[label=\"";
	if (formula_) {
		out << formula_->GetVariableCoefficientMap().begin()->first << "\n";
	} else {
		out << "str term" << "\n";
	}
	out << "\"]\n";
	out << " }";
}

} /* namespace Theory */
} /* namespace Vlab */
