/*
 * ConstraintSolver.cpp
 *
 *  Created on: Jun 24, 2015
 *      Author: baki
 */

#include "ConstraintSolver.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int ConstraintSolver::VLOG_LEVEL = 11;
bool ConstraintSolver::many_vars = false;

ConstraintSolver::ConstraintSolver(Script_ptr script, SymbolTable_ptr symbol_table,
                                   ConstraintInformation_ptr constraint_information)
    : iteration_count_ { 0 },
      root_(script),
      symbol_table_(symbol_table),
      constraint_information_(constraint_information),
      arithmetic_constraint_solver_(script, symbol_table, constraint_information,
                                    Option::Solver::USE_SIGNED_INTEGERS),
      string_constraint_solver_(script, symbol_table, constraint_information) {
	Automaton::SetCountBoundExact(Option::Solver::COUNT_BOUND_EXACT);
}

ConstraintSolver::~ConstraintSolver() {
}

void ConstraintSolver::start() {
  DVLOG(VLOG_LEVEL) << "start";
  arithmetic_constraint_solver_.collect_arithmetic_constraint_info();
  string_constraint_solver_.collect_string_constraint_info();
  visit(root_);
  end();
}

void ConstraintSolver::start(int iteration_count) {
  DVLOG(VLOG_LEVEL) << "start" << iteration_count;
  arithmetic_constraint_solver_.collect_arithmetic_constraint_info();
  string_constraint_solver_.collect_string_constraint_info();
  iteration_count_ = iteration_count;
  for (iteration_count_ = 0; iteration_count_ < iteration_count; ++iteration_count_) {
    visit(root_);
  }
  
  

  end();
}

void ConstraintSolver::end() {
	for(auto &it : term_values_) {
		delete it.second;
		it.second = nullptr;
	}
	term_values_.clear();
	arithmetic_constraint_solver_.clear_term_values();
	string_constraint_solver_.clear_term_values();
}

void ConstraintSolver::visitScript(Script_ptr script) {
  symbol_table_->push_scope(script);
  Visitor::visit_children_of(script);
  symbol_table_->pop_scope();  // global scope, it is reachable via script pointer all the time
}

void ConstraintSolver::visitCommand(Command_ptr command) {
  LOG(ERROR)<< "'" << *command<< "' is not expected.";
}

void ConstraintSolver::visitAssert(Assert_ptr assert_command) {
  DVLOG(VLOG_LEVEL) << "visit: " << *assert_command;

  check_and_visit(assert_command->term);

  Value_ptr result = getTermValue(assert_command->term);
  bool is_satisfiable = result->is_satisfiable();
  symbol_table_->update_satisfiability_result(is_satisfiable);
  if ((Term::Type::OR not_eq assert_command->term->type()) and (Term::Type::AND not_eq assert_command->term->type())) {

    if (is_satisfiable) {
      update_variables();
    }
  }
  clearTermValuesAndLocalLetVars();

}

void ConstraintSolver::visitTerm(Term_ptr term) {
}

void ConstraintSolver::visitExclamation(Exclamation_ptr exclamation_term) {
}

void ConstraintSolver::visitExists(Exists_ptr exists_term) {
  DVLOG(VLOG_LEVEL) << "visit children start: " << *exists_term << "@" << exists_term;
  auto is_satisfiable = check_and_visit(exists_term->term);
  DVLOG(VLOG_LEVEL) << "visit children end: " << *exists_term << "@" << exists_term;

  DVLOG(VLOG_LEVEL) << "temp variable projection start: " << *exists_term << "@" << exists_term;
  for(auto sorted_var : *exists_term->sorted_var_list) {
    auto sorted_var_name = sorted_var->symbol->getData();
    symbol_table_->project_variable_all_scopes(sorted_var_name);
    string_constraint_solver_.project_variable(sorted_var_name);
  }
  DVLOG(VLOG_LEVEL) << "temp variable projection end: " << *exists_term << "@" << exists_term;

  if(constraint_information_->has_string_constraint(exists_term->term)) {
    is_satisfiable = is_satisfiable and string_constraint_solver_.get_term_value(exists_term->term);
  }

  Value_ptr result = new Value(is_satisfiable);
  setTermValue(exists_term,result);
}

void ConstraintSolver::visitForAll(ForAll_ptr for_all_term) {
}

void ConstraintSolver::visitLet(Let_ptr let_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *let_term;

  symbol_table_->push_scope(let_term);

  Value_ptr param = nullptr;
  for (auto& var_binding : *(let_term->var_binding_list)) {
    path_trace_.push_back(let_term);
    check_and_visit(var_binding->term);
    path_trace_.pop_back();
    param = getTermValue(var_binding->term);
    symbol_table_->set_value(var_binding->symbol->getData(), param->clone());

    // TEST: inspect params
//    if (param->getType() == Value::Type::STRING_AUTOMATON) {
//      param->getStringAutomaton()->inspectAuto();
//    } else {
//      param->getIntAutomaton()->inspectAuto();
//    }
  }

  path_trace_.push_back(let_term);
  check_and_visit(let_term->term);
  path_trace_.pop_back();
  param = getTermValue(let_term->term);
  symbol_table_->pop_scope();

  Value_ptr result = param->clone();
  setTermValue(let_term, result);
//  result->getStringAutomaton()->inspectAuto();

//  LOG(FATAL) << "I am here" << std::endl;
}

/**
 * 1) Solve arithmetic constraints
 * 2) Solve relational string constraints
 * 3) Solve single-track strings and mixed constraints
 */
void ConstraintSolver::visitAnd(And_ptr and_term) {
  bool is_satisfiable = true;
  bool is_component = constraint_information_->is_component(and_term);


  if (is_component) {
    if (constraint_information_->has_arithmetic_constraint(and_term)) {
      arithmetic_constraint_solver_.start(and_term);
      is_satisfiable = arithmetic_constraint_solver_.get_term_value(and_term)->is_satisfiable();
      DVLOG(VLOG_LEVEL) << "Arithmetic formulae solved: " << *and_term << "@" << and_term;
    }
    if ((is_satisfiable or (!constraint_information_->has_arithmetic_constraint(and_term)))
    				and constraint_information_->has_string_constraint(and_term)) {
      string_constraint_solver_.start(and_term);
      is_satisfiable = string_constraint_solver_.get_term_value(and_term)->is_satisfiable();
      DVLOG(VLOG_LEVEL) << "String formulae solved: " << *and_term << "@" << and_term;
    }

    DVLOG(VLOG_LEVEL) << "Multi-track solving done: " << *and_term << "@" << and_term;
  }

  DVLOG(VLOG_LEVEL) << "visit children start: " << *and_term << "@" << and_term;

  //if (is_satisfiable and (constraint_information_->has_mixed_constraint(and_term) or (not is_component))) {
  if (is_satisfiable) {
    for (auto& term : *(and_term->term_list)) {
      is_satisfiable = check_and_visit(term) and is_satisfiable;
      if (not is_satisfiable) {
      	clearTermValuesAndLocalLetVars();
      	variable_path_table_.clear();
      	break;
      }
      if (dynamic_cast<Or_ptr>(term) == nullptr and  (dynamic_cast<Exists_ptr>(term) == nullptr)) {
        if (is_satisfiable) {
          is_satisfiable = update_variables();
          if(not is_satisfiable) {
          	break;
          }
        }
        clearTermValuesAndLocalLetVars();
      }
    }
  }

  DVLOG(VLOG_LEVEL) << "visit children end: " << *and_term << "@" << and_term;

  if (is_component and is_satisfiable) {
    if (constraint_information_->has_arithmetic_constraint(and_term)) {
      arithmetic_constraint_solver_.postVisitAnd(and_term);
      is_satisfiable = arithmetic_constraint_solver_.get_term_value(and_term)->is_satisfiable();
    }

    if (is_satisfiable and constraint_information_->has_string_constraint(and_term)) {
      string_constraint_solver_.postVisitAnd(and_term);
      is_satisfiable = string_constraint_solver_.get_term_value(and_term)->is_satisfiable();
    }
  }

  Value_ptr result = new Value(is_satisfiable);
  setTermValue(and_term, result);
}

/**
 * 1) Solve arithmetic constraints
 * 2) Solve relational string constraints
 * 3) Solve single-track strings and mixed constraints
 */
void ConstraintSolver::visitOr(Or_ptr or_term) {
  bool is_satisfiable = false;
  bool is_component = constraint_information_->is_component(or_term);
  
  if (is_component) {
    if (constraint_information_->has_arithmetic_constraint(or_term)) {
      arithmetic_constraint_solver_.start(or_term);
      is_satisfiable = arithmetic_constraint_solver_.get_term_value(or_term)->is_satisfiable();
      DVLOG(VLOG_LEVEL) << "Arithmetic formulae solved: " << *or_term << "@" << or_term;
    }
    if ((is_satisfiable or !constraint_information_->has_arithmetic_constraint(or_term))
    				and constraint_information_->has_string_constraint(or_term)) {
      string_constraint_solver_.start(or_term);
      is_satisfiable = string_constraint_solver_.get_term_value(or_term)->is_satisfiable();
      DVLOG(VLOG_LEVEL) << "String formulae solved: " << *or_term << "@" << or_term;
    }

    DVLOG(VLOG_LEVEL) << "Multi-track solving done: " << *or_term << "@" << or_term;
  }

  DVLOG(VLOG_LEVEL) << "visit children start: " << *or_term << "@" << or_term;

  //if (constraint_information_->has_mixed_constraint(or_term)) {
  if(true) {
    for (auto& term : *(or_term->term_list)) {
      symbol_table_->push_scope(term);
      bool is_scope_satisfiable = check_and_visit(term);

      if (dynamic_cast<And_ptr>(term) == nullptr and  (dynamic_cast<Exists_ptr>(term) == nullptr)) {
        if (is_scope_satisfiable) {
          update_variables();
        } else {
        	variable_path_table_.clear();
        }
        clearTermValuesAndLocalLetVars();
      }

      if(!is_scope_satisfiable) {
        auto val = new Value(is_scope_satisfiable);
        string_constraint_solver_.set_term_value(term,val);
      }

      is_satisfiable = is_satisfiable or is_scope_satisfiable;
      symbol_table_->pop_scope();
    }
  }

  if (is_component and is_satisfiable) {
    if (constraint_information_->has_arithmetic_constraint(or_term)) {
      arithmetic_constraint_solver_.postVisitOr(or_term);
      is_satisfiable = arithmetic_constraint_solver_.get_term_value(or_term)->is_satisfiable();
    }

    if (is_satisfiable and constraint_information_->has_string_constraint(or_term)) {
      string_constraint_solver_.postVisitOr(or_term);
      is_satisfiable = string_constraint_solver_.get_term_value(or_term)->is_satisfiable();
    }
  }

  Value_ptr result = new Value(is_satisfiable);
  setTermValue(or_term, result);

  DVLOG(VLOG_LEVEL) << "visit children end: " << *or_term << "@" << or_term;
}

void ConstraintSolver::visitNot(Not_ptr not_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;

  visit_children_of(not_term);
  Value_ptr result = nullptr, param = getTermValue(not_term->term);

  switch (param->getType()) {
    case Value::Type::BOOL_CONSTANT: {
      result = param->complement();
      break;
    }
    case Value::Type::BOOL_AUTOMATON: {
      // 1- if singleton do not
      // 2- else over-approximate
      LOG(FATAL)<< "implement me";
      break;
    }
    case Value::Type::INT_AUTOMATON: {
      if (param->getIntAutomaton()->isAcceptingSingleInt()) {
        result = param->complement();
      } else {
        result = param->clone();
      }
      break;
    }
    case Value::Type::STRING_AUTOMATON: {
      // TODO multi-track automaton solves over-approximation problem in most cases
      if (param->getStringAutomaton()->IsAcceptingSingleString()) {
        result = param->complement();
      } else {
        result = param->clone();
      }
      break;
    }
    default:
    result = param->complement();
    break;
  }

  setTermValue(not_term, result);
}

void ConstraintSolver::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *u_minus_term;

  Value_ptr result = nullptr, param = getTermValue(u_minus_term->term);

  switch (param->getType()) {
    case Value::Type::INT_CONSTANT: {
      int data = (-param->getIntConstant());
      result = new Value(data);
      break;
    }
    case Value::Type::INT_AUTOMATON: {
      if (param->getIntAutomaton()->isAcceptingSingleInt()) {
        int value = (-param->getIntAutomaton()->getAnAcceptingInt());
        result = new Value(value);
      } else {
        result = new Value(param->getIntAutomaton()->uminus());
      }
      break;
    }
    default:
      LOG(FATAL)<< "unary minus term child is not computed properly: " << *(u_minus_term->term);
      break;
    }

  setTermValue(u_minus_term, result);
}

void ConstraintSolver::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *minus_term;

  Value_ptr result = nullptr, param_left = getTermValue(minus_term->left_term), param_right = getTermValue(
      minus_term->right_term);

  result = param_left->minus(param_right);

  setTermValue(minus_term, result);
}

void ConstraintSolver::visitPlus(Plus_ptr plus_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *plus_term << " ...";

  Value_ptr result = nullptr, plus_value = nullptr, param = nullptr;
  path_trace_.push_back(plus_term);
  for (auto& term_ptr : *(plus_term->term_list)) {
    visit(term_ptr);
    param = getTermValue(term_ptr);
    if (result == nullptr) {
      result = param->clone();
    } else {
      plus_value = result->plus(param);
      delete result;
      result = plus_value;
    }
  }
  path_trace_.pop_back();
  setTermValue(plus_term, result);
}

void ConstraintSolver::visitTimes(Times_ptr times_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *times_term << " ...";

  Value_ptr result = nullptr, times_value = nullptr, param = nullptr;
  path_trace_.push_back(times_term);
  for (auto& term_ptr : *(times_term->term_list)) {
    visit(term_ptr);
    param = getTermValue(term_ptr);
    if (result == nullptr) {
      result = param->clone();
    } else {
      times_value = result->times(param);
      delete result;
      result = times_value;
    }
  }
  path_trace_.pop_back();
  setTermValue(times_term, result);
}

void ConstraintSolver::visitDiv(Div_ptr div_term) {
  LOG(FATAL) << "implement me";
}

void ConstraintSolver::visitEq(Eq_ptr eq_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term << "@" << eq_term;
  visit_children_of(eq_term);

  Value_ptr result = nullptr, param_left = getTermValue(eq_term->left_term), param_right = getTermValue(
      eq_term->right_term);

  if (Value::Type::BOOL_CONSTANT == param_left->getType() and Value::Type::BOOL_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getBoolConstant() == param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType()
      and Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getIntConstant() == param_right->getIntConstant());
  } else {
//    LOG(INFO) << "Before Intersect!";
//    std::cin.get();
//    param_left->getStringAutomaton()->inspectAuto(false,true);
//    param_right->getStringAutomaton()->inspectAuto(false,true);
    result = param_left->intersect(param_right);
//    result->getStringAutomaton()->inspectAuto(false,true);
//    std::cin.get();
  }
  setTermValue(eq_term, result);
}

void ConstraintSolver::visitNotEq(NotEq_ptr not_eq_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;

  // optimization, bypasses variablevaluecomputation & extraction of singletrack from multitrack
  // which is prohibitively expensive
  if(QualIdentifier_ptr left_var = dynamic_cast<QualIdentifier_ptr>(not_eq_term->left_term)) {
    if(TermConstant_ptr right_constant = dynamic_cast<TermConstant_ptr>(not_eq_term->right_term)) {
    	StringAutomaton_ptr temp,con;
      Variable_ptr var = symbol_table_->get_variable(left_var->getVarName());

      if(right_constant->getValue() == "") {
      	con = StringAutomaton::MakeAnyStringLengthGreaterThan(0);
      } else {
      	auto t1 = StringAutomaton::MakeAnyString();
      	auto t2 = StringAutomaton::MakeString(right_constant->getValue());
        con = t1->Difference(t2);
        delete t1;
        delete t2;
      }
      StringFormula_ptr formula = new StringFormula();
      formula->SetType(StringFormula::Type::VAR);
      formula->AddVariable(var->getName(),1);
      con->SetFormula(formula);
      Value_ptr val = new Value(con);
      bool result = symbol_table_->IntersectValue(var,val);
      delete val;
      setTermValue(not_eq_term, new Value(result));
      return;
    }
  }

  visit_children_of(not_eq_term);

  Value_ptr result = nullptr, param_left = getTermValue(not_eq_term->left_term), param_right = getTermValue(
      not_eq_term->right_term);

  if (Value::Type::BOOL_CONSTANT == param_left->getType() and Value::Type::BOOL_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getBoolConstant() not_eq param_right->getBoolConstant());
  } else if (Value::Type::INT_CONSTANT == param_left->getType()
      and Value::Type::INT_CONSTANT == param_right->getType()) {
    result = new Value(param_left->getIntConstant() not_eq param_right->getIntConstant());
  } else if (not (param_left->is_satisfiable() and param_right->is_satisfiable())) {
    result = new Value(false);
  } else {
    Value_ptr intersection = param_left->intersect(param_right);
    if (not intersection->is_satisfiable()) {
      result = new Value(true);
      delete intersection;
    } else if(param_left->isSingleValue() and param_right->isSingleValue() and intersection->is_satisfiable()) {
      result = new Value(false);
      delete intersection;
    } else {
      result = intersection;
    }
  }

  setTermValue(not_eq_term, result);
}

void ConstraintSolver::visitGt(Gt_ptr gt_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *gt_term;

  visit_children_of(gt_term);

  Value_ptr result = nullptr, param_left = getTermValue(gt_term->left_term), param_right = getTermValue(
      gt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() > param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isLessThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThan(param_right->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    }
  } else if(Value::Type::STRING_AUTOMATON == param_left->getType()) {
    if (Value::Type::STRING_AUTOMATON == param_right->getType()) {
      if(not param_left->getStringAutomaton()->IsAcceptingSingleString() or not param_right->getStringAutomaton()->IsAcceptingSingleString()) {
        LOG(FATAL) << "Unexpected comparison; both string automatons should be only accepting single strings";
      }
      result = new Value((param_left->getStringAutomaton()->GetAnAcceptingString() > param_right->getStringAutomaton()->GetAnAcceptingString()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *gt_term;
    } 
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *gt_term;
  }

  setTermValue(gt_term, result);
}

void ConstraintSolver::visitGe(Ge_ptr ge_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *ge_term;

  visit_children_of(ge_term);

  Value_ptr result = nullptr, param_left = getTermValue(ge_term->left_term), param_right = getTermValue(
      ge_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() >= param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isLessThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isGreaterThanOrEqual(param_right->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    }
  } else if(Value::Type::STRING_AUTOMATON == param_left->getType()) {
    if (Value::Type::STRING_AUTOMATON == param_right->getType()) {
      if(not param_left->getStringAutomaton()->IsAcceptingSingleString() or not param_right->getStringAutomaton()->IsAcceptingSingleString()) {
        LOG(FATAL) << "Unexpected comparison; both string automatons should be only accepting single strings";
      }
      result = new Value((param_left->getStringAutomaton()->GetAnAcceptingString() >= param_right->getStringAutomaton()->GetAnAcceptingString()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *ge_term;
    } 
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *ge_term;
  }

  setTermValue(ge_term, result);
}

void ConstraintSolver::visitLt(Lt_ptr lt_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *lt_term;

  visit_children_of(lt_term);

  Value_ptr result = nullptr, param_left = getTermValue(lt_term->left_term), param_right = getTermValue(
      lt_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() < param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isGreaterThan(param_left->getIntConstant()));
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThan(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThan(param_right->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    }
  } else if(Value::Type::STRING_AUTOMATON == param_left->getType()) {
    if (Value::Type::STRING_AUTOMATON == param_right->getType()) {
      if(not param_left->getStringAutomaton()->IsAcceptingSingleString() or not param_right->getStringAutomaton()->IsAcceptingSingleString()) {
        LOG(FATAL) << "Unexpected comparison; both string automatons should be only accepting single strings";
      }
      result = new Value((param_left->getStringAutomaton()->GetAnAcceptingString() < param_right->getStringAutomaton()->GetAnAcceptingString()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *lt_term;
    } 
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *lt_term;
  } 

  setTermValue(lt_term, result);
}

void ConstraintSolver::visitLe(Le_ptr le_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *le_term;

  visit_children_of(le_term);

  Value_ptr result = nullptr, param_left = getTermValue(le_term->left_term), param_right = getTermValue(
      le_term->right_term);

  if (Value::Type::INT_CONSTANT == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value((param_left->getIntConstant() <= param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_right->getIntAutomaton()->isGreaterThanOrEqual(param_left->getIntConstant()));
    } else {
      LOG(FATAL)<< "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else if (Value::Type::INT_AUTOMATON == param_left->getType()) {
    if (Value::Type::INT_CONSTANT == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThanOrEqual(param_right->getIntConstant()));
    } else if (Value::Type::INT_AUTOMATON == param_right->getType()) {
      result = new Value(param_left->getIntAutomaton()->isLessThanOrEqual(param_right->getIntAutomaton()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    }
  } else if(Value::Type::STRING_AUTOMATON == param_left->getType()) {
    if (Value::Type::STRING_AUTOMATON == param_right->getType()) {
      if(not param_left->getStringAutomaton()->IsAcceptingSingleString() or not param_right->getStringAutomaton()->IsAcceptingSingleString()) {
        LOG(FATAL) << "Unexpected comparison; both string automatons should be only accepting single strings";
      }
      result = new Value((param_left->getStringAutomaton()->GetAnAcceptingString() <= param_right->getStringAutomaton()->GetAnAcceptingString()));
    } else {
      LOG(FATAL) << "Unexpected right parameter: " << *param_right << " in " << *le_term;
    } 
  } else {
    LOG(FATAL) << "Unexpected left parameter: " << *param_left << " in " << *le_term;
  }

  setTermValue(le_term, result);
}

void ConstraintSolver::visitConcat(Concat_ptr concat_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *concat_term << " ...";

  Value_ptr result = nullptr, concat_value = nullptr, param = nullptr;

	if(Option::Solver::CONCAT_COLLAPSE_HEURISTIC) {
    if(concat_term->term_list->size() <= 10) {
      path_trace_.push_back(concat_term);
    } else {
      many_vars = true;
    }      
    for (auto& term_ptr : *(concat_term->term_list)) {
      visit(term_ptr);
      param = getTermValue(term_ptr);
      if (result == nullptr) {
        result = param->clone();
      } else {
        concat_value = result->concat(param);
        delete result;
        result = concat_value;
      }
    }
    if(concat_term->term_list->size() <= 10) {
      path_trace_.pop_back();
    }
    many_vars = false;
  } else {
    path_trace_.push_back(concat_term);
    for (auto& term_ptr : *(concat_term->term_list)) {
      visit(term_ptr);
      param = getTermValue(term_ptr);

      if (result == nullptr) {
        result = param->clone();
      } else {
        concat_value = result->concat(param);
        delete result;
        result = concat_value;
      }

    }
    path_trace_.pop_back();
  }

	setTermValue(concat_term, result);
}

void ConstraintSolver::visitIn(In_ptr in_term) {
//  if(symbol_table_->top_scope() == root_) {
  if(Term::Type::QUALIDENTIFIER == in_term->left_term->type() && Term::Type::TERMCONSTANT == in_term->right_term->type()) {
    auto left_var = dynamic_cast<QualIdentifier_ptr>(in_term->left_term);
    auto right_constant = dynamic_cast<TermConstant_ptr>(in_term->right_term);
    Variable_ptr var = symbol_table_->get_variable(left_var->getVarName());
    auto temp = StringAutomaton::MakeRegexAuto(right_constant->getValue());
    auto formula = new Theory::StringFormula();
    formula->AddVariable(left_var->getVarName(), 1);
    formula->SetType(Theory::StringFormula::Type::VAR);
    temp->SetFormula(formula);
    Value_ptr val = new Value(temp);
    bool result1 = symbol_table_->IntersectValue(var, val);
    setTermValue(in_term, new Value(result1));
    return;
  }

  visit_children_of(in_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *in_term;

  Value_ptr result = nullptr, param_left = getTermValue(in_term->left_term), param_right = getTermValue(
      in_term->right_term);

  if (Value::Type::STRING_AUTOMATON == param_left->getType()
      and Value::Type::STRING_AUTOMATON == param_right->getType()) {
    result = param_left->intersect(param_right);
  } else {
    LOG(FATAL)<< "unexpected parameter(s) of '" << *in_term << "' term";  // handle cases in a better way
  }

  setTermValue(in_term, result);
}

/**
 * TODO check all boolean string functions right hand side
 * if there is no variable involved we can do precise calculation
 * otherwise discuss?? if it is problem
 */

void ConstraintSolver::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_in_term;

  Value_ptr result = nullptr, param_left = getTermValue(not_in_term->left_term), param_right = getTermValue(
      not_in_term->right_term);

  if (Value::Type::STRING_AUTOMATON == param_left->getType()
      and Value::Type::STRING_AUTOMATON == param_right->getType()) {
    result = param_left->difference(param_right);
  } else {
    LOG(FATAL)<< "unexpected parameter(s) of '" << *not_in_term << "' term";  // handle cases in a better way
  }

  setTermValue(not_in_term, result);
}

void ConstraintSolver::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *len_term;
  Value_ptr result = nullptr, param = getTermValue(len_term->term);
  Theory::IntAutomaton_ptr int_auto = param->getStringAutomaton()->Length();

  if (int_auto->isAcceptingSingleInt()) {
    result = new Value(int_auto->getAnAcceptingInt());
    delete int_auto;
    int_auto = nullptr;
  } else {
    result = new Value(int_auto);
  }
  setTermValue(len_term, result);
}

void ConstraintSolver::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *contains_term;

  Value_ptr result = nullptr, param_subject = getTermValue(contains_term->subject_term), param_search = getTermValue(
      contains_term->search_term);
  result = new Value(param_subject->getStringAutomaton()->Contains(param_search->getStringAutomaton()));

  setTermValue(contains_term, result);
}

void ConstraintSolver::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_contains_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_contains_term->subject_term), param_search =
      getTermValue(not_contains_term->search_term);


  if (not (param_subject->is_satisfiable() and param_search->is_satisfiable())) {
    result = new Value(false);
  } else if (param_search->isSingleValue()) {
    Theory::StringAutomaton_ptr contains_auto = param_subject->getStringAutomaton()->Contains(
        param_search->getStringAutomaton());
    result = new Value(param_subject->getStringAutomaton()->Difference(contains_auto));
    delete contains_auto;
    contains_auto = nullptr;
  } else if (param_subject->isSingleValue()) {
    Theory::StringAutomaton_ptr sub_strings_auto = param_subject->getStringAutomaton()->SubStrings();
    Theory::StringAutomaton_ptr difference_auto = param_search->getStringAutomaton()->Difference(sub_strings_auto);
    delete sub_strings_auto;
    sub_strings_auto = nullptr;
    if (difference_auto->IsEmptyLanguage()) {
      result = new Value(Theory::StringAutomaton::MakePhi());
    } else {
      result = param_subject->clone();
    }
    delete difference_auto;
    difference_auto = nullptr;
  } else {
    // TODO if param_subject is a suffix automaton (all the strings accepted is actually substrings of largest length string),
    // there can be a more precise calculation instead of just cloning the subject
    result = param_subject->clone();
  }

  setTermValue(not_contains_term, result);
}

void ConstraintSolver::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *begins_term;

  Value_ptr result = nullptr, param_left = getTermValue(begins_term->subject_term), param_right = getTermValue(
      begins_term->search_term);

  result = new Value(param_left->getStringAutomaton()->Begins(param_right->getStringAutomaton()));

  setTermValue(begins_term, result);
}

void ConstraintSolver::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_begins_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_begins_term->subject_term), param_search = getTermValue(
      not_begins_term->search_term);

  if (param_search->isSingleValue()) {
    Theory::StringAutomaton_ptr begins_auto = param_subject->getStringAutomaton()->Begins(
        param_search->getStringAutomaton());
    result = new Value(param_subject->getStringAutomaton()->Difference(begins_auto));
    delete begins_auto;
    begins_auto = nullptr;
  } else if (param_subject->isSingleValue()) {
    Theory::StringAutomaton_ptr prefixes_auto = param_subject->getStringAutomaton()->Prefixes();
    Theory::StringAutomaton_ptr difference_auto = param_search->getStringAutomaton()->Difference(prefixes_auto);
    delete prefixes_auto;
    prefixes_auto = nullptr;
    if (difference_auto->IsEmptyLanguage()) {
      result = new Value(Theory::StringAutomaton::MakePhi());
    } else {
      result = param_subject->clone();
    }
    delete difference_auto;
    difference_auto = nullptr;
  } else {
    result = param_subject->clone();
  }

  setTermValue(not_begins_term, result);
}

void ConstraintSolver::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *ends_term;

  Value_ptr result = nullptr, param_left = getTermValue(ends_term->subject_term), param_right = getTermValue(
      ends_term->search_term);

  result = new Value(param_left->getStringAutomaton()->Ends(param_right->getStringAutomaton()));

  setTermValue(ends_term, result);
}

void ConstraintSolver::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_ends_term;

  Value_ptr result = nullptr, param_subject = getTermValue(not_ends_term->subject_term), param_search = getTermValue(
      not_ends_term->search_term);

  if (param_search->isSingleValue()) {
    Theory::StringAutomaton_ptr ends_auto = param_subject->getStringAutomaton()->Ends(
        param_search->getStringAutomaton());
    result = new Value(param_subject->getStringAutomaton()->Difference(ends_auto));
    delete ends_auto;
    ends_auto = nullptr;
  } else if (param_subject->isSingleValue()) {
    Theory::StringAutomaton_ptr suffixes_auto = param_subject->getStringAutomaton()->Suffixes();
    Theory::StringAutomaton_ptr difference_auto = param_search->getStringAutomaton()->Difference(suffixes_auto);
    delete suffixes_auto;
    suffixes_auto = nullptr;
    if (difference_auto->IsEmptyLanguage()) {
      result = new Value(Theory::StringAutomaton::MakePhi());
    } else {
      result = param_subject->clone();
    }
    delete difference_auto;
    difference_auto = nullptr;
  } else {
    result = param_subject->clone();
  }

  setTermValue(not_ends_term, result);
}

void ConstraintSolver::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);

  DVLOG(VLOG_LEVEL) << "visit: " << *index_of_term;

  Value_ptr result = nullptr, param_left = getTermValue(index_of_term->subject_term), param_right = getTermValue(
      index_of_term->search_term);

  Theory::IntAutomaton_ptr index_of_auto = nullptr;
  if(index_of_term->from_index != nullptr) {
    Value_ptr param_from_index = getTermValue(index_of_term->from_index);
    if(Value::Type::INT_AUTOMATON == param_from_index->getType()) {
      index_of_auto = param_left->getStringAutomaton()->IndexOf(param_right->getStringAutomaton(),param_from_index->getIntAutomaton());
    } else if(Value::Type::INT_CONSTANT == param_from_index->getType()) {
      index_of_auto = param_left->getStringAutomaton()->IndexOf(param_right->getStringAutomaton(),param_from_index->getIntConstant());
    } else {
      LOG(FATAL) << "handle more cases here";
    }
  } else {
    index_of_auto = param_left->getStringAutomaton()->IndexOf(param_right->getStringAutomaton());
  }


  if (index_of_auto->isAcceptingSingleInt()) {
    result = new Value(index_of_auto->getAnAcceptingInt());
    delete index_of_auto;
    index_of_auto = nullptr;
  } else {
    result = new Value(index_of_auto);
  }
  setTermValue(index_of_term, result);
}

void ConstraintSolver::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *last_index_of_term;

  Value_ptr result = nullptr, param_left = getTermValue(last_index_of_term->subject_term), param_right = getTermValue(
      last_index_of_term->search_term);

  Theory::IntAutomaton_ptr last_index_of_auto = param_left->getStringAutomaton()->LastIndexOf(
      param_right->getStringAutomaton());
  if (last_index_of_auto->isAcceptingSingleInt()) {
    result = new Value(last_index_of_auto->getAnAcceptingInt());
    delete last_index_of_auto;
    last_index_of_auto = nullptr;
  } else {
    result = new Value(last_index_of_auto);
  }
  setTermValue(last_index_of_term, result);
}

void ConstraintSolver::visitCharAt(CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *char_at_term;

  Value_ptr result = nullptr, param_subject = getTermValue(char_at_term->subject_term), param_index = getTermValue(
      char_at_term->index_term);
  if (Value::Type::INT_CONSTANT == param_index->getType()) {
    result = new Value(param_subject->getStringAutomaton()->CharAt(param_index->getIntConstant()));
  } else if (Value::Type::INT_AUTOMATON == param_index->getType()) {
    result = new Value(param_subject->getStringAutomaton()->CharAt(param_index->getIntAutomaton()));
  } else if (Value::Type::BINARYINT_AUTOMATON == param_index->getType()) {
    LOG(FATAL)<< "Handle this case";
  }

//  result->getStringAutomaton()->inspectAuto(false,true);
//  std::cin.get();

  setTermValue(char_at_term, result);
}

void ConstraintSolver::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *sub_string_term;
  Value_ptr result = nullptr, param_subject = getTermValue(sub_string_term->subject_term), param_start_index =
      getTermValue(sub_string_term->start_index_term);

  Value_ptr param_end_index = nullptr;
  if(sub_string_term->end_index_term != nullptr) {
    param_end_index = getTermValue(sub_string_term->end_index_term);
  }

  Theory::StringAutomaton_ptr substring_auto = nullptr;
  if(Value::Type::INT_CONSTANT == param_start_index->getType() and param_end_index == nullptr) {
    substring_auto = param_subject->getStringAutomaton()->SubString(param_start_index->getIntConstant());
  } else if(Value::Type::INT_AUTOMATON == param_start_index->getType() and Value::Type::INT_AUTOMATON == param_end_index->getType()) {
    substring_auto = param_subject->getStringAutomaton()->SubString(param_start_index->getIntAutomaton(),param_end_index->getIntAutomaton());
  } else if(Value::Type::INT_CONSTANT == param_start_index->getType() and Value::Type::INT_AUTOMATON == param_end_index->getType()) {
    substring_auto = param_subject->getStringAutomaton()->SubString(param_start_index->getIntConstant(),param_end_index->getIntAutomaton());
  } else if(Value::Type::INT_AUTOMATON == param_start_index->getType() and Value::Type::INT_CONSTANT == param_end_index->getType()) {
    substring_auto = param_subject->getStringAutomaton()->SubString(param_start_index->getIntAutomaton(),param_end_index->getIntConstant());
  } else if(Value::Type::INT_CONSTANT == param_start_index->getType() and Value::Type::INT_CONSTANT == param_end_index->getType()) {
    substring_auto = param_subject->getStringAutomaton()->SubString(param_start_index->getIntConstant(),param_end_index->getIntConstant());
  } else {
    LOG(FATAL) << "add more cases here";
  }

//  int start_index_value = 0;
//  // First calculate substring from start to end index
//  //Theory::StringAutomaton_ptr substring_auto = param_subject->getStringAutomaton()->clone();
//  Theory::IntAutomaton_ptr start_index_auto = nullptr;
//  if (Value::Type::INT_CONSTANT == param_start_index->getType()) {
//    start_index_value = param_start_index->getIntConstant();
//  } else {
//    LOG(FATAL) << "add more cases here";
//  }
//
//  // If there is an end index handle it
//  if (sub_string_term->end_index_term) {
//    param_end_index = getTermValue(sub_string_term->end_index_term);
//    Theory::StringAutomaton_ptr sub_str_start_auto = substring_auto;
//    substring_auto = nullptr;
//
//    // Based on the type handle it;
//    // TODO need to generalize the cases below, a substringhelper class can be used
//    if (Value::Type::BINARYINT_AUTOMATON == param_end_index->getType()) {
//      auto bin_end_index_auto = param_end_index->getBinaryIntAutomaton();
//      // if end index is a variable (TODO make sure it is always a variable)
//      QualIdentifier_ptr index_var = dynamic_cast<QualIdentifier_ptr>(sub_string_term->end_index_term);
//
//      Optimization::ConstraintQuerier query;
//      // checks if the integer parameter is an index of operation (currently works for indexof only)
//      if (index_var and bin_end_index_auto->GetFormula()->HasRelationToMixedTerm(index_var->getVarName())) {
//        auto relation = bin_end_index_auto->GetFormula()->GetRelationToMixedTerm(index_var->getVarName());
//        if (relation.first == Theory::ArithmeticFormula::Type::EQ and
//            query.is_param_equal_to(sub_string_term->subject_term, relation.second, 1)) {
//          // Refactor below flow into a function
//          auto positive_bin_end_index_var_auto = bin_end_index_auto->GetPositiveValuesFor(index_var->getVarName());
//          auto bin_end_index_var_auto = positive_bin_end_index_var_auto->GetBinaryAutomatonFor(index_var->getVarName());
//          delete positive_bin_end_index_var_auto;
//          positive_bin_end_index_var_auto = nullptr;
//          auto unary_end_index_var_auto = bin_end_index_var_auto->ToUnaryAutomaton();
//          delete bin_end_index_var_auto;
//          bin_end_index_var_auto = nullptr;
//          auto string_len_end_index_auto = unary_end_index_var_auto->toIntAutomaton(param_subject->getStringAutomaton()->get_number_of_bdd_variables(), false);
//          delete unary_end_index_var_auto;
//          unary_end_index_var_auto = nullptr;
//
//          // TODO more cases here to handle
//          auto string_search_term = query.get_parameter(relation.second, 2);
//          auto string_search_term_value = getTermValue(string_search_term);
//          if (string_search_term_value == nullptr) {
//            visit(string_search_term); // generate automata for it
//            string_search_term_value = getTermValue(string_search_term);
//          }
//
//          // if there is an additional from index parameter, we need to consider it
//          // I guess the best way to handle it is to add a substring variable from from
//          // index and then to implement the rest
//          substring_auto = sub_str_start_auto->SubString(string_len_end_index_auto, string_search_term_value->getStringAutomaton());
//          delete string_len_end_index_auto;
//          string_len_end_index_auto = nullptr;
//        }
//      }
//    } else if(Value::Type::INT_AUTOMATON == param_end_index->getType()) {
//      Theory::IntAutomaton_ptr param_end_index_auto = param_end_index->getIntAutomaton();
//      substring_auto = sub_str_start_auto->SubString(start_index_value,param_end_index_auto);
//    } else if(Value::Type::INT_CONSTANT == param_start_index->getType()) {
//      int end_index_value = param_end_index->getIntConstant();
//      substring_auto = sub_str_start_auto->SubString(start_index_value,end_index_value);
//    } else {
//      LOG(FATAL) << "implement and fix me";
//    }
//  } else {
//    LOG(FATAL) << "implement me";
//  }

  CHECK_NOTNULL(substring_auto);
  result = new Value(substring_auto);
  setTermValue(sub_string_term, result);
}

void ConstraintSolver::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_upper_term;

  Value_ptr param = getTermValue(to_upper_term->subject_term);
  Value_ptr result = new Value(param->getStringAutomaton()->ToUpperCase());

  setTermValue(to_upper_term, result);
}

void ConstraintSolver::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_lower_term;

  Value_ptr param = getTermValue(to_lower_term->subject_term);
  Value_ptr result = new Value(param->getStringAutomaton()->ToLowerCase());

  setTermValue(to_lower_term, result);
}

void ConstraintSolver::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *trim_term;

  Value_ptr param = getTermValue(trim_term->subject_term);
  Value_ptr result = new Value(param->getStringAutomaton()->Trim());

  setTermValue(trim_term, result);

}

void ConstraintSolver::visitToString(ToString_ptr to_string_term) {
  visit_children_of(to_string_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_string_term;

  Value_ptr param = getTermValue(to_string_term->subject_term);
  Value_ptr result = nullptr;
  if (Value::Type::INT_CONSTANT == param->getType()) {
    std::stringstream ss;
    ss << param->getIntConstant();
    result = new Value(StringAutomaton::MakeString(ss.str()));
  } else {
    auto unary_auto = param->getIntAutomaton()->toUnaryAutomaton();
    auto str_auto = unary_auto->toStringAutomaton();

    delete unary_auto;

    // if param has negative one, then also return empty string
    if(param->getIntAutomaton()->hasNegative1()) {
      auto empty_string_auto = Theory::StringAutomaton::MakeEmptyString();
      auto temp_auto = str_auto->Union(empty_string_auto);
      delete str_auto;
      delete empty_string_auto;
      str_auto = temp_auto;
    }
    result = new Value(str_auto);
  }

//  result->getStringAutomaton()->inspectAuto(false,true);
//  std::cin.get();

  setTermValue(to_string_term, result);
}

void ConstraintSolver::visitToInt(ToInt_ptr to_int_term) {
  visit_children_of(to_int_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *to_int_term;

  Value_ptr param = getTermValue(to_int_term->subject_term);

  Theory::IntAutomaton_ptr int_auto = param->getStringAutomaton()->ParseToIntAutomaton();
//  param->getStringAutomaton()->inspectAuto(false,true);
//  int_auto->inspectAuto(false,true);
//  std::cin.get();
  Value_ptr result = nullptr;
  if (int_auto->isAcceptingSingleInt()) {
    result = new Value(int_auto->getAnAcceptingInt());
  } else {
    result = new Value(int_auto);
  }

//  int_auto->inspectAuto(false,true);
//  std::cin.get();

  setTermValue(to_int_term, result);
}

void ConstraintSolver::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *replace_term;

  Value_ptr param_subject = getTermValue(replace_term->subject_term), param_search = getTermValue(
      replace_term->search_term), param_replace = getTermValue(replace_term->replace_term);

  Value_ptr result = new Value(
      param_subject->getStringAutomaton()->Replace(param_search->getStringAutomaton(),
                                                   param_replace->getStringAutomaton()));

  setTermValue(replace_term, result);
}

void ConstraintSolver::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
  LOG(FATAL)<< "implement me";
}

void ConstraintSolver::visitIte(Ite_ptr ite_term) {
}

void ConstraintSolver::visitIsDigit(IsDigit_ptr is_digit_term) {
  LOG(FATAL) << "IMPLEMENT ME";
}

void ConstraintSolver::visitToCode(ToCode_ptr to_code_term) {
  LOG(FATAL) << "IMPLEMENT ME";
}

void ConstraintSolver::visitFromCode(FromCode_ptr from_code_term) {
  LOG(FATAL) << "IMPLEMENT ME";
}

void ConstraintSolver::visitReConcat(ReConcat_ptr re_concat_term) {
}

void ConstraintSolver::visitToRegex(ToRegex_ptr to_regex_term) {
}

void ConstraintSolver::visitReUnion(ReUnion_ptr re_union_term) {
}

void ConstraintSolver::visitReInter(ReInter_ptr re_inter_term) {
}

void ConstraintSolver::visitReStar(ReStar_ptr re_star_term) {
}

void ConstraintSolver::visitRePlus(RePlus_ptr re_plus_term) {
}

void ConstraintSolver::visitReOpt(ReOpt_ptr re_opt_term) {
}

void ConstraintSolver::visitReLoop(ReLoop_ptr re_loop_term) {

}

void ConstraintSolver::visitUnknownTerm(Unknown_ptr unknown_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *unknown_term;
  LOG(WARNING)<< "operation is not known, over-approximate params: " << *(unknown_term->term);

  path_trace_.push_back(unknown_term);
  for (auto& term_ptr : *(unknown_term->term_list)) {
    visit(term_ptr);
  }
  path_trace_.pop_back();
  Value_ptr result = new Value(Theory::StringAutomaton::MakeAnyString());

  setTermValue(unknown_term, result);
}

void ConstraintSolver::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void ConstraintSolver::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term << " = " << qi_term->getVarName();

  Variable_ptr variable = symbol_table_->get_variable(qi_term->getVarName());

  Value_ptr variable_value = symbol_table_->get_value(variable);

  Value_ptr result = nullptr;
  if (Value::Type::STRING_AUTOMATON == variable_value->getType()) {
    result = new Value(variable_value->getStringAutomaton()->GetAutomatonForVariable(qi_term->getVarName()));
    // result->getStringAutomaton()->inspectAuto(true,false);
    // std::cin.get();
  } else if (Value::Type::BINARYINT_AUTOMATON == variable_value->getType()) {
  	// TODO baki: added for charat may need to fix it
    auto var_auto = variable_value->getBinaryIntAutomaton()->GetBinaryAutomatonFor(qi_term->getVarName());
    auto positive_var_auto = var_auto->GetPositiveValuesFor(qi_term->getVarName());
    auto unary_auto = positive_var_auto->ToUnaryAutomaton();
    result = new Value(unary_auto->toIntAutomaton(8,var_auto->HasNegative1()));
    delete var_auto;
    delete positive_var_auto;
    delete unary_auto;
  } else
  {
    result = variable_value->clone();
  }


  setTermValue(qi_term, result);
  if(Option::Solver::CONCAT_COLLAPSE_HEURISTIC) {
    if(!many_vars) {
      setVariablePath(qi_term);
    }
  } else {
    setVariablePath(qi_term);
  }
}

void ConstraintSolver::visitTermConstant(TermConstant_ptr term_constant) {
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  Value_ptr result = nullptr;

  switch (term_constant->getValueType()) {
    case Primitive::Type::BOOL: {
      bool b;
      std::istringstream(term_constant->getValue()) >> std::boolalpha >> b;
      result = new Value(b);
      break;
    }
    case Primitive::Type::BINARY:
      LOG(FATAL)<< "implement me";
      break;
      case Primitive::Type::HEXADECIMAL:
      LOG(FATAL) << "implement me";
      break;
      case Primitive::Type::DECIMAL:
      LOG(FATAL) << "implement me";
      break;
      case Primitive::Type::NUMERAL:
      // TODO we may get rid of constants if the automaton implementation is good enough
      result = new Value(std::stoi(term_constant->getValue()));
      break;
      case Primitive::Type::STRING:
      // TODO instead we may use string constants before going into automaton
      // and keep it unless we need automaton
      // this may complicate the code with a perf gain ??
      result = new Value(Theory::StringAutomaton::MakeString(term_constant->getValue()));
      break;
      case Primitive::Type::REGEX:
      result = new Value(Theory::StringAutomaton::MakeRegexAuto(term_constant->getValue()));
      break;
      default:
      LOG(FATAL) << "unhandled term constant: " << *term_constant;
      break;
    }

  setTermValue(term_constant, result);
}

void ConstraintSolver::visitIdentifier(Identifier_ptr identifier) {
}

void ConstraintSolver::visitPrimitive(Primitive_ptr primitive) {
}

void ConstraintSolver::visitTVariable(TVariable_ptr t_variable) {
}

void ConstraintSolver::visitTBool(TBool_ptr t_bool) {
}

void ConstraintSolver::visitTInt(TInt_ptr t_int) {
}

void ConstraintSolver::visitTString(TString_ptr t_string) {
}

void ConstraintSolver::visitVariable(Variable_ptr variable) {
}

void ConstraintSolver::visitSort(Sort_ptr sort) {
}

void ConstraintSolver::visitAttribute(Attribute_ptr attribute) {
}

void ConstraintSolver::visitSortedVar(SortedVar_ptr sorted_var) {
}

void ConstraintSolver::visitVarBinding(VarBinding_ptr var_binding) {
}

/**
 *
 */
Value_ptr ConstraintSolver::getTermValue(Term_ptr term) {

  auto iter = term_values_.find(term);
  if (iter != term_values_.end()) {
    return iter->second;
  }

  DVLOG(VLOG_LEVEL) << "value is not computed for term: " << *term;
  return nullptr;
}

bool ConstraintSolver::setTermValue(Term_ptr term, Value_ptr value) {
  auto result = term_values_.insert(std::make_pair(term, value));
  if (result.second == false) {
    LOG(FATAL)<< "value is already computed for term: " << *term;
  }
  return result.second;
}

void ConstraintSolver::clearTermValue(SMT::Term_ptr term) {
  auto pair = term_values_.find(term);
  if (pair != term_values_.end()) {
    delete pair->second;
    term_values_.erase(pair);
  }
}

void ConstraintSolver::clearTermValuesAndLocalLetVars() {
  for (auto& entry : term_values_) {
    delete entry.second;
  }
  term_values_.clear();
  symbol_table_->clearLetScopes();
}

void ConstraintSolver::setVariablePath(QualIdentifier_ptr qi_term) {
  path_trace_.push_back(qi_term);
  variable_path_table_.push_back(std::vector<Term_ptr>());
  auto iter = variable_path_table_.back().begin();
  variable_path_table_.back().insert(iter, path_trace_.rbegin(), path_trace_.rend());
  path_trace_.pop_back();
}

bool ConstraintSolver::update_variables() {
  if (variable_path_table_.size() == 0) {
    return true;
  }
  VariableValueComputer value_updater(symbol_table_, variable_path_table_, term_values_);
  value_updater.start();
  auto is_satisfiable = value_updater.is_satisfiable();
  variable_path_table_.clear();
  // TODO should we delete term_values ???
  // TODO refactor relation - single interaction
  return is_satisfiable;
}

void ConstraintSolver::visit_children_of(Term_ptr term) {
  path_trace_.push_back(term);
  Visitor::visit_children_of(term);
  path_trace_.pop_back();
}

bool ConstraintSolver::check_and_visit(Term_ptr term) {
  if ((Term::Type::OR not_eq term->type()) and (Term::Type::AND not_eq term->type()) and (Term::Type::EXISTS not_eq term->type())) {
    if (constraint_information_->has_arithmetic_constraint(term)) {  // if arithmetic constraint and has string terms
      bool is_satisfiable = true;
      if (arithmetic_constraint_solver_.has_string_terms(term)) {
        DVLOG(VLOG_LEVEL) << "Mixed Linear Arithmetic Constraint";
        is_satisfiable = process_mixed_integer_string_constraints_in(term);
      } else {
      	DVLOG(VLOG_LEVEL) << "Arithmetic Constraint";
      }
      return is_satisfiable;
    } else if (constraint_information_->has_string_constraint(term)) {
      DVLOG(VLOG_LEVEL) << "Mixed Multi- and Single- Track String Automata Constraint: " << *term;
      return true;  // should be checked already
    }
  }
  visit(term);
  auto param = getTermValue(term);
  return param->is_satisfiable();
}

bool ConstraintSolver::process_mixed_integer_string_constraints_in(Term_ptr term) {
  UnaryAutomaton_ptr string_term_unary_auto = nullptr;
  BinaryIntAutomaton_ptr string_term_binary_auto = nullptr, updated_arith_auto = nullptr;
  IntAutomaton_ptr updated_int_auto = nullptr;
  bool has_minus_one = false;
  int number_of_variables_for_int_auto;
  bool is_satisfiable = true;
  bool delete_extra_arithmetic_result = false;
  // get term value returns result from the symbol table (should return)
  auto arithmetic_result = arithmetic_constraint_solver_.get_term_value(term);
  for (auto& string_term : arithmetic_constraint_solver_.get_string_terms_in(term)) {
    visit(string_term);

    auto string_term_result = getTermValue(string_term);
    is_satisfiable = string_term_result->is_satisfiable();
    
    if (not is_satisfiable) {
      auto binary_auto = arithmetic_result->getBinaryIntAutomaton();
      arithmetic_result = new Value(
          BinaryIntAutomaton::MakePhi(binary_auto->GetFormula()->clone(), binary_auto->is_natural_number()));
      arithmetic_constraint_solver_.set_group_value(term, arithmetic_result);
      break;
    }

    std::string string_term_var_name = symbol_table_->get_var_name_for_expression(string_term, Variable::Type::INT);
    if (Value::Type::INT_AUTOMATON == string_term_result->getType()) {
      has_minus_one = string_term_result->getIntAutomaton()->hasNegative1();
      number_of_variables_for_int_auto = string_term_result->getIntAutomaton()->get_number_of_bdd_variables();
      // first convert integer result to unary, then unary to binary
      string_term_unary_auto = string_term_result->getIntAutomaton()->toUnaryAutomaton();
      string_term_binary_auto = string_term_unary_auto->toBinaryIntAutomaton(
          string_term_var_name, arithmetic_result->getBinaryIntAutomaton()->GetFormula()->clone(), has_minus_one);
      delete string_term_unary_auto;
      string_term_unary_auto = nullptr;
    } else if (Value::Type::INT_CONSTANT == string_term_result->getType()) {
      int value = string_term_result->getIntConstant();
      has_minus_one = (value < 0);
      number_of_variables_for_int_auto = Theory::IntAutomaton::DEFAULT_NUM_OF_VARIABLES;
      string_term_binary_auto = Theory::BinaryIntAutomaton::MakeAutomaton(
          value, string_term_var_name, arithmetic_result->getBinaryIntAutomaton()->GetFormula()->clone(), true);
    } else {
      LOG(FATAL)<< "unexpected type";
    }

    // update the stored binary int auto with new string term results
    updated_arith_auto = arithmetic_result->getBinaryIntAutomaton()->Intersect(string_term_binary_auto);
    delete string_term_binary_auto;
    string_term_binary_auto = nullptr;

    if(delete_extra_arithmetic_result) {
    	delete arithmetic_result;
    }
    arithmetic_result = new Value(updated_arith_auto);
    delete_extra_arithmetic_result = true;
    is_satisfiable = arithmetic_constraint_solver_.set_group_value(term, arithmetic_result);  // in turn, update group variable

    if (not is_satisfiable) {
      break;
    }

    // 2- update string term result, since we first update binary binary automaton it may only contain
    // numbers >= -1 (values a string constraint can return as an integer)
    string_term_binary_auto = updated_arith_auto->GetBinaryAutomatonFor(string_term_var_name);

    if (has_minus_one) {
      has_minus_one = string_term_binary_auto->HasNegative1();
      BinaryIntAutomaton_ptr positive_values_auto = string_term_binary_auto->GetPositiveValuesFor(string_term_var_name);
      delete string_term_binary_auto;
      string_term_binary_auto = positive_values_auto;
    }

    string_term_unary_auto = string_term_binary_auto->ToUnaryAutomaton();
    delete string_term_binary_auto;
    string_term_binary_auto = nullptr;
    updated_int_auto = string_term_unary_auto->toIntAutomaton(number_of_variables_for_int_auto, has_minus_one);
    delete string_term_unary_auto;
    string_term_unary_auto = nullptr;
    clearTermValue(string_term);
    string_term_result = new Value(updated_int_auto);
    setTermValue(string_term, string_term_result);

    // 3 - update variables involved in string term
    is_satisfiable = update_variables();
    if (not is_satisfiable) {
      auto binary_auto = arithmetic_result->getBinaryIntAutomaton();
      arithmetic_result = new Value(
          BinaryIntAutomaton::MakePhi(binary_auto->GetFormula()->clone(), binary_auto->is_natural_number()));
      arithmetic_constraint_solver_.set_group_value(term, arithmetic_result);
      break;
    }

  }
  if(delete_extra_arithmetic_result) {
		delete arithmetic_result;
	}

  return is_satisfiable;
}

} /* namespace Solver */
} /* namespace Vlab */
