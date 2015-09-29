/*
 * Initializer.cpp
 *
 *  Created on: Apr 27, 2015
 *      Author: baki
 */

#include "Initializer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int Initializer::VLOG_LEVEL = 19;

Initializer::Initializer(Script_ptr script, SymbolTable_ptr symbol_table)
        : root(script), symbol_table(symbol_table) {
}

Initializer::~Initializer() {
}

void Initializer::start() {
  CHECK_NOTNULL(root);
  visit(root);
  end();
}

void Initializer::end() {
  if (VLOG_IS_ON(19)) {
    for (auto& pair : symbol_table->getVariables()) {
      DVLOG(VLOG_LEVEL) << *pair.second;
    }
  }
}

void Initializer::visitScript(Script_ptr script) {

  CommandList_ptr commands = script->command_list;

  for (auto iter = commands->begin(); iter != commands->end();) {
    if ((*iter)->getType() != Command::Type::ASSERT) {
      visit(*iter);
      delete (*iter);
      iter = commands->erase(iter);
    } else {
      iter++;
    }
  }

  verifyVariableDefinitions();
}

void Initializer::visitCommand(Command_ptr command) {

  switch (command->getType()) {
  case Command::Type::DECLARE_FUN: {
    visit_children_of(command);
    CHECK_EQ(1, primitives.size())<< "Expecting one symbol name.";
    CHECK_EQ(1, sorts.size())<< "Currently supports only functions with no arguments.";

    Primitive_ptr primitive = primitives.top();
    primitives.pop();
    Sort_ptr sort = sorts.top();
    sorts.pop();
    Variable_ptr variable = new Variable(primitive, sort->var_type->getType());
    symbol_table->addVariable(variable);

    break;
  }
  case Command::Type::CHECK_SAT: {
    visit_children_of(command);
    if (primitives.size() == 1) {
      Primitive_ptr primitive = primitives.top();
      primitives.pop();
      Variable_ptr variable = symbol_table->getVariable(primitive->getData());
      variable->setSymbolic(true);
      DVLOG(VLOG_LEVEL) << *variable << " is changed to a symbolic var.";
    }
    CHECK_EQ(0, primitives.size())<< "unexpected primitive left.";
    break;
  }
  case Command::Type::CHECK_SAT_AND_COUNT: {
    visit_children_of(command);
    if (primitives.size() == 1) {
      Primitive_ptr primitive = primitives.top();
      primitives.pop();
      int bound = std::stoi(primitive->getData());
      symbol_table->setBound(bound);
      DVLOG(VLOG_LEVEL) << "Model count bound: " << bound;
    } else if (primitives.size() == 2) {
      Primitive_ptr primitive = primitives.top();
      primitives.pop();
      Variable_ptr variable = symbol_table->getVariable(primitive->getData());
      variable->setSymbolic(true);
      DVLOG(VLOG_LEVEL) << *variable << " is changed to a symbolic var.";
      primitive = primitives.top();
      primitives.pop();
      int bound = std::stoi(primitive->getData());
      symbol_table->setBound(bound);
      DVLOG(VLOG_LEVEL) << "Model count bound: " << bound;
    }
    CHECK_EQ(0, primitives.size())<< "unexpected primitive left.";
    break;
  }
  case Command::Type::ASSERT: {
    break;
  }
  default:
    LOG(WARNING)<< "'" << *command<< "' is not handled, skipping; contact us for any questions.";
    break;
  }
}

void Initializer::visitAssert(Assert_ptr assert_command) {
}

void Initializer::visitTerm(Term_ptr term) {
}

void Initializer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void Initializer::visitExists(Exists_ptr exists_term) {
}

void Initializer::visitForAll(ForAll_ptr for_all_term) {
}

void Initializer::visitLet(Let_ptr let_term) {
}

void Initializer::visitAnd(And_ptr and_term) {
}

void Initializer::visitOr(Or_ptr or_term) {
}

void Initializer::visitNot(Not_ptr not_term) {
}

void Initializer::visitUMinus(UMinus_ptr u_minus_term) {
}

void Initializer::visitMinus(Minus_ptr minus_term) {
}

void Initializer::visitPlus(Plus_ptr plus_term) {
}

void Initializer::visitEq(Eq_ptr eq_term) {
}

void Initializer::visitNotEq(NotEq_ptr not_eq_term) {
}

void Initializer::visitGt(Gt_ptr gt_term) {
}

void Initializer::visitGe(Ge_ptr ge_term) {
}

void Initializer::visitLt(Lt_ptr lt_term) {
}

void Initializer::visitLe(Le_ptr le_term) {
}

void Initializer::visitConcat(Concat_ptr concat_term) {
}

void Initializer::visitIn(In_ptr in_term) {
}

void Initializer::visitNotIn(NotIn_ptr not_in_term) {
}

void Initializer::visitLen(Len_ptr len_term) {
}

void Initializer::visitContains(Contains_ptr contains_term) {
}

void Initializer::visitNotContains(NotContains_ptr not_contains_term) {
}

void Initializer::visitBegins(Begins_ptr begins_term) {
}

void Initializer::visitNotBegins(NotBegins_ptr not_begins_term) {
}

void Initializer::visitEnds(Ends_ptr ends_term) {
}

void Initializer::visitNotEnds(NotEnds_ptr not_ends_term) {
}


void Initializer::visitIndexOf(IndexOf_ptr index_of_term) {
}

void Initializer::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
}

void Initializer::visitCharAt(SMT::CharAt_ptr char_at_term) {
}

void Initializer::visitSubString(SMT::SubString_ptr sub_string_term) {
}

void Initializer::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
}

void Initializer::visitToLower(SMT::ToLower_ptr to_lower_term) {
}

void Initializer::visitTrim(SMT::Trim_ptr trim_term) {
}

void Initializer::visitReplace(Replace_ptr replace_term) {
}

void Initializer::visitCount(Count_ptr count_term) {
}

void Initializer::visitIte(Ite_ptr ite_term) {
}

void Initializer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void Initializer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void Initializer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void Initializer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void Initializer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void Initializer::visitTermConstant(TermConstant_ptr term_constant) {
}

void Initializer::visitIdentifier(Identifier_ptr identifier) {
}

void Initializer::visitPrimitive(Primitive_ptr primitive) {
  primitives.push(primitive);
}

void Initializer::visitTVariable(TVariable_ptr t_variable) {
}

void Initializer::visitTBool(TBool_ptr t_bool) {
}

void Initializer::visitTInt(TInt_ptr t_int) {
}

void Initializer::visitTString(TString_ptr t_string) {
}

void Initializer::visitVariable(Variable_ptr variable) {
}

void Initializer::visitSort(Sort_ptr sort) {
  sorts.push(sort);
}

void Initializer::visitAttribute(Attribute_ptr attribute) {
}

void Initializer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void Initializer::visitVarBinding(VarBinding_ptr var_binding) {
}

void Initializer::verifyVariableDefinitions() {
  bool is_symbolic = false;
  VariableMap variable_map = symbol_table->getVariables();
  Variable_ptr variable = variable_map.begin()->second;
  for (auto& pair : variable_map) {
    is_symbolic = pair.second->isSymbolic();
    if (is_symbolic) {
      variable = pair.second;
      break;
    }
    switch (variable->getType()) {
    case Variable::Type::BOOL: {
      variable = pair.second;
      break;
    }
    case Variable::Type::INT: {
      if (pair.second->getType() != Variable::Type::BOOL) {
        variable = pair.second;
      }
      break;
    }
    case Variable::Type::STRING: {
      if (pair.second->getType() == Variable::Type::STRING) {
        variable = pair.second;
      }
      break;
    }
    default:
      break;
    }
  }
  if (not is_symbolic) {
    variable->setSymbolic(true);
    LOG(INFO)<<"No target var defined by user; setting target var: " << *variable;
  }
}

}
/* namespace Solver */
} /* namespace Vlab */
