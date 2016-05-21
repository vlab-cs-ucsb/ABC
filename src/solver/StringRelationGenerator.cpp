//
// Created by will on 3/4/16.
//

#include "StringRelationGenerator.h"

namespace Vlab {
namespace Solver {

using namespace SMT;
using namespace Theory;

const int StringRelationGenerator::VLOG_LEVEL = 14;

StringRelationGenerator::StringRelationGenerator(Script_ptr script, SymbolTable_ptr st)
  : root(script), symbol_table(st) {
}

StringRelationGenerator::~StringRelationGenerator() {
  // delete var track map ptr?
}

void StringRelationGenerator::start() {
  DVLOG(VLOG_LEVEL) << "String relation extraction starts";
  visit(root);
  end();
}

void StringRelationGenerator::end() {
}

void StringRelationGenerator::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void StringRelationGenerator::visitCommand(Command_ptr command) {

}

void StringRelationGenerator::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void StringRelationGenerator::visitTerm(Term_ptr term) {
}

void StringRelationGenerator::visitExclamation(Exclamation_ptr exclamation) {
}

void StringRelationGenerator::visitExists(Exists_ptr exists_term) {
}

void StringRelationGenerator::visitForAll(ForAll_ptr for_all_term) {
}

void StringRelationGenerator::visitLet(Let_ptr let_term) {
}

void StringRelationGenerator::visitAnd(And_ptr and_term) {
  visit_children_of(and_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *and_term;
}

void StringRelationGenerator::visitOr(Or_ptr or_term) {
  for (auto &term : *(or_term->term_list)) {
    visit(term);
  }
  DVLOG(VLOG_LEVEL) << "visit: " << *or_term;

}

void StringRelationGenerator::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_term;
  // do shit here
}

void StringRelationGenerator::visitUMinus(UMinus_ptr uminus_term) {
}

void StringRelationGenerator::visitMinus(Minus_ptr minus_term) {
}

void StringRelationGenerator::visitPlus(Plus_ptr plus_term) {
}

void StringRelationGenerator::visitTimes(Times_ptr times_term) {
}

void StringRelationGenerator::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *eq_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr,
                     relation = nullptr;
  left_relation = getTermRelation(eq_term->left_term);
  right_relation = getTermRelation(eq_term->right_term);

  if(left_relation not_eq nullptr and right_relation not_eq nullptr) {
    if(left_relation->getType() == StringRelation::Type::VAR &&
            right_relation->getType() == StringRelation::Type::VAR) {
      relation = left_relation->combine(right_relation);
      relation->setType(StringRelation::Type::EQ);
      deleteTermRelation(eq_term->left_term);
      deleteTermRelation(eq_term->right_term);
      setTermRelation(eq_term,relation);
    }
  }
}

void StringRelationGenerator::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
  DVLOG(VLOG_LEVEL) << "visit: " << *not_eq_term;
  StringRelation_ptr left_relation = nullptr, right_relation = nullptr,
                     relation = nullptr;
  left_relation = getTermRelation(not_eq_term->left_term);
  right_relation = getTermRelation(not_eq_term->right_term);

  if(left_relation not_eq nullptr and right_relation not_eq nullptr) {
    if(left_relation->getType() == StringRelation::Type::VAR &&
            right_relation->getType() == StringRelation::Type::VAR) {
      relation = left_relation->combine(right_relation);
      relation->setType(StringRelation::Type::NOTEQ);
      deleteTermRelation(not_eq_term->left_term);
      deleteTermRelation(not_eq_term->right_term);
      setTermRelation(not_eq_term,relation);
    }
  }
}

void StringRelationGenerator::visitGt(Gt_ptr gt_term) {
}

void StringRelationGenerator::visitGe(Ge_ptr ge_term) {
}

void StringRelationGenerator::visitLt(Lt_ptr lt_term) {
}

void StringRelationGenerator::visitLe(Le_ptr le_term) {
}

void StringRelationGenerator::visitConcat(Concat_ptr concat_term) {
}

void StringRelationGenerator::visitIn(In_ptr in_term) {
  // do shit
}

void StringRelationGenerator::visitNotIn(NotIn_ptr not_in_term) {
  // do shit
}

void StringRelationGenerator::visitLen(Len_ptr len_term) {
  // do shit
}

void StringRelationGenerator::visitContains(Contains_ptr contains_term) {
  // do shit
}

void StringRelationGenerator::visitNotContains(NotContains_ptr not_contains_term) {
  // do shit
}

void StringRelationGenerator::visitBegins(Begins_ptr begins_term) {
  // do shit
}

void StringRelationGenerator::visitNotBegins(NotBegins_ptr not_begins_term) {
  // do shit
}

void StringRelationGenerator::visitEnds(Ends_ptr ends_term) {
  // do shit
}

void StringRelationGenerator::visitNotEnds(NotEnds_ptr not_ends_term) {
  // do shit
}

void StringRelationGenerator::visitIndexOf(IndexOf_ptr index_of_term) {
  // do shit
}

void StringRelationGenerator::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  // do shit
}

void StringRelationGenerator::visitCharAt(CharAt_ptr char_at_term) {
  // do shit
}

void StringRelationGenerator::visitSubString(SubString_ptr sub_string_term) {
  // do shit
}

void StringRelationGenerator::visitToUpper(ToUpper_ptr to_upper_term) {
  // do shit
}

void StringRelationGenerator::visitToLower(ToLower_ptr to_lower_term) {
  // do shit
}

void StringRelationGenerator::visitTrim(Trim_ptr trim_term) {
  // do shit
}

void StringRelationGenerator::visitToString(ToString_ptr to_string_term) {
}

void StringRelationGenerator::visitToInt(ToInt_ptr to_int_term) {
}

void StringRelationGenerator::visitReplace(Replace_ptr replace_term) {
  // do shit
}

void StringRelationGenerator::visitCount(Count_ptr count_term) {
  // do shit
}

void StringRelationGenerator::visitIte(Ite_ptr ite_term) {
  // do shit
}

void StringRelationGenerator::visitReConcat(ReConcat_ptr reconcat_term) {
  // do shit
}

void StringRelationGenerator::visitToRegex(ToRegex_ptr to_regex_term) {
  // do shit
}

void StringRelationGenerator::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void StringRelationGenerator::visitAsQualIdentifier(AsQualIdentifier_ptr as_qual_id_term) {
}

void StringRelationGenerator::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  StringRelation_ptr str_rel = nullptr;
  DVLOG(VLOG_LEVEL) << "visit: " << *qi_term;
  Variable_ptr variable = symbol_table->getVariable(qi_term->getVarName());

  if (Variable::Type::STRING == variable->getType()) {
    str_rel = new StringRelation();
    // track set later, 0 for now
    str_rel->addVariable(variable->getName(),0);
    str_rel->setType(StringRelation::Type::VAR);
  }
  setTermRelation(qi_term,str_rel);
}

void StringRelationGenerator::visitTermConstant(TermConstant_ptr term_constant) {
  StringRelation_ptr str_rel = nullptr;
  DVLOG(VLOG_LEVEL) << "visit: " << *term_constant;

  str_rel = new StringRelation();
  str_rel->addVariable(variable->getName(),-1);
  str_rel->setType(StringRelation::Type::VAR); // misnomer, should be constant

  setTermRelation(qi_term,str_rel);
}

void StringRelationGenerator::visitSort(Sort_ptr sort_term) {
}

void StringRelationGenerator::visitTVariable(TVariable_ptr tvar_term) {
}

void StringRelationGenerator::visitTBool(TBool_ptr tbool_term) {
}

void StringRelationGenerator::visitTInt(TInt_ptr tint_term) {
}

void StringRelationGenerator::visitTString(TString_ptr tstring_term) {
}

void StringRelationGenerator::visitAttribute(Attribute_ptr tattr_term) {
}

void StringRelationGenerator::visitSortedVar(SortedVar_ptr sorted_var_term) {
}

void StringRelationGenerator::visitVarBinding(VarBinding_ptr var_binding_term) {
}

void StringRelationGenerator::visitIdentifier(Identifier_ptr id_term) {
}

void StringRelationGenerator::visitPrimitive(Primitive_ptr prim_term) {
}

void StringRelationGenerator::visitVariable(Variable_ptr var_term) {
  // do shit?
}

StringRelation_ptr StringRelationGenerator::getTermRelation(Term_ptr term) {
  auto iter = relations.find(term);
  if(iter == relations.end()) {
    return nullptr;
  }
  return iter->second;
}

bool StringRelationGenerator::setTermRelation(Term_ptr term, Theory::StringRelation_ptr str_rel) {
  auto result = relations.insert(std::make_pair(term,str_rel));
  if(result.second == false) {
    LOG(FATAL) << "relation is already computed for term: " << *term;
  }
  return result.second;
}

void StringRelationGenerator::deleteTermRelation(Term_ptr term) {
  auto relation = getTermRelation(term);
  if(relation not_eq nullptr) {
    delete relation;
    relations.erase(term);
  }
}

} /* namespace Solver */
} /* namespace Vlab */