//
// Created by will on 11/21/19.
//

#include "AstSortComputer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

AstSortComputer::AstSortComputer(Script_ptr root, SymbolTable_ptr symbol_table)
    : root_(root),
      symbol_table_(symbol_table) {

}

AstSortComputer::~AstSortComputer() {

}

void AstSortComputer::start() {
  visit(root_);
}

void AstSortComputer::start(Visitable_ptr term) {
  visit(term);
}

void AstSortComputer::end() {

}

void AstSortComputer::visitScript(Script_ptr script) {

}

void AstSortComputer::visitCommand(Command_ptr command) {

}

void AstSortComputer::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void AstSortComputer::visitTerm(Term_ptr term) {

}

void AstSortComputer::visitExclamation(Exclamation_ptr exclamation_term) {

}

void AstSortComputer::visitExists(Exists_ptr exists_term) {

}

void AstSortComputer::visitForAll(ForAll_ptr for_all_term) {

}

void AstSortComputer::visitLet(Let_ptr let_term) {

}

void AstSortComputer::visitAnd(And_ptr and_term) {
  visit_children_of(and_term);
  SetTermSort(and_term,Sort::Type::BOOL);
}

void AstSortComputer::visitOr(Or_ptr or_term) {
  visit_children_of(or_term);
  SetTermSort(or_term,Sort::Type::BOOL);
}

void AstSortComputer::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
  SetTermSort(not_term,Sort::Type::BOOL);
}

void AstSortComputer::visitUMinus(UMinus_ptr uminus_term) {
  visit_children_of(uminus_term);
  SetTermSort(uminus_term,Sort::Type::INT);
}

void AstSortComputer::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
  SetTermSort(minus_term,Sort::Type::INT);
}

void AstSortComputer::visitPlus(Plus_ptr plus_term) {
  visit_children_of(plus_term);
  SetTermSort(plus_term,Sort::Type::INT);
}

void AstSortComputer::visitTimes(Times_ptr times_term) {
  visit_children_of(times_term);
  SetTermSort(times_term,Sort::Type::INT);
}

void AstSortComputer::visitDiv(Div_ptr div_term) {
  visit_children_of(div_term);
  SetTermSort(div_term,Sort::Type::INT);
}

void AstSortComputer::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);

  auto left_sort_type = GetTermSort(eq_term->left_term);
  auto right_sort_type = GetTermSort(eq_term->right_term);

  if(left_sort_type == right_sort_type) {
    SetTermSort(eq_term,left_sort_type);
  } else {
    SetTermSort(eq_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);

  auto left_sort_type = GetTermSort(not_eq_term->left_term);
  auto right_sort_type = GetTermSort(not_eq_term->right_term);

  if(left_sort_type == right_sort_type) {
    SetTermSort(not_eq_term,left_sort_type);
  } else {
    SetTermSort(not_eq_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);

  auto left_sort_type = GetTermSort(gt_term->left_term);
  auto right_sort_type = GetTermSort(gt_term->right_term);

  if(left_sort_type == right_sort_type) {
    SetTermSort(gt_term,left_sort_type);
  } else {
    SetTermSort(gt_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);

  auto left_sort_type = GetTermSort(ge_term->left_term);
  auto right_sort_type = GetTermSort(ge_term->right_term);

  if(left_sort_type == right_sort_type) {
    SetTermSort(ge_term,left_sort_type);
  } else {
    SetTermSort(ge_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);

  auto left_sort_type = GetTermSort(lt_term->left_term);
  auto right_sort_type = GetTermSort(lt_term->right_term);

  if(left_sort_type == right_sort_type) {
    SetTermSort(lt_term,left_sort_type);
  } else {
    SetTermSort(lt_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);

  auto left_sort_type = GetTermSort(le_term->left_term);
  auto right_sort_type = GetTermSort(le_term->right_term);

  if(left_sort_type == right_sort_type) {
    SetTermSort(le_term,left_sort_type);
  } else {
    SetTermSort(le_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitConcat(Concat_ptr concat_term) {
  visit_children_of(concat_term);
  SetTermSort(concat_term,Sort::Type::STRING);
}

void AstSortComputer::visitIn(In_ptr in_term) {
  visit_children_of(in_term);
  SetTermSort(in_term,Sort::Type::STRING);
}

void AstSortComputer::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
  SetTermSort(not_in_term,Sort::Type::STRING);
}

void AstSortComputer::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
  SetTermSort(len_term,Sort::Type::INT);
}

void AstSortComputer::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
  SetTermSort(contains_term,Sort::Type::STRING);
}

void AstSortComputer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
  SetTermSort(not_contains_term,Sort::Type::STRING);
}

void AstSortComputer::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
  SetTermSort(begins_term,Sort::Type::STRING);
}

void AstSortComputer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
  SetTermSort(not_begins_term,Sort::Type::STRING);
}

void AstSortComputer::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
  SetTermSort(ends_term,Sort::Type::STRING);
}

void AstSortComputer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
  SetTermSort(not_ends_term,Sort::Type::STRING);
}

void AstSortComputer::visitIndexOf(IndexOf_ptr indexof_term) {
  visit_children_of(indexof_term);
  SetTermSort(indexof_term,Sort::Type::INT);
}

void AstSortComputer::visitLastIndexOf(LastIndexOf_ptr lastindexof_term) {
  visit_children_of(lastindexof_term);
  SetTermSort(lastindexof_term,Sort::Type::INT);
}


void AstSortComputer::visitCharAt(CharAt_ptr charat_term) {
  visit_children_of(charat_term);
  SetTermSort(charat_term,Sort::Type::STRING);
}

void AstSortComputer::visitSubString(SubString_ptr substring_term) {
  visit_children_of(substring_term);
  SetTermSort(substring_term,Sort::Type::STRING);
}

void AstSortComputer::visitToUpper(ToUpper_ptr toupper_term) {
  visit_children_of(toupper_term);
  SetTermSort(toupper_term,Sort::Type::STRING);
}

void AstSortComputer::visitToLower(ToLower_ptr tolower_term) {
  visit_children_of(tolower_term);
  SetTermSort(tolower_term,Sort::Type::STRING);
}

void AstSortComputer::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
  SetTermSort(trim_term,Sort::Type::STRING);
}

void AstSortComputer::visitToString(ToString_ptr tostring_term) {
  visit_children_of(tostring_term);
  SetTermSort(tostring_term,Sort::Type::STRING);
}

void AstSortComputer::visitToInt(ToInt_ptr toint_term) {
  visit_children_of(toint_term);
  SetTermSort(toint_term,Sort::Type::INT);
}

void AstSortComputer::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);
  SetTermSort(replace_term,Sort::Type::STRING);
}

void AstSortComputer::visitCount(Count_ptr count_term) {
}

void AstSortComputer::visitIte(Ite_ptr ite_term) {
  visit_children_of(ite_term);
  auto left_sort_type = GetTermSort(ite_term->then_branch);
  auto right_sort_type = GetTermSort(ite_term->else_branch);

  if(left_sort_type == right_sort_type) {
    SetTermSort(ite_term,left_sort_type);
  } else {
    SetTermSort(ite_term,Sort::Type::NONE);
  }
}

void AstSortComputer::visitReConcat(ReConcat_ptr re_concat_term) {

}

void AstSortComputer::visitReUnion(ReUnion_ptr re_union_term) {

}

void AstSortComputer::visitReInter(ReInter_ptr re_inter_term) {

}

void AstSortComputer::visitReStar(ReStar_ptr re_star_term) {

}

void AstSortComputer::visitRePlus(RePlus_ptr re_plus_term) {

}

void AstSortComputer::visitReOpt(ReOpt_ptr re_opt_term) {

}

void AstSortComputer::visitToRegex(ToRegex_ptr to_regex_term) {

}

void AstSortComputer::visitUnknownTerm(Unknown_ptr unknown_term) {

}

void AstSortComputer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {

}

void AstSortComputer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  Variable_ptr variable = symbol_table_->get_variable(qi_term->getVarName());
  switch(variable->getType()) {
    case Variable::Type::STRING:
      SetTermSort(qi_term,Sort::Type::STRING);
      break;
    case Variable::Type::INT:
      SetTermSort(qi_term,Sort::Type::INT);
      break;
    case Variable::Type::BOOL:
      SetTermSort(qi_term,Sort::Type::BOOL);
      break;
    default:
      SetTermSort(qi_term,Sort::Type::NONE);
      break;
  }
}

void AstSortComputer::visitTermConstant(TermConstant_ptr term_constant) {
  switch (term_constant->getValueType()) {
    case Primitive::Type::STRING: {
      SetTermSort(term_constant,Sort::Type::STRING);
      break;
    }
    case Primitive::Type::NUMERAL: {
      SetTermSort(term_constant,Sort::Type::INT);
      break;
    }
		case Primitive::Type::BOOL: {
      SetTermSort(term_constant,Sort::Type::BOOL);
      break;
    }
    default:
      SetTermSort(term_constant,Sort::Type::NONE);
      break;
  }
}

void AstSortComputer::visitSort(Sort_ptr sort_term) {

}

void AstSortComputer::visitTVariable(TVariable_ptr t_variable) {

}

void AstSortComputer::visitTBool(TBool_ptr t_bool) {

}

void AstSortComputer::visitTInt(TInt_ptr t_int) {

}

void AstSortComputer::visitTString(TString_ptr t_string) {

}

void AstSortComputer::visitAttribute(Attribute_ptr attribute) {

}

void AstSortComputer::visitSortedVar(SortedVar_ptr sorted_var) {

}

void AstSortComputer::visitVarBinding(VarBinding_ptr var_binding) {

}

void AstSortComputer::visitIdentifier(Identifier_ptr identifier) {

}

void AstSortComputer::visitPrimitive(Primitive_ptr primitive) {

}

void AstSortComputer::visitVariable(Variable_ptr variable) {

}

Sort::Type AstSortComputer::GetTermSort(Visitable_ptr term) {
  if (term_sort_map_.find(term) != term_sort_map_.end()) {
    return term_sort_map_[term];
  }
  return SMT::Sort::Type::NONE;
}

bool AstSortComputer::IsBoolTerm(Term_ptr term) {
  bool is_bool = false;

  switch(term->type()) {
    case Term::Type::NOT:
    case Term::Type::EQ:
    case Term::Type::NOTEQ:
    case Term::Type::GT:
    case Term::Type::GE:
    case Term::Type::LT:
    case Term::Type::LE:
    case Term::Type::CONTAINS:
    case Term::Type::NOTCONTAINS:
    case Term::Type::IN:
    case Term::Type::NOTIN:
    case Term::Type::BEGINS:
    case Term::Type::NOTBEGINS:
    case Term::Type::ENDS:
    case Term::Type::NOTENDS:
      is_bool = true;
      break;
    default:
      break;
  }

  return is_bool;
}

void AstSortComputer::SetTermSort(Visitable_ptr term, Sort::Type sort_type) {
  term_sort_map_[term] = sort_type;
}

} /* namespace Solver */
} /* namespace Vlab */
