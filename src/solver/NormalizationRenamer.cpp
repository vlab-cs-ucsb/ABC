//
// Created by will on 10/18/18.
//

#include "NormalizationRenamer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

NormalizationRenamer::NormalizationRenamer(Script_ptr script, SymbolTable_ptr symbol_table)
    : root_(script),
      symbol_table_(symbol_table) {
}

NormalizationRenamer::NormalizationRenamer(Script_ptr script, SymbolTable_ptr symbol_table,
                        std::map<std::string,std::string> var_map, std::map<char,char> char_map)
    : root_ (script),
      symbol_table_(symbol_table),
      variable_mapping_(var_map),
      alphabet_mapping_(char_map) {

}

NormalizationRenamer::~NormalizationRenamer() {
}

void NormalizationRenamer::start () {
  symbol_table_->push_scope(root_, false);
  visitScript(root_);
  symbol_table_->pop_scope();
  end();
}

void NormalizationRenamer::start(Term_ptr term, bool store_mapping) {
  visitTerm(term);
  if(store_mapping) {
    end();
  }
}

void NormalizationRenamer::end() {
  // add mapping to symbol table
  // symbol_table_->SetVariableMapping(variable_mapping_);
  // symbol_table_->SetCharacterMapping(alphabet_mapping_);
}

void NormalizationRenamer::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void NormalizationRenamer::visitCommand(Command_ptr command) {
}

void NormalizationRenamer::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void NormalizationRenamer::visitTerm(Term_ptr term) {
}

void NormalizationRenamer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void NormalizationRenamer::visitExists(Exists_ptr exists_term) {
}

void NormalizationRenamer::visitForAll(ForAll_ptr for_all_term) {
}

void NormalizationRenamer::visitLet(Let_ptr let_term) {
  LOG(ERROR) << "optimizations are not checked for let term";
}

void NormalizationRenamer::visitAnd(And_ptr and_term) {
  for (auto& term : * (and_term->term_list)) {
    visit(term);
  }
}

void NormalizationRenamer::visitOr(Or_ptr or_term) {
  for (auto& term : * (or_term->term_list)) {
    symbol_table_->push_scope(term, false);
    visit(term);
    symbol_table_->pop_scope();
  }
}

void NormalizationRenamer::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
}

void NormalizationRenamer::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
}

void NormalizationRenamer::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
}

void NormalizationRenamer::visitPlus(Plus_ptr plus_term) {
  for (auto& term_ptr : * (plus_term->term_list)) {
    visit(term_ptr);
  }
}

void NormalizationRenamer::visitTimes(Times_ptr times_term) {
  for (auto& term_ptr : * (times_term->term_list)) {
    visit(term_ptr);
  }
}

void NormalizationRenamer::visitDiv(Div_ptr div_term) {
  LOG(FATAL) << "implement me";
}

void NormalizationRenamer::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
}


void NormalizationRenamer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
}

void NormalizationRenamer::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
}

void NormalizationRenamer::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
}

void NormalizationRenamer::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
}

void NormalizationRenamer::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
}

void NormalizationRenamer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : * (concat_term->term_list)) {
    visit(term_ptr);
  }
}

void NormalizationRenamer::visitIn(In_ptr in_term) {
  visit_children_of(in_term);
}

void NormalizationRenamer::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
}

void NormalizationRenamer::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
}

void NormalizationRenamer::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
}

void NormalizationRenamer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
}

void NormalizationRenamer::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
}

void NormalizationRenamer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
}

void NormalizationRenamer::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
}

void NormalizationRenamer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
}

void NormalizationRenamer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);
}

void NormalizationRenamer::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
}

void NormalizationRenamer::visitCharAt(CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
}

void NormalizationRenamer::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
}

void NormalizationRenamer::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
}

void NormalizationRenamer::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
}

void NormalizationRenamer::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
}

void NormalizationRenamer::visitToString(ToString_ptr to_string_term) {
  visit_children_of(to_string_term);
}

void NormalizationRenamer::visitToInt(ToInt_ptr to_int_term) {
  visit_children_of(to_int_term);
}

void NormalizationRenamer::visitReplace(Replace_ptr replace_term) {
}

void NormalizationRenamer::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
}

void NormalizationRenamer::visitIte(Ite_ptr ite_term) {
}

void NormalizationRenamer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void NormalizationRenamer::visitReUnion(ReUnion_ptr re_union_term) {
}

void NormalizationRenamer::visitReInter(ReInter_ptr re_inter_term) {
}

void NormalizationRenamer::visitReStar(ReStar_ptr re_star_term) {
}

void NormalizationRenamer::visitRePlus(RePlus_ptr re_plus_term) {
}

void NormalizationRenamer::visitReOpt(ReOpt_ptr re_opt_term) {
}

void NormalizationRenamer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void NormalizationRenamer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void NormalizationRenamer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void NormalizationRenamer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  // for both current scope and root_
  auto current_scope = symbol_table_->top_scope();
  auto root_scope = root_;
  std::string var_name = qi_term->getVarName();

  // current scope
//  if(variable_mapping_[current_scope].find(var_name) == variable_mapping_[current_scope].end()) {
//    std::string new_var_name = "v"+std::to_string(variable_mapping_[current_scope].size());
//    variable_mapping_[current_scope][var_name] = new_var_name;
////    qi_term->identifier->symbol->setData(new_var_name);
//  }

  // root scope

  if(variable_mapping_.find(var_name) == variable_mapping_.end()) {
    std::string new_var_name = "v"+std::to_string(variable_mapping_.size());
    variable_mapping_[var_name] = new_var_name;
    qi_term->identifier->symbol->setData(new_var_name);
  } else {
    qi_term->identifier->symbol->setData(variable_mapping_[var_name]);
  }
}

void NormalizationRenamer::visitTermConstant(TermConstant_ptr term_constant) {

    //
////
////
//  // only for string constants atm?

    auto current_scope = symbol_table_->top_scope();
  auto root_scope = root_;
  std::string value = term_constant->primitive->getData();
  std::string new_value = "";

  if(term_constant->getValueType() == Primitive::Type::STRING) {
    for(auto iter : term_constant->primitive->getData()) {
      new_value += AddToMap(root_scope,iter);
    }
  } else if(term_constant->getValueType() == Primitive::Type::REGEX) {
    bool escape = false;
    bool range = false;
    for(int i = 0; i < value.length(); i++) {
      char c = value[i];
      char cnew;
      if(i == 0 || i == value.length()-1) {
        cnew = c;
      } else if(escape) {
        cnew = AddToMap(root_scope, c);
        escape = false;
      } else if(range) {
        cnew = c;
        if(c == '}') {
          range = false;
        }
      } else if(c == '\\') {
        escape = true;
        continue;
      } else if(c == '{') {
        range = true;
        cnew = c;
      } else if(c == '-') {
        // e.g., [B-E]
        for(char cc = value[i-1]; cc != value[i+1]; cc++) {
          AddToMap(root_scope,cc);
        }
        cnew = c;
      } else if(special_chars_.find(c) != special_chars_.end()) {
        cnew = c;
      } else {
        cnew = AddToMap(root_scope,c);
      }
      new_value += cnew;
    }
  } else {

    new_value = value;
  }

  term_constant->primitive->setData(new_value);

}

void NormalizationRenamer::visitIdentifier(Identifier_ptr identifier) {
}

void NormalizationRenamer::visitPrimitive(Primitive_ptr primitive) {
}

void NormalizationRenamer::visitTVariable(TVariable_ptr t_variable) {
}

void NormalizationRenamer::visitTBool(TBool_ptr t_bool) {
}

void NormalizationRenamer::visitTInt(TInt_ptr t_int) {
}

void NormalizationRenamer::visitTString(TString_ptr t_string) {
}

void NormalizationRenamer::visitVariable(Variable_ptr variable) {
}

void NormalizationRenamer::visitSort(Sort_ptr sort) {
}

void NormalizationRenamer::visitAttribute(Attribute_ptr attribute) {
}

void NormalizationRenamer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void NormalizationRenamer::visitVarBinding(VarBinding_ptr var_binding) {
}

char NormalizationRenamer::AddToMap(Visitable_ptr term, char c) {
  if (alphabet_mapping_.find(c) == alphabet_mapping_.end()) {
    // not in map, add to map
    int pos = alphabet_mapping_.size()+48;
    alphabet_mapping_[c] = (char)(pos);
  }
  return alphabet_mapping_[c];
}

}
}
