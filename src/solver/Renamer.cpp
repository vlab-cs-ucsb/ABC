//
// Created by will on 10/18/18.
//

#include "Renamer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

Renamer::Renamer(Script_ptr script, SymbolTable_ptr symbol_table)
    : root_(script),
      symbol_table_(symbol_table) {
}

Renamer::Renamer(Script_ptr script, SymbolTable_ptr symbol_table,
                        std::map<std::string,std::string> var_map, std::map<char,char> char_map)
    : root_ (script),
      symbol_table_(symbol_table),
      variable_mapping_(var_map),
      alphabet_mapping_(char_map) {

}

Renamer::~Renamer() {
}

void Renamer::start () {
  symbol_table_->push_scope(root_, false);
  visitScript(root_);
  symbol_table_->pop_scope();
  end();
}

void Renamer::start(Term_ptr term, bool store_mapping) {
  visitTerm(term);
  if(store_mapping) {
    end();
  }
}

void Renamer::end() {
  // add mapping to symbol table
  symbol_table_->SetVariableMapping(variable_mapping_);
  symbol_table_->SetCharacterMapping(alphabet_mapping_);
}

void Renamer::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void Renamer::visitCommand(Command_ptr command) {
}

void Renamer::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void Renamer::visitTerm(Term_ptr term) {
}

void Renamer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void Renamer::visitExists(Exists_ptr exists_term) {
}

void Renamer::visitForAll(ForAll_ptr for_all_term) {
}

void Renamer::visitLet(Let_ptr let_term) {
  LOG(ERROR) << "optimizations are not checked for let term";
}

void Renamer::visitAnd(And_ptr and_term) {
  for (auto& term : * (and_term->term_list)) {
    visit(term);
  }
}

void Renamer::visitOr(Or_ptr or_term) {
  for (auto& term : * (or_term->term_list)) {
    symbol_table_->push_scope(term, false);
    visit(term);
    symbol_table_->pop_scope();
  }
}

void Renamer::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
}

void Renamer::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
}

void Renamer::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
}

void Renamer::visitPlus(Plus_ptr plus_term) {
  for (auto& term_ptr : * (plus_term->term_list)) {
    visit(term_ptr);
  }
}

void Renamer::visitTimes(Times_ptr times_term) {
  for (auto& term_ptr : * (times_term->term_list)) {
    visit(term_ptr);
  }
}

void Renamer::visitDiv(Div_ptr div_term) {
  LOG(FATAL) << "implement me";
}

void Renamer::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
}


void Renamer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
}

void Renamer::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
}

void Renamer::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
}

void Renamer::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
}

void Renamer::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
}

void Renamer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : * (concat_term->term_list)) {
    visit(term_ptr);
  }
}

void Renamer::visitIn(In_ptr in_term) {
  visit_children_of(in_term);
}

void Renamer::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
}

void Renamer::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
}

void Renamer::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
}

void Renamer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
}

void Renamer::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
}

void Renamer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
}

void Renamer::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
}

void Renamer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
}

void Renamer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);
}

void Renamer::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
}

void Renamer::visitCharAt(CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
}

void Renamer::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
}

void Renamer::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
}

void Renamer::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
}

void Renamer::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
}

void Renamer::visitToString(ToString_ptr to_string_term) {
  visit_children_of(to_string_term);
}

void Renamer::visitToInt(ToInt_ptr to_int_term) {
  visit_children_of(to_int_term);
}

void Renamer::visitReplace(Replace_ptr replace_term) {
}

void Renamer::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
}

void Renamer::visitIte(Ite_ptr ite_term) {
}

void Renamer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void Renamer::visitReUnion(ReUnion_ptr re_union_term) {
}

void Renamer::visitReInter(ReInter_ptr re_inter_term) {
}

void Renamer::visitReStar(ReStar_ptr re_star_term) {
}

void Renamer::visitRePlus(RePlus_ptr re_plus_term) {
}

void Renamer::visitReOpt(ReOpt_ptr re_opt_term) {
}

void Renamer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void Renamer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void Renamer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void Renamer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
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

void Renamer::visitTermConstant(TermConstant_ptr term_constant) {

  // only for string constants atm?
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
//      } else if(range) {
//        cnew = c;
//        if(c == '}') {
//          range = false;
//        }
      } else if(c == '\\') {
        escape = true;
        continue;
//      } else if(c == '{') {
//        range = true;
//        cnew = c;
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

void Renamer::visitIdentifier(Identifier_ptr identifier) {
}

void Renamer::visitPrimitive(Primitive_ptr primitive) {
}

void Renamer::visitTVariable(TVariable_ptr t_variable) {
}

void Renamer::visitTBool(TBool_ptr t_bool) {
}

void Renamer::visitTInt(TInt_ptr t_int) {
}

void Renamer::visitTString(TString_ptr t_string) {
}

void Renamer::visitVariable(Variable_ptr variable) {
}

void Renamer::visitSort(Sort_ptr sort) {
}

void Renamer::visitAttribute(Attribute_ptr attribute) {
}

void Renamer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void Renamer::visitVarBinding(VarBinding_ptr var_binding) {
}

char Renamer::AddToMap(Visitable_ptr term, char c) {
  if (alphabet_mapping_.find(c) == alphabet_mapping_.end()) {
    // not in map, add to map
    int pos = alphabet_mapping_.size()+65;
    alphabet_mapping_[c] = (char)(pos);
  }
  return alphabet_mapping_[c];
}

}
}
