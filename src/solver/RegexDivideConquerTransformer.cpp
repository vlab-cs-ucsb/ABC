/*
 * RegexDivideConquerTransformer.cpp
 *
  *  Created on: May 4, 2015
 *      Author: baki, tegan
 *   Copyright: Copyright 2015 The ABC Authors. All rights reserved.
 *              Use of this source code is governed license that can
 *              be found in the COPYING file.
 */

#include "RegexDivideConquerTransformer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int RegexDivideConquerTransformer::VLOG_LEVEL = 16;

RegexDivideConquerTransformer::RegexDivideConquerTransformer(Script_ptr script, SymbolTable_ptr symbol_table)
  : root(script), symbol_table_(symbol_table) {
}

RegexDivideConquerTransformer::~RegexDivideConquerTransformer() {
}

void RegexDivideConquerTransformer::start() {

  symbol_table_->add_regex_prefix_var();
  // symbol_table_->add_regex_suffix_var();

  std::string regex_prefix_var_name = symbol_table_->get_var_name_for_expression(root, Variable::Type::STRING) + "_PREFIX";
  // std::string regex_suffix_var_name = symbol_table_->get_var_name_for_expression(root, Variable::Type::STRING) + "_SUFFIX";
  symbol_table_->add_variable(new Variable(regex_prefix_var_name, Variable::Type::STRING));
  // symbol_table_->add_variable(new Variable(regex_suffix_var_name, Variable::Type::STRING));

  symbol_table_->push_scope(root, false);
  visit(root);
  symbol_table_->pop_scope();

  end();
}
void RegexDivideConquerTransformer::end() {

	SyntacticProcessor syntactic_processor(root);
	syntactic_processor.start();

  SyntacticOptimizer syntactic_optimizer(root, symbol_table_);
  syntactic_optimizer.start();
}


void RegexDivideConquerTransformer::visitScript(Script_ptr script) {
  visit_children_of(script);
}

void RegexDivideConquerTransformer::visitCommand(Command_ptr command) {
}

void RegexDivideConquerTransformer::visitAssert(Assert_ptr assert_command) {
  visit_children_of(assert_command);
}

void RegexDivideConquerTransformer::visitTerm(Term_ptr term) {
}

void RegexDivideConquerTransformer::visitExclamation(Exclamation_ptr exclamation_term) {
}

void RegexDivideConquerTransformer::visitExists(Exists_ptr exists_term) {
}

void RegexDivideConquerTransformer::visitForAll(ForAll_ptr for_all_term) {
}

void RegexDivideConquerTransformer::visitLet(Let_ptr let_term) {
  LOG(ERROR) << "optimizations are not checked for let term";
}

void RegexDivideConquerTransformer::visitAnd(And_ptr and_term) {
  if(root != symbol_table_->top_scope()) {
    std::reverse(and_term->term_list->begin(),and_term->term_list->end());
  }
  for (auto &term : * (and_term->term_list)) {
    visit_and_callback(term);
  }
}

void RegexDivideConquerTransformer::visitOr(Or_ptr or_term) {

  // under a single or (and single variable) prefixes are unique
  // that is, each prefix corresponds to a single set (not multiple sets) of suffix terms
  std::map<std::string, TermList_ptr> prefix_suffix_termlists; 

  for (auto iter = or_term->term_list->begin(); iter != or_term->term_list->end();) {
    symbol_table_->push_scope(*iter, false);
    visit(*iter);
    symbol_table_->pop_scope();

    // if has transformation, move it to new termlist
    // relevant in_terms will already be transformed accordingly
    LOG(INFO) << "CHECKING FOR TRANSFORMATION";
    LOG(INFO) << "  scope = " << symbol_table_->top_scope();
    LOG(INFO) << "  term  = " << *iter;
    if(symbol_table_->has_regex_prefix_transformation(symbol_table_->top_scope(),*iter)) {
      LOG(INFO) << "  >> HAS TRANSFORMATION <<";
      std::string prefix_string = symbol_table_->get_regex_prefix_transformation(symbol_table_->top_scope(), *iter);
      if(prefix_suffix_termlists.find(prefix_string) == prefix_suffix_termlists.end()) {
        prefix_suffix_termlists[prefix_string] = new TermList();
      }
      prefix_suffix_termlists[prefix_string]->push_back(*iter);
      *iter = nullptr;
      iter = or_term->term_list->erase(iter);
    } else {
      iter++;
    }
  }

  for(auto it : prefix_suffix_termlists) {

    auto or_termlist = it.second;
    std::string prefix_string = it.first;
    std::string regex_prefix_var_name = symbol_table_->get_regex_prefix_var_name();

    auto regex_prefix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_prefix_var_name, Primitive::Type::SYMBOL)));
    auto regex_prefix_in_term_constant = new TermConstant(new Primitive(prefix_string,Primitive::Type::REGEX));
    auto regex_prefix_in_term = new In(regex_prefix_term_qualid->clone(),regex_prefix_in_term_constant);
    
    auto sub_or_term = new Or(or_termlist);
    auto and_termlist = new TermList();
    // add term for regex prefix (r in rp)
    
    // add term for regex suffixes (disjunction of terms (r in sp))
    // each child can be a conjunction of (r in sp) and other terms (like (a in a1))
    and_termlist->push_back(sub_or_term);
    and_termlist->push_back(regex_prefix_in_term);
    auto and_term = new And(and_termlist);

    or_term->term_list->push_back(and_term);
  }

  // if(!prefix_suffix_termlists.empty()) {
  //   std::string regex_prefix_var_name = symbol_table_->get_regex_prefix_var_name();
  //   std::string regex_suffix_var_name = symbol_table_->get_regex_suffix_var_name();
  //   std::string regex_split_var_name = symbol_table_->get_regex_split_var_name();

  //   // add new conjunction which adds (r = rp,rs) && (disjunction for rp, rs)
  //   // note that, since we wil call syntactic processor/optimizer, and term will get pushed into parent and term (if it exists)
  //   callback_ = [or_term, regex_split_var_name, regex_suffix_var_name, regex_prefix_var_name](Term_ptr & term) mutable {
  //       auto regex_prefix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_prefix_var_name, Primitive::Type::SYMBOL)));
  //       auto regex_suffix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_suffix_var_name, Primitive::Type::SYMBOL)));
  //       auto regex_split_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_split_var_name, Primitive::Type::SYMBOL)));
    
  //       auto concat_termlist = new TermList();
  //       concat_termlist->push_back(regex_prefix_term_qualid);
  //       concat_termlist->push_back(regex_suffix_term_qualid);
  //       auto concat_term = new Concat(concat_termlist);

  //       auto eq_term = new Eq(regex_split_term_qualid, concat_term);
        
  //       auto and_termlist = new TermList();
  //       and_termlist->push_back(or_term);
  //       and_termlist->push_back(eq_term);

  //       term = new And(and_termlist);
  //     };
  // }

  // std::cin.get();
}

void RegexDivideConquerTransformer::visitNot(Not_ptr not_term) {
  visit_children_of(not_term);
}

void RegexDivideConquerTransformer::visitUMinus(UMinus_ptr u_minus_term) {
  visit_children_of(u_minus_term);
}

void RegexDivideConquerTransformer::visitMinus(Minus_ptr minus_term) {
  visit_children_of(minus_term);
}

void RegexDivideConquerTransformer::visitPlus(Plus_ptr plus_term) {
  for (auto& term_ptr : * (plus_term->term_list)) {
    visit(term_ptr);
  }
}

void RegexDivideConquerTransformer::visitTimes(Times_ptr times_term) {
  for (auto& term_ptr : * (times_term->term_list)) {
    visit(term_ptr);
  }
}

void RegexDivideConquerTransformer::visitDiv(Div_ptr div_term) {
  LOG(FATAL) << "implement me";
}

void RegexDivideConquerTransformer::visitEq(Eq_ptr eq_term) {
  visit_children_of(eq_term);
}


void RegexDivideConquerTransformer::visitNotEq(NotEq_ptr not_eq_term) {
  visit_children_of(not_eq_term);
}

void RegexDivideConquerTransformer::visitGt(Gt_ptr gt_term) {
  visit_children_of(gt_term);
}

void RegexDivideConquerTransformer::visitGe(Ge_ptr ge_term) {
  visit_children_of(ge_term);
}

void RegexDivideConquerTransformer::visitLt(Lt_ptr lt_term) {
  visit_children_of(lt_term);
}

void RegexDivideConquerTransformer::visitLe(Le_ptr le_term) {
  visit_children_of(le_term);
}

void RegexDivideConquerTransformer::visitConcat(Concat_ptr concat_term) {
  for (auto& term_ptr : * (concat_term->term_list)) {
    visit(term_ptr);
  }
}

void RegexDivideConquerTransformer::visitIn(In_ptr in_term) {
  // check if need to transform from (r in p.s)
  // if so, new constraint will be (rs in s)
  // where rs is new variable (created earlier)

  if(symbol_table_->has_regex_prefix_transformation(symbol_table_->top_scope(),in_term)) {
    // get prefix string, replace regex with suffix string
    std::string regex_split_var_name = symbol_table_->get_regex_split_var_name();
    std::string prefix_string = symbol_table_->get_regex_prefix_transformation(symbol_table_->top_scope(),in_term);
    std::string regex_prefix_var_name = symbol_table_->get_regex_prefix_var_name();

    auto qualid_term = dynamic_cast<QualIdentifier_ptr>(in_term->left_term);
    auto regex_term = dynamic_cast<TermConstant_ptr>(in_term->right_term);
    if(qualid_term == nullptr || regex_term == nullptr) {
      LOG(FATAL) << "expected valid qualid and regex terms";
    }

    std::string regex_string = regex_term->primitive->getData();
    // regex prefix has unnecessary parenthesis in raw string due to current implementation
    // need to account for that when deleting prefix
    auto r = new Util::RegularExpression(regex_string); 
    regex_string = r->str();
    delete r;
    regex_string.erase(0, prefix_string.size());

    callback_ = [in_term, prefix_string, regex_split_var_name, regex_string, regex_prefix_var_name, this](Term_ptr & term) mutable {
      auto regex_prefix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_prefix_var_name, Primitive::Type::SYMBOL)));
      auto regex_suffix_term_constant = new TermConstant(new Primitive(regex_string,Primitive::Type::REGEX));
      auto regex_split_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_split_var_name, Primitive::Type::SYMBOL)));

      auto concat_termlist = new TermList();
      concat_termlist->push_back(regex_prefix_term_qualid);
      concat_termlist->push_back(regex_suffix_term_constant);
      auto concat_term = new Concat(concat_termlist);

      auto eq_term = new Eq(regex_split_term_qualid, concat_term);
      symbol_table_->add_regex_prefix_transformation(symbol_table_->top_scope(), eq_term, prefix_string);

      term = eq_term;

      delete in_term->left_term; in_term->left_term = nullptr;
      delete in_term->right_term; in_term->right_term = nullptr;
      delete in_term; in_term = nullptr;
    };
  }

  // if(symbol_table_->has_regex_prefix_transformation(symbol_table_->top_scope(),in_term)) {
  //   // get prefix string, replace regex with suffix string
  //   std::string prefix_string = symbol_table_->get_regex_prefix_transformation(symbol_table_->top_scope(),in_term);
  //   std::string regex_suffix_var_name = symbol_table_->get_regex_suffix_var_name();

  //   //TODO: no need to create new terms and delete old ones
  //   // can't we just replace the primitives inside? would it be faster?
  //   auto qualid_term = dynamic_cast<QualIdentifier_ptr>(in_term->left_term);
  //   auto regex_term = dynamic_cast<TermConstant_ptr>(in_term->right_term);
  //   if(qualid_term == nullptr || regex_term == nullptr) {
  //     LOG(FATAL) << "expected valid qualid and regex terms";
  //   }

  //   std::string regex_string = regex_term->primitive->getData();
  //   // regex prefix has unnecessary parenthesis in raw string due to current implementation
  //   // need to account for that when deleting prefix
  //   auto r = new Util::RegularExpression(regex_string); 
  //   regex_string = r->str();
  //   delete r;
  //   regex_string.erase(0, prefix_string.size());

  //   auto regex_suffix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_suffix_var_name, Primitive::Type::SYMBOL)));
  //   auto regex_suffix_in_term_constant = new TermConstant(new Primitive(regex_string,Primitive::Type::REGEX));

  //   delete in_term->left_term;
  //   in_term->left_term = regex_suffix_term_qualid;
  //   delete in_term->right_term;
  //   in_term->right_term = regex_suffix_in_term_constant;
  // }

}

void RegexDivideConquerTransformer::visitNotIn(NotIn_ptr not_in_term) {
  visit_children_of(not_in_term);
}

void RegexDivideConquerTransformer::visitLen(Len_ptr len_term) {
  visit_children_of(len_term);
}

void RegexDivideConquerTransformer::visitContains(Contains_ptr contains_term) {
  visit_children_of(contains_term);
}

void RegexDivideConquerTransformer::visitNotContains(NotContains_ptr not_contains_term) {
  visit_children_of(not_contains_term);
}

void RegexDivideConquerTransformer::visitBegins(Begins_ptr begins_term) {
  visit_children_of(begins_term);
}

void RegexDivideConquerTransformer::visitNotBegins(NotBegins_ptr not_begins_term) {
  visit_children_of(not_begins_term);
}

void RegexDivideConquerTransformer::visitEnds(Ends_ptr ends_term) {
  visit_children_of(ends_term);
}

void RegexDivideConquerTransformer::visitNotEnds(NotEnds_ptr not_ends_term) {
  visit_children_of(not_ends_term);
}

void RegexDivideConquerTransformer::visitIndexOf(IndexOf_ptr index_of_term) {
  visit_children_of(index_of_term);
}

void RegexDivideConquerTransformer::visitLastIndexOf(LastIndexOf_ptr last_index_of_term) {
  visit_children_of(last_index_of_term);
}

void RegexDivideConquerTransformer::visitCharAt(CharAt_ptr char_at_term) {
  visit_children_of(char_at_term);
}

void RegexDivideConquerTransformer::visitSubString(SubString_ptr sub_string_term) {
  visit_children_of(sub_string_term);
}

void RegexDivideConquerTransformer::visitToUpper(ToUpper_ptr to_upper_term) {
  visit_children_of(to_upper_term);
}

void RegexDivideConquerTransformer::visitToLower(ToLower_ptr to_lower_term) {
  visit_children_of(to_lower_term);
}

void RegexDivideConquerTransformer::visitTrim(Trim_ptr trim_term) {
  visit_children_of(trim_term);
}

void RegexDivideConquerTransformer::visitToString(ToString_ptr to_string_term) {
  visit_children_of(to_string_term);
}

void RegexDivideConquerTransformer::visitToInt(ToInt_ptr to_int_term) {
  visit_children_of(to_int_term);
}

void RegexDivideConquerTransformer::visitReplace(Replace_ptr replace_term) {
  visit_children_of(replace_term);

}

void RegexDivideConquerTransformer::visitCount(Count_ptr count_term) {
  visit_children_of(count_term);
}

void RegexDivideConquerTransformer::visitIte(Ite_ptr ite_term) {
}

void RegexDivideConquerTransformer::visitReConcat(ReConcat_ptr re_concat_term) {
}

void RegexDivideConquerTransformer::visitReUnion(ReUnion_ptr re_union_term) {
}

void RegexDivideConquerTransformer::visitReInter(ReInter_ptr re_inter_term) {
}

void RegexDivideConquerTransformer::visitReStar(ReStar_ptr re_star_term) {
}

void RegexDivideConquerTransformer::visitRePlus(RePlus_ptr re_plus_term) {
}

void RegexDivideConquerTransformer::visitReOpt(ReOpt_ptr re_opt_term) {
}

void RegexDivideConquerTransformer::visitToRegex(ToRegex_ptr to_regex_term) {
}

void RegexDivideConquerTransformer::visitUnknownTerm(Unknown_ptr unknown_term) {
}

void RegexDivideConquerTransformer::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
}

void RegexDivideConquerTransformer::visitQualIdentifier(QualIdentifier_ptr qi_term) {
}

void RegexDivideConquerTransformer::visitTermConstant(TermConstant_ptr term_constant) {
}

void RegexDivideConquerTransformer::visitIdentifier(Identifier_ptr identifier) {
}

void RegexDivideConquerTransformer::visitPrimitive(Primitive_ptr primitive) {
}

void RegexDivideConquerTransformer::visitTVariable(TVariable_ptr t_variable) {
}

void RegexDivideConquerTransformer::visitTBool(TBool_ptr t_bool) {
}

void RegexDivideConquerTransformer::visitTInt(TInt_ptr t_int) {
}

void RegexDivideConquerTransformer::visitTString(TString_ptr t_string) {
}

void RegexDivideConquerTransformer::visitVariable(Variable_ptr variable) {
}

void RegexDivideConquerTransformer::visitSort(Sort_ptr sort) {
}

void RegexDivideConquerTransformer::visitAttribute(Attribute_ptr attribute) {
}

void RegexDivideConquerTransformer::visitSortedVar(SortedVar_ptr sorted_var) {
}

void RegexDivideConquerTransformer::visitVarBinding(VarBinding_ptr var_binding) {
}

void RegexDivideConquerTransformer::visit_and_callback(Term_ptr & term) {
  visit(term);
  if (callback_) {
    callback_(term);
    callback_ = nullptr;
    visit_and_callback(term);
  }
}

} /* namespace Solver */
} /* namespace Vlab */
