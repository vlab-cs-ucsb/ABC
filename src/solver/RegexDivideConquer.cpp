#include "RegexDivideConquer.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

RegexDivideConquer::RegexDivideConquer(Script_ptr script, SymbolTable_ptr symbol_table) 
        : AstTraverser(script), symbol_table_(symbol_table) {
  setCallbacks();
  computed_prefix_ = "";
  and_term_ = nullptr;
}

RegexDivideConquer::~RegexDivideConquer() {

}

void RegexDivideConquer::start() {
  symbol_table_->push_scope(root_, false);
  visitScript(root_);
  symbol_table_->pop_scope();

  end();
}

void RegexDivideConquer::end() {
  // Ast2Dot::inspectAST(root_);
  // RegexDivideConquerTransformer regex_transformer(root_,symbol_table_);
  // regex_transformer.start();

  shorten_prefixes();

  // Ast2Dot::inspectAST(root_);

  // std::cin.get();
}      

void RegexDivideConquer::setCallbacks() {
  auto term_callback = [this] (Term_ptr term) -> bool {
    switch (term->type()) {
    case Term::Type::TERMCONSTANT: {
      return false;
    }
    default:
      return true;
    }
  };

  auto command_callback = [](Command_ptr command) -> bool {
    if (Command::Type::ASSERT == command->getType()) {
      return true;
    }
    return false;
  };

  setCommandPreCallback(command_callback);
  setTermPreCallback(term_callback);
}

void RegexDivideConquer::visitAnd(And_ptr and_term) {

  // if(and_term_ == nullptr) {
  //   and_term_ = and_term;
  // }

  for (auto term : *(and_term->term_list)) {
    visit(term);
  }

  // if(and_term_ == and_term && !constraints_to_add.empty()) {
  //   and_term->term_list->insert(and_term->term_list->end(),constraints_to_add.begin(),constraints_to_add.end());
  //   constraints_to_add.clear();
  // }


}

void RegexDivideConquer::visitOr(Or_ptr or_term)  {
  for (auto& term : *(or_term->term_list)) {
    symbol_table_->push_scope(term, false);
    visit(term);
    symbol_table_->pop_scope();
  }

  // std::set<std::string> vars;
  // for(auto it : in_term_regexes_) {
  //   auto in_term = dynamic_cast<In_ptr>(it);
  //   auto qualid = dynamic_cast<QualIdentifier_ptr>(in_term->left_term);
  //   vars.insert(qualid->getVarName());
  // }

  // if(in_term_regexes_.size() >= 2 && vars.size() == 1) {
  //   // Ast2Dot::inspectAST(and_term);

  //   std::vector<Term_ptr> constraints_from_regex = analyze_regexes();
  //   constraints_to_add.insert(constraints_to_add.end(),constraints_from_regex.begin(),constraints_from_regex.end());
  //   constraints_from_regex.clear();

  // }
  // in_term_regexes_.clear();
}

void RegexDivideConquer::visitEq(Eq_ptr eq_term) {
  if(eq_term->left_term->type() == Term::Type::QUALIDENTIFIER 
          && eq_term->right_term->type() == Term::Type::TERMCONSTANT) {
    auto qid = dynamic_cast<QualIdentifier_ptr>(eq_term->left_term);
    if(qid->getVarName() == "resource") {
      prefix_shorten_terms_.push_back(eq_term->right_term);
    }
  }
}

void RegexDivideConquer::visitNotEq(NotEq_ptr not_eq_term) {
  if(not_eq_term->left_term->type() == Term::Type::QUALIDENTIFIER 
          && not_eq_term->right_term->type() == Term::Type::TERMCONSTANT) {
    auto qid = dynamic_cast<QualIdentifier_ptr>(not_eq_term->left_term);
    if(qid->getVarName() == "resource") {
      prefix_shorten_terms_.push_back(not_eq_term->right_term);
    }
  }
}

void RegexDivideConquer::visitIn(In_ptr in_term) {
  
  if(in_term->left_term->type() == Term::Type::QUALIDENTIFIER 
          && in_term->right_term->type() == Term::Type::TERMCONSTANT) {
    auto qid = dynamic_cast<QualIdentifier_ptr>(in_term->left_term);
    if(qid->getVarName() == "resource") {
      prefix_shorten_terms_.push_back(in_term->right_term);
    }
  }
}

void RegexDivideConquer::visitNotIn(NotIn_ptr not_in_term) {
  
  if(not_in_term->left_term->type() == Term::Type::QUALIDENTIFIER 
          && not_in_term->right_term->type() == Term::Type::TERMCONSTANT) {
    auto qid = dynamic_cast<QualIdentifier_ptr>(not_in_term->left_term);
    if(qid->getVarName() == "resource") {
      prefix_shorten_terms_.push_back(not_in_term->right_term);
    }
  }
}

std::string RegexDivideConquer::get_computed_prefix() {
  return computed_prefix_;
}

std::string longestCommonPrefix(std::string ar[], int n)
{

    // If size is 0, return empty string
    if (n == 0)
        return "";
 
    if (n == 1)
        return ar[0];
 
    // Sort the given array
    std::sort(ar, ar + n);
    // Find the minimum length from
    // first and last string
    int en = std::min(ar[0].size(),
                 ar[n - 1].size());
    // Now the common prefix in first and
    // last string is the longest common prefix
    std::string first = ar[0], last = ar[n - 1];
    int i = 0;
    while (i < en && first[i] == last[i])
        i++;



    std::string pre = first.substr(0, i);
    return pre;
}

Util::RegularExpression_ptr compute_regex_prefix(Util::RegularExpression_ptr r1, Util::RegularExpression_ptr r2) {
  auto temp_r1 = r1;
  auto temp_r2 = r2;

  Util::RegularExpression_ptr prefix_regex = nullptr;
  
  // preprocess; if not concat, return early
  if(r1->type() != Util::RegularExpression::Type::CONCATENATION || r2->type() != Util::RegularExpression::Type::CONCATENATION) {
    prefix_regex = new Util::RegularExpression("");
    return prefix_regex;
  }

  while(temp_r1->get_expr1()->str() == temp_r2->get_expr1()->str()) {

    if(prefix_regex == nullptr) {
      prefix_regex = temp_r1->get_expr1()->clone();
    } else {
      auto pr = prefix_regex;
      prefix_regex = Util::RegularExpression::makeConcatenation(pr->clone(),temp_r1->get_expr1()->clone());
      delete pr;
    }

    temp_r1 = temp_r1->get_expr2();
    temp_r2 = temp_r2->get_expr2();

    if(temp_r1->get_expr1() == nullptr || temp_r2->get_expr1() == nullptr) {
      break;
    }
  }

  if(prefix_regex == nullptr) {
    prefix_regex = new Util::RegularExpression("");
  }
  return prefix_regex;
}

// assume input regexes is sorted lexo
// assume >= 2 regexes
std::vector<std::pair<int,Util::RegularExpression_ptr>> longest_common_prefixes_sorted(std::vector<std::string> regexes) {
  std::vector<std::pair<int,Util::RegularExpression_ptr>> prefixes;

  Util::RegularExpression_ptr r1 = new Util::RegularExpression(regexes[0]);
  Util::RegularExpression_ptr r2 = new Util::RegularExpression(regexes[1]);

  Util::RegularExpression_ptr curr_prefix = compute_regex_prefix(r1,r2);

  LOG(INFO) << "PREFIX AT 0: " << curr_prefix->str();
  prefixes.push_back(std::pair<int,Util::RegularExpression_ptr>(0,curr_prefix));

  int pos = 1;
  while(pos+1 < regexes.size()) {
    // LOG(INFO) << "";
    r1 = new Util::RegularExpression(regexes[pos]);
    r2 = new Util::RegularExpression(regexes[pos+1]);

    // LOG(INFO) << "-------BEFORE COMPUTE_REGEX_PREFIX-------";
    Util::RegularExpression_ptr next_prefix = compute_regex_prefix(r1,r2);
    // LOG(INFO) << "-------AFTER COMPUTE_REGEX_PREFIX-------";
    if(curr_prefix->str() != next_prefix->str() && next_prefix->str() != "") {
      LOG(INFO) << "FOUND NEW PREFIX at " << pos << ": " << next_prefix->str();
      prefixes.push_back(std::pair<int,Util::RegularExpression_ptr>(pos, next_prefix));
      curr_prefix = next_prefix;
    }

    if(r1 == nullptr || r2 == nullptr || curr_prefix == nullptr || next_prefix == nullptr) {
      LOG(FATAL) << "k";
    }

    pos++;

    // if(regexes[pos].rfind(curr_prefix,0) == 0) {
    //   // starts with prefix, we good
    //   pos++;      
    // } else {
    //   // does not start with prefix
    //   // might be new common prefix, but only if theres more elements
    //   if(pos+1 == regexes.size()) {
    //     // last element doesn't match, has its own prefix; 
    //     // prefix then is "" (or prefix between this and current)
    //     curr_prefix = "";
    //     prefixes.push_back(curr_prefix);
    //     break;
    //   } else {
    //     // at least 2 more elements
    //     // find their common prefix
    //     temp[0] = regexes[pos];
    //     temp[1] = regexes[pos+1];
    //     curr_prefix = longestCommonPrefix(temp,2);
    //     prefixes.push_back(curr_prefix);
    //     pos++;
    //   }
    // }
  }

  return prefixes;
}


void RegexDivideConquer::shorten_prefixes() {

  std::vector<std::string> strings_to_shorten;

  for(auto it = prefix_shorten_terms_.begin(); it != prefix_shorten_terms_.end();) {
    auto term_constant = dynamic_cast<TermConstant_ptr>(*it);

    if(term_constant->getValueType() == Primitive::Type::REGEX) {
      Util::RegularExpression_ptr regex = new Util::RegularExpression(term_constant->primitive->getData());
      if(regex->str() == ".*" || regex->str() == "~(.*)") {
        *it = nullptr;
        it = prefix_shorten_terms_.erase(it);
        delete regex; regex = nullptr;
        continue;
      }

      std::string prefix = "";
      Util::RegularExpression_ptr temp_regex = regex;
      
      if(temp_regex->type() == Util::RegularExpression::Type::COMPLEMENT) {
        temp_regex = temp_regex->get_expr1();
      }
      
      while(temp_regex->type() == Util::RegularExpression::Type::CONCATENATION) {
        temp_regex = temp_regex->get_expr1();
      }

      if(temp_regex->type() == Util::RegularExpression::Type::STRING) {
        strings_to_shorten.push_back(temp_regex->get_string());
      } else {
        strings_to_shorten.push_back("");
      }
      delete regex; regex = nullptr;
    } else {
      strings_to_shorten.push_back(term_constant->primitive->getData());
    }
    it++;
  }

  std::string *arr = new std::string[strings_to_shorten.size()];
  for(int i = 0; i < strings_to_shorten.size(); i++) {
    arr[i] = strings_to_shorten[i];
    LOG(INFO) << arr[i];
  }
  std::string prefix = longestCommonPrefix(arr,strings_to_shorten.size());

  if(prefix == "") {
    computed_prefix_ = "";
    return;
  }

  prefix.erase(prefix.size()-1,prefix.size());

  delete[] arr; arr = nullptr;

  for(auto it : prefix_shorten_terms_) {
    auto term_constant = dynamic_cast<TermConstant_ptr>(it);
    std::string data = term_constant->primitive->getData();
    if(data[0] == '~') {
      data.erase(2,prefix.size());
    } else {
      if(data.substr(0,prefix.size()) != prefix) {
        LOG(INFO) << data;
        LOG(INFO) << data.substr(0, prefix.size());
        LOG(INFO) << prefix;
        LOG(FATAL) << "WHAT";
      }
      data.erase(0,prefix.size());
    }
    term_constant->primitive->setData(data);
  }

  computed_prefix_ = prefix;
}


// in_term regexes must always have type (var,term constant)

// create two new variables, R1 R2
// R1 is for prefixes, R2 for suffixes
// for each in_term with variable R,
// replace with in_term for variable R2 with regex suffixes
// then add new constraint for R1 being the disjunction of regex prefixes
// add new constraint R = R1 . R2
// R1,R2 no longer necessarydsdee
//
// return constraints to be added 
std::vector<Term_ptr> RegexDivideConquer::analyze_regexes() {
  std::vector<Term_ptr> constraints_to_add;

  // assume only one variable ("resource" for policy constraints)
  auto in_term_0 = dynamic_cast<In_ptr>(in_term_regexes_[0]);
  auto in_term_0_var_term = dynamic_cast<QualIdentifier_ptr>(in_term_0->left_term)->clone(); // will be used later
  std::string var_to_split_name = in_term_0_var_term->getVarName();
  
  if(symbol_table_->get_regex_split_var_name() == "") {
    symbol_table_->set_regex_split_var(var_to_split_name);
  }

  // std::string regex_prefix_var_name = symbol_table_->get_var_name_for_expression(in_term_0_var_term, Variable::Type::STRING) + "_PREFIX";
  // std::string regex_suffix_var_name = symbol_table_->get_var_name_for_expression(in_term_0_var_term, Variable::Type::STRING) + "_SUFFIX";
  // symbol_table_->add_variable(new Variable(regex_prefix_var_name, Variable::Type::STRING));
  // symbol_table_->add_variable(new Variable(regex_suffix_var_name, Variable::Type::STRING));

  std::stable_sort(in_term_regexes_.begin(),in_term_regexes_.end(), 
            [](Term_ptr left_term, Term_ptr right_term) -> bool {
              auto in_term_1 = dynamic_cast<In_ptr>(left_term);
              auto term_constant_1 = dynamic_cast<TermConstant_ptr>(in_term_1->right_term);

              auto in_term_2 = dynamic_cast<In_ptr>(right_term);
              auto term_constant_2 = dynamic_cast<TermConstant_ptr>(in_term_2->right_term);

              return term_constant_1->primitive->getData() < term_constant_2->primitive->getData();
            });


  std::vector<std::string> regexes;
  for(auto it : in_term_regexes_) {
    auto in_term = dynamic_cast<In_ptr>(it);
    auto term_constant = dynamic_cast<TermConstant_ptr>(in_term->right_term);
    std::string term_constant_as_string = term_constant->primitive->getData();
    regexes.push_back(term_constant_as_string);
  }

  std::string *arr = new std::string[regexes.size()];
  for(int i = 0; i < regexes.size(); i++) {
    arr[i] = regexes[i];
    // LOG(INFO) << arr[i];
  }

  // LOG(INFO) << "\nFinding prefixes: ";
  std::vector<std::pair<int,Util::RegularExpression_ptr>> prefixes = longest_common_prefixes_sorted(regexes);


  // auto regex_prefix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_prefix_var_name, Primitive::Type::SYMBOL)));
  // auto regex_suffix_term_qualid = new QualIdentifier(new Identifier(new Primitive(regex_suffix_var_name, Primitive::Type::SYMBOL)));

  // replace each regex_in_term with new regex for suffix
  // TODO: delets may be slow, can just replace primitives in terms instead
  auto prefix_iter = prefixes.begin();
  TermList_ptr prefix_suffix_or_list = new TermList();

  int start_index = 0;
  int end_index = 0;
  std::string prefix_string = "";
  while(prefix_iter != prefixes.end()) {
    
    // each prefix can have multiple corresponding suffixes
    // current position of prefix iterator has starting index and prefix string
    start_index = prefix_iter->first;
    prefix_string = prefix_iter->second->str();
    
    // end index is simply the beginning of starting index for the next prefix
    // since we have all necessary info from prefix iterator, can safely increment it
    prefix_iter++;
    if(prefix_iter != prefixes.end()) {
      end_index = prefix_iter->first;
    } else {
      end_index = in_term_regexes_.size();
    }

    if(prefix_string == "") {
      continue;
    }

    for(int i = start_index; i < end_index; i++) {
      auto &in_term_iter = in_term_regexes_.at(i);

LOG(INFO) << "ADDING TRANSFORMATION ";
LOG(INFO) << "  scope = " << symbol_table_->top_scope() ;
LOG(INFO) << "  term  = " << in_term_iter;
      symbol_table_->add_regex_prefix_transformation(symbol_table_->top_scope(), in_term_iter, prefix_string);

      // auto in_term = dynamic_cast<In_ptr>(in_term_iter);
      // auto in_term_constant = dynamic_cast<TermConstant_ptr>(in_term->right_term);
      // std::string regex_string = in_term_constant->primitive->getData();
    
      // // regex prefix has unnecessary parenthesis in raw string due to current implementation
      // // need to account for that when deleting prefix
      // auto r = new Util::RegularExpression(regex_string); 
      // regex_string = r->str();
      // delete r;
      // regex_string.erase(0, prefix_string.size());

      // auto regex_suffix_in_term_constant = new TermConstant(new Primitive(regex_string,Primitive::Type::REGEX));
      // auto suffix_in_term = new In(regex_suffix_term_qualid->clone(),regex_suffix_in_term_constant);
      // or_term_list->push_back(suffix_in_term);
    
      
      // auto f1 = new TermConstant(new Primitive("t",Primitive::Type::STRING));
      // auto f2 = new TermConstant(new Primitive("f",Primitive::Type::STRING));
      // if(i+1 == end_index && end_index == in_term_regexes_.size()) {
      //   f2->primitive->setData("t");
      // }
      // // delete in_term_iter;
      // // in_term_iter = false_term;
      // in_term->left_term = f1;
      // in_term->right_term = f2;
    }

    // auto or_term = new Or(or_term_list);
    // and_term_list->push_back(or_term);
    // auto and_term = new And(and_term_list);

    // auto &tt = in_term_regexes_.at(start_index);


    // prefix_suffix_or_list->push_back(and_term); 
    // std::cin.get();
  }

  // delete all old in_term regexes
  // replace them with TRUE ("" in "") and run syntactic processor/optimizer to get rid of them
  // auto empty_string_term_constant = new TermConstant(new Primitive("",Primitive::Type::REGEX));
  // for(auto &it : in_term_regexes_) {
  //   auto in_term = dynamic_cast<In_ptr>(it);
  //   delete in_term->left_term;
  //   in_term->left_term = empty_string_term_constant->clone();
  //   delete in_term->right_term;
  //   in_term->right_term = empty_string_term_constant->clone();
  // }

  // Or_ptr prefix_suffix_or_term = new Or(prefix_suffix_or_list);
  // constraints_to_add.push_back(prefix_suffix_or_term);

  // // finally, create term R = R1 . R2 to be added to constraint formula
  // auto term_list = new TermList();
  // term_list->push_back(regex_prefix_term_qualid->clone());
  // term_list->push_back(regex_suffix_term_qualid->clone());
  // auto concat_term = new Concat(term_list);

  // auto eq_term = new Eq(in_term_0_var_term->clone(), concat_term);
  // constraints_to_add.push_back(eq_term);

  // std::string p = "";
  
  // for(auto &it : in_term_regexes_) {
  //   if((prefix_iter+1) != prefixes.end() && curr_pos >= (prefix_iter+1)->first) {
  //     prefix_iter++;
  //   }
  //   p = prefix_iter->second->str();
  //   auto in_term = dynamic_cast<In_ptr>(it);
    
  //   // replace qualid term
  //   delete in_term->left_term;
  //   in_term->left_term = regex_suffix_term_qualid->clone();
  //   // replace prefix term
  //   // prefix is guaranteed to exist at beginning of string
  //   auto in_term_constant = dynamic_cast<TermConstant_ptr>(in_term->right_term);
  //   std::string regex_string = in_term_constant->primitive->getData();
  //   // regex prefix has unnecessary parenthesis in raw string due to current implementation
  //   // need to account for that when deleting prefix
  //   auto r = new Util::RegularExpression(regex_string); 
  //   regex_string = r->str();
  //   delete r;
  //   regex_string.erase(0, p.size());

  //   delete in_term->right_term;
  //   in_term->right_term = new TermConstant(new Primitive(regex_string,Primitive::Type::REGEX));
  //   curr_pos++;
  // }
  

  return constraints_to_add;
}

} // Solver
} // Vlab