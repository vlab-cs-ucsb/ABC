/*
 * Ast2Dot.cpp
 *
 *  Created on: Nov 23, 2014
 *      Author: baki
 */

#include "Ast2Dot.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

int Ast2Dot::name_counter = 0;

Ast2Dot::Ast2Dot(std::ostream* out)
        : m_out(out), count(0) {
}

Ast2Dot::~Ast2Dot() {
}

void Ast2Dot::start(Visitable_ptr p) {
  count = 0;
  *m_out << "digraph G { " << std::endl;

  if (dynamic_cast<Script_ptr>(p)) {
    add_node(count, "Script");
  } else {
    add_node(count, "Partial");
  }

  s.push(count);
  visit(p);
  s.pop();

  end();
}

void Ast2Dot::start() {
  LOG(FATAL)<< "Please use the start function that accepts a parameter.";}

void Ast2Dot::end() {
  *m_out << "}" << std::endl;
}

void Ast2Dot::add_edge(u_int64_t p, u_int64_t c) {
  *m_out << "\"" << p << "\" -> \"" << c << "\";" << std::endl;

}

void Ast2Dot::add_node(u_int64_t c, std::string label) {
  *m_out << "\"" << c << "\" [label=\"" << label << "\"];" << std::endl;
}

void Ast2Dot::draw(std::string label, Visitable_ptr p) {
  count++;
  add_node(count, label);
  add_edge(s.top(), count);
  s.push(count);
  if (p != nullptr) {
    visit_children_of(p);
  }
  s.pop();

}

void Ast2Dot::draw_terminal(std::string label) {
  count++;
  *m_out << "\"" << count << "\" [label=\"" << label << "\"];" << std::endl;
  add_edge(s.top(), count);
}

void Ast2Dot::visitScript(Script_ptr script) {
  if (script != nullptr) {
    visit_children_of(script);
  }
}

void Ast2Dot::visitCommand(Command_ptr command) {
  draw(command->str(), command);
}

void Ast2Dot::visitAssert(Assert_ptr assert_command) {
  draw(assert_command->str(), assert_command);
}

void Ast2Dot::visitTerm(Term_ptr term) {
  draw(term->str(), term);
}

void Ast2Dot::visitSort(Sort_ptr sort) {
  draw("Sort", sort);
}

void Ast2Dot::visitAttribute(Attribute_ptr attribute) {
  draw("Attribute", attribute);
}

void Ast2Dot::visitSortedVar(SortedVar_ptr sorted_var) {
  draw("SortedVar", sorted_var);
}

void Ast2Dot::visitVarBinding(VarBinding_ptr var_binding) {
  draw("VarBinding", var_binding);
}

void Ast2Dot::visitIdentifier(Identifier_ptr identifier) {
  draw("Identifier", identifier);
}

void Ast2Dot::visitExclamation(Exclamation_ptr exclamation_term) {
  visitTerm(exclamation_term);
}

void Ast2Dot::visitExists(Exists_ptr exists_term) {
  visitTerm(exists_term);
}

void Ast2Dot::visitForAll(ForAll_ptr for_all_term) {
  visitTerm(for_all_term);
}

void Ast2Dot::visitLet(Let_ptr let_term) {
  visitTerm(let_term);
}

void Ast2Dot::visitAnd(And_ptr and_term) {
  visitTerm(and_term);
}

void Ast2Dot::visitOr(Or_ptr or_term) {
  visitTerm(or_term);
}

void Ast2Dot::visitNot(Not_ptr not_term) {
  visitTerm(not_term);
}

void Ast2Dot::visitUMinus(UMinus_ptr u_minus_term) {
  visitTerm(u_minus_term);
}

void Ast2Dot::visitMinus(Minus_ptr minus_term) {
  visitTerm(minus_term);
}

void Ast2Dot::visitPlus(Plus_ptr plus_term) {
  visitTerm(plus_term);
}

void Ast2Dot::visitTimes(Times_ptr times_term) {
  visitTerm(times_term);
}

void Ast2Dot::visitEq(Eq_ptr eq_term) {
  visitTerm(eq_term);
}

void Ast2Dot::visitNotEq(NotEq_ptr not_eq_term) {
  visitTerm(not_eq_term);
}

void Ast2Dot::visitGt(Gt_ptr gt_term) {
  visitTerm(gt_term);
}

void Ast2Dot::visitGe(Ge_ptr ge_term) {
  visitTerm(ge_term);
}

void Ast2Dot::visitLt(Lt_ptr lt_term) {
  visitTerm(lt_term);
}

void Ast2Dot::visitLe(Le_ptr le_term) {
  visitTerm(le_term);
}

void Ast2Dot::visitConcat(Concat_ptr concat_term) {
  visitTerm(concat_term);
}

void Ast2Dot::visitIn(In_ptr in_term) {
  visitTerm(in_term);
}

void Ast2Dot::visitNotIn(NotIn_ptr not_in_term) {
  visitTerm(not_in_term);
}

void Ast2Dot::visitLen(Len_ptr len_term) {
  visitTerm(len_term);
}

void Ast2Dot::visitContains(Contains_ptr contains_term) {
  visitTerm(contains_term);
}

void Ast2Dot::visitNotContains(NotContains_ptr not_contains_term) {
  visitTerm(not_contains_term);
}

void Ast2Dot::visitBegins(Begins_ptr begins_term) {
  visitTerm(begins_term);
}

void Ast2Dot::visitNotBegins(NotBegins_ptr not_begins_term) {
  visitTerm(not_begins_term);
}

void Ast2Dot::visitEnds(Ends_ptr ends_term) {
  visitTerm(ends_term);
}

void Ast2Dot::visitNotEnds(NotEnds_ptr not_ends_term) {
  visitTerm(not_ends_term);
}

void Ast2Dot::visitIndexOf(IndexOf_ptr index_of_term) {
  visitTerm(index_of_term);
}

void Ast2Dot::visitLastIndexOf(SMT::LastIndexOf_ptr last_index_of_term) {
  visitTerm(last_index_of_term);
}

void Ast2Dot::visitCharAt(SMT::CharAt_ptr char_at_term) {
  visitTerm(char_at_term);
}

void Ast2Dot::visitSubString(SMT::SubString_ptr sub_string_term) {
  visitTerm(sub_string_term);
}

void Ast2Dot::visitToUpper(SMT::ToUpper_ptr to_upper_term) {
  visitTerm(to_upper_term);
}

void Ast2Dot::visitToLower(SMT::ToLower_ptr to_lower_term) {
  visitTerm(to_lower_term);
}

void Ast2Dot::visitTrim(SMT::Trim_ptr trim_term) {
  visitTerm(trim_term);
}

void Ast2Dot::visitReplace(Replace_ptr replace_term) {
  visitTerm(replace_term);
}

void Ast2Dot::visitCount(Count_ptr count_term) {
  visitTerm(count_term);
}

void Ast2Dot::visitIte(Ite_ptr ite_term) {
  visitTerm(ite_term);
}

void Ast2Dot::visitReConcat(ReConcat_ptr re_concat_term) {
  visitTerm(re_concat_term);
}

void Ast2Dot::visitToRegex(ToRegex_ptr to_regex_term) {
  visitTerm(to_regex_term);
}

void Ast2Dot::visitUnknownTerm(Unknown_ptr unknown_term) {
  visitTerm(unknown_term);
}

void Ast2Dot::visitAsQualIdentifier(AsQualIdentifier_ptr as_qid_term) {
  visitTerm(as_qid_term);
}

void Ast2Dot::visitQualIdentifier(QualIdentifier_ptr qi_term) {
  visitTerm(qi_term);
}

void Ast2Dot::visitTermConstant(TermConstant_ptr term_constant) {
  visitTerm(term_constant);
}

void Ast2Dot::visitTVariable(TVariable_ptr t_variable) {
  draw_terminal(t_variable->str());
}

void Ast2Dot::visitTBool(TBool_ptr t_bool) {
  draw_terminal(t_bool->str());
}

void Ast2Dot::visitTInt(TInt_ptr t_int) {
  draw_terminal(t_int->str());
}

void Ast2Dot::visitTString(TString_ptr t_string) {
  draw_terminal(t_string->str());
}

void Ast2Dot::visitPrimitive(Primitive_ptr primitive) {
  draw_terminal(primitive->str());
}

void Ast2Dot::visitVariable(Variable_ptr variable) {
  draw_terminal(variable->str());
}

int Ast2Dot::inspectAST(Visitable_ptr node) {
  std::stringstream file_name_ss;
  file_name_ss << "./output/ast_" << name_counter++ << ".dot";
  std::string file_name = file_name_ss.str();
  std::ofstream outfile(file_name.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file_name << std::endl;
    exit(2);
  }
  m_out = &outfile;
  start(node);
  outfile.close();

  std::string dot_cmd("xdot " + file_name + " &");
  return std::system(dot_cmd.c_str());
}

bool Ast2Dot::isEquivalent(SMT::Visitable_ptr x, SMT::Visitable_ptr y) {
  if (x == y) {
    return true;
  }

  return (Ast2Dot::toString(x) == Ast2Dot::toString(y));
}

std::string Ast2Dot::toString(SMT::Visitable_ptr node) {
  std::stringstream ss;
  Ast2Dot toDot(&ss);
  toDot.start(node);
  return ss.str();
}

} /* namespace Solver */
} /* namespace Vlab */


