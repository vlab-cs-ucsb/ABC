/*
 * SyntacticOptimizer.h
 *
 *  Created on: Apr 28, 2015
 *      Author: baki
 */

#ifndef SOLVER_SYNTACTICOPTIMIZER_H_
#define SOLVER_SYNTACTICOPTIMIZER_H_

#include <iostream>
#include <sstream>
#include <queue>
#include <functional>

#include <glog/logging.h>
#include "../smt/ast.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

// TODO There may be a bug when we try to add multiple callbacks in one visit
// check that behaviour especially for relational operations and
// 'not' operation (add more optimizaiton for not)
class SyntacticOptimizer: public Visitor {
public:
	SyntacticOptimizer(Script_ptr, SymbolTable_ptr);
	virtual ~SyntacticOptimizer();

	void start();
	void end();

	void visitScript(Script_ptr);
	void visitCommand(Command_ptr);
	void visitTerm(Term_ptr);
	void visitExclamation(Exclamation_ptr);
	void visitExists(Exists_ptr);
	void visitForAll(ForAll_ptr);
	void visitLet(Let_ptr);
	void visitAnd(And_ptr);
	void visitOr(Or_ptr);
	void visitNot(Not_ptr);
	void visitUMinus(UMinus_ptr);
	void visitMinus(Minus_ptr);
	void visitPlus(Plus_ptr);
	void visitEq(Eq_ptr);
	void visitGt(Gt_ptr);
	void visitGe(Ge_ptr);
	void visitLt(Lt_ptr);
	void visitLe(Le_ptr);
	void visitConcat(Concat_ptr);
	void visitIn(In_ptr);
	void visitLen(Len_ptr);
	void visitContains(Contains_ptr);
	void visitBegins(Begins_ptr);
	void visitEnds(Ends_ptr);
	void visitIndexOf(IndexOf_ptr);
	void visitReplace(Replace_ptr);
	void visitCount(Count_ptr);
	void visitIte(Ite_ptr);
	void visitReConcat(ReConcat_ptr);
	void visitToRegex(ToRegex_ptr);
	void visitUnknownTerm(Unknown_ptr);
	void visitAsQualIdentifier(AsQualIdentifier_ptr);
	void visitQualIdentifier(QualIdentifier_ptr);
	void visitTermConstant(TermConstant_ptr);
	void visitSort(Sort_ptr);
	void visitTVariable(TVariable_ptr);
	void visitTBool(TBool_ptr);
	void visitTInt(TInt_ptr);
	void visitTString(TString_ptr);
	void visitAttribute(Attribute_ptr);
	void visitSortedVar(SortedVar_ptr);
	void visitVarBinding(VarBinding_ptr);
	void visitIdentifier(Identifier_ptr);
	void visitPrimitive(Primitive_ptr);
	void visitVariable(Variable_ptr);
protected:
	void visit_and_callback(Term_ptr&);
	bool is_equivalent(Term_ptr, Term_ptr);
	std::string to_string(Visitable_ptr);
	std::string escape_regex(std::string regex);
	std::string regex_to_str(std::string regex);
	void pre_concat_constants(TermConstant_ptr, TermConstant_ptr);
	bool check_and_process_in_transformation(Term_ptr, bool is_complement);
	// TODO check len transformation later when pres. arith. added.
	bool check_and_process_len_transformation(Term_ptr, Term_ptr&, Term_ptr&);
	bool __check_and_process_len_transformation(std::string operation, Term_ptr&, Term_ptr&);
	std::string syntactic_reverse_relation(std::string operation);
	Term_ptr generate_term_constant(std::string data, Primitive::Type type);
	Term_ptr generate_dummy_term();
	void add_callback_to_replace_with_bool(Term_ptr, std::string value);
	bool check_bool_constant_value(Term_ptr, std::string value);

	Script_ptr root;
	SymbolTable_ptr symbol_table;
	Assert_ptr current_assert;
	std::queue<std::function <void (Term_ptr&)>> callbacks;
private:
	static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_SYNTACTICOPTIMIZER_H_ */
