/*
 * OptimizationRuleRunner.h
 *
 *  Created on: May 6, 2015
 *      Author: baki
 */

#ifndef SOLVER_OPTIMIZATIONRULERUNNER_H_
#define SOLVER_OPTIMIZATIONRULERUNNER_H_

#include <sstream>
#include <queue>
#include <map>
#include <functional>

#include <glog/logging.h>
#include "../smt/ast.h"
#include "Ast2Dot.h"
#include "SymbolTable.h"
#include "Counter.h"

namespace Vlab {
namespace SMT {

class OptimizationRuleRunner: public Visitor {
public:
	OptimizationRuleRunner(Script_ptr, SymbolTable_ptr);
	virtual ~OptimizationRuleRunner();
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
	bool has_optimization_rules();
	bool is_equivalent(Term_ptr, Term_ptr);
	std::string to_string(Visitable_ptr);
	Term_ptr generate_dummy_term();

	bool check_and_substitute_var(Term_ptr& term);

	Script_ptr root;
	SymbolTable_ptr symbol_table;
	std::queue<std::function <void (Term_ptr&)>> callbacks;
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SOLVER_OPTIMIZATIONRULERUNNER_H_ */
