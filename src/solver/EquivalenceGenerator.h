#ifndef SOLVER_EQUIVALENCEGENERATOR_H_
#define SOLVER_EQUIVALENCEGENERATOR_H_

#include <cstdbool>
#include <map>

#include "smt/ast.h"
#include "smt/typedefs.h"
#include "AstTraverser.h"
#include "SymbolTable.h"

namespace Vlab {
namespace Solver {

using SubstitutionSets = std::vector<std::set<std::string>>;
using SubstitutionMap = std::map<SMT::Variable_ptr, SMT::Term_ptr>;
using SubstitutionTable = std::map<SMT::Visitable_ptr, SubstitutionMap>;


class EquivalenceGenerator: public AstTraverser {
  public:
	EquivalenceGenerator(SMT::Script_ptr, SymbolTable_ptr);
	virtual ~EquivalenceGenerator();
	void start();
	void end();

	void setCallbacks();
	void visitAnd(SMT::And_ptr);
	void visitOr(SMT::Or_ptr);
	void visitEq(SMT::Eq_ptr);
	bool make_substitution_rules();
	bool add_variable_substitution_rule(SMT::Variable_ptr, SMT::Term_ptr);


	std::string get_string_rep(SMT::Term_ptr);
	void extend_equiv_class(std::string, std::string);
	void merge(int, int);
	void clear_mappings();
	void reset_substitution_rules();


  protected:
	SymbolTable_ptr symbol_table_;

	SubstitutionSets sub_components_;
	std::map<std::string, int> term_to_component_map_;

	std::map<std::string, SMT::Term_ptr> variables_;
	std::map<std::string, SMT::Term_ptr> constants_;

	SubstitutionTable substitution_map_;

	std::set<SMT::Visitable_ptr> set_to_false_;



  private:
	static const int VLOG_LEVEL;
};

} /* namespace Solver */
} /* namespace Vlab */

#endif /* SOLVER_EQUIVALENCEGENERATOR_H_ */
