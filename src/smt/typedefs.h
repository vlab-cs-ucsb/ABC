/*
 * typedefs.h
 *
 *  Created on: Apr 9, 2015
 *      Author: baki
 */

#ifndef SMT_TYPEDEFS_H_
#define SMT_TYPEDEFS_H_

namespace Vlab {
namespace SMT {

/* Forward Declarations for typedefs */

/* SMT AST STRUCTURE CLASSES */
class Script;
class Command;
class SetLogic;
class DeclareFun;
class Assert;
class CheckSat;
class Term;
class And;
class Not;
class UMinus;
class Minus;
class Plus;
class Eq;
class Gt;
class Ge;
class Lt;
class Le;
class Ite;
class ReConcat;
class ReOr;
class Concat;
class In;
class Len;
class ToRegex;
class UnknownTerm;
class QualIdentifier;
class AsQualIdentifier;
class TermConstant;
class Sort;
class VarType;
class TBool;
class TInt;
class TString;
class Attribute;
class SortedVar;
class VarBinding;
class Identifier;
class Primitive;
class Variable;

/* ABSTRACT CLASSES*/
class Visitor;
class Visitable;

/* TYPE_DEFINITIONS */
typedef Script* Script_ptr;
typedef Command* Command_ptr;
typedef std::vector<Command_ptr> CommandList;
typedef CommandList* CommandList_ptr;
typedef Assert* Assert_ptr;
typedef CheckSat* CheckSat_ptr;
typedef Term* Term_ptr;
typedef std::vector<Term_ptr> TermList;
typedef TermList* TermList_ptr;
typedef And* And_ptr;
typedef Not* Not_ptr;
typedef UMinus* UMinus_ptr;
typedef Minus* Minus_ptr;
typedef Plus* Plus_ptr;
typedef Eq* Eq_ptr;
typedef Gt* Gt_ptr;
typedef Ge* Ge_ptr;
typedef Lt* Lt_ptr;
typedef Le* Le_ptr;
typedef Ite* Ite_ptr;
typedef ReConcat* ReConcat_ptr;
typedef ReOr* ReOr_ptr;
typedef Concat* Concat_ptr;
typedef In* In_ptr;
typedef Len* Len_ptr;
typedef ToRegex* ToRegex_ptr;
typedef UnknownTerm* Unknown_ptr;
typedef Sort* Sort_ptr;
typedef std::vector<Sort_ptr> SortList;
typedef SortList* SortList_ptr;
typedef VarType* VarType_ptr;
typedef TBool* TBool_ptr;
typedef TInt* TInt_ptr;
typedef TString* TString_ptr;
typedef Attribute* Attribute_ptr;
typedef std::vector<Attribute_ptr> AttributeList;
typedef AttributeList* AttributeList_ptr;
typedef SortedVar* SortedVar_ptr;
typedef std::vector<SortedVar_ptr> SortedVarList;
typedef SortedVarList* SortedVarList_ptr;
typedef VarBinding* VarBinding_ptr;
typedef std::vector<VarBinding_ptr> VarBindingList;
typedef VarBindingList* VarBindingList_ptr;
typedef QualIdentifier* QualIdentifier_ptr;
typedef AsQualIdentifier* AsQualIdentifier_ptr;
typedef TermConstant* TermConstant_ptr;
typedef Identifier* Identifier_ptr;
typedef Primitive* Primitive_ptr;
typedef Variable* Variable_ptr;
typedef std::vector<Primitive_ptr> NumeralList;
typedef NumeralList* NumeralList_ptr;

typedef Visitor* Visitor_ptr;
typedef Visitable* Visitable_ptr;


} /* namespace SMT */
} /* namespace Vlab */

#endif /* SMT_TYPEDEFS_H_ */
