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
class CheckSatAndCount;
class Term;
class Exclamation;
class Exists;
class ForAll;
class Let;
class And;
class Or;
class Not;
class UMinus;
class Minus;
class Plus;
class Eq;
class NotEq;
class Gt;
class Ge;
class Lt;
class Le;
class Concat;
class NotIn;
class In;
class Len;
class Contains;
class NotContains;
class Begins;
class NotBegins;
class Ends;
class NotEnds;
class IndexOf;
class LastIndexOf;
class CharAt;
class SubString;
class SubStringFirstOf;
class SubStringLastOf;
class ToUpper;
class ToLower;
class Trim;
class Replace;
class Count;
class Ite;
class ReConcat;
class ToRegex;
class UnknownTerm;
class QualIdentifier;
class AsQualIdentifier;
class TermConstant;
class Sort;
class TVariable;
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
typedef SetLogic* SetLogic_ptr;
typedef DeclareFun* DeclareFun_ptr;
typedef Assert* Assert_ptr;
typedef CheckSat* CheckSat_ptr;
typedef Term* Term_ptr;
typedef std::vector<Term_ptr> TermList;
typedef TermList* TermList_ptr;
typedef Exclamation* Exclamation_ptr;
typedef Exists* Exists_ptr;
typedef ForAll* ForAll_ptr;
typedef Let* Let_ptr;
typedef And* And_ptr;
typedef Or* Or_ptr;
typedef Not* Not_ptr;
typedef UMinus* UMinus_ptr;
typedef Minus* Minus_ptr;
typedef Plus* Plus_ptr;
typedef Eq* Eq_ptr;
typedef NotEq* NotEq_ptr;
typedef Gt* Gt_ptr;
typedef Ge* Ge_ptr;
typedef Lt* Lt_ptr;
typedef Le* Le_ptr;
typedef Concat* Concat_ptr;
typedef In* In_ptr;
typedef NotIn* NotIn_ptr;
typedef Len* Len_ptr;
typedef Contains* Contains_ptr;
typedef NotContains* NotContains_ptr;
typedef Begins* Begins_ptr;
typedef NotBegins* NotBegins_ptr;
typedef Ends* Ends_ptr;
typedef NotEnds* NotEnds_ptr;
typedef IndexOf* IndexOf_ptr;
typedef LastIndexOf* LastIndexOf_ptr;
typedef CharAt* CharAt_ptr;
typedef SubString* SubString_ptr;
typedef SubStringFirstOf* SubStringFirstOf_ptr;
typedef SubStringLastOf* SubStringLastOf_ptr;
typedef ToUpper* ToUpper_ptr;
typedef ToLower* ToLower_ptr;
typedef Trim* Trim_ptr;
typedef Replace* Replace_ptr;
typedef Count* Count_ptr;
typedef Ite* Ite_ptr;
typedef ReConcat* ReConcat_ptr;
typedef ToRegex* ToRegex_ptr;
typedef UnknownTerm* Unknown_ptr;
typedef Sort* Sort_ptr;
typedef std::vector<Sort_ptr> SortList;
typedef SortList* SortList_ptr;
typedef TVariable* TVariable_ptr;
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
