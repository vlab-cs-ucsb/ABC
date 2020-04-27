/*
 * typedefs.h
 *
 *  Created on: Apr 9, 2015
 *      Author: baki
 */

#ifndef SMT_TYPEDEFS_H_
#define SMT_TYPEDEFS_H_

#include <vector>

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
class Times;
class Div;
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
class ToUpper;
class ToLower;
class Trim;
class ToString;
class ToInt;
class Replace;
class Count;
class Ite;
class ReConcat;
class ReUnion;
class ReInter;
class ReStar;
class RePlus;
class ReOpt;
class ReLoop;
class ReComp;
class ReDiff;
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
class TRegExp;
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
using Script_ptr = Script*;
using Command_ptr = Command*;
using CommandList = std::vector<Command_ptr>;
using CommandList_ptr = CommandList*;
using SetLogic_ptr = SetLogic*;
using DeclareFun_ptr = DeclareFun*;
using Assert_ptr = Assert*;
using CheckSat_ptr = CheckSat*;
using Term_ptr = Term*;
using TermList = std::vector<Term_ptr>;
using TermList_ptr = TermList*;
using Exclamation_ptr = Exclamation*;
using Exists_ptr = Exists*;
using ForAll_ptr = ForAll*;
using Let_ptr = Let*;
using And_ptr = And*;
using Or_ptr = Or*;
using Not_ptr = Not*;
using UMinus_ptr = UMinus*;
using Minus_ptr = Minus*;
using Plus_ptr = Plus*;
using Eq_ptr = Eq*;
using Times_ptr = Times*;
using Div_ptr = Div*;
using NotEq_ptr = NotEq*;
using Gt_ptr = Gt*;
using Ge_ptr = Ge*;
using Lt_ptr = Lt*;
using Le_ptr = Le*;
using Concat_ptr = Concat*;
using In_ptr = In*;
using NotIn_ptr = NotIn*;
using Len_ptr = Len*;
using Contains_ptr = Contains*;
using NotContains_ptr = NotContains*;
using Begins_ptr = Begins*;
using NotBegins_ptr = NotBegins*;
using Ends_ptr = Ends*;
using NotEnds_ptr = NotEnds*;
using IndexOf_ptr = IndexOf*;
using LastIndexOf_ptr = LastIndexOf*;
using CharAt_ptr = CharAt*;
using SubString_ptr = SubString*;
using ToUpper_ptr = ToUpper*;
using ToLower_ptr = ToLower*;
using Trim_ptr = Trim*;
using ToString_ptr = ToString*;
using ToInt_ptr = ToInt*;
using Replace_ptr = Replace*;
using Count_ptr = Count*;
using Ite_ptr = Ite*;
using ReConcat_ptr = ReConcat*;
using ReUnion_ptr = ReUnion*;
using ReInter_ptr = ReInter*;
using ReStar_ptr = ReStar*;
using RePlus_ptr = RePlus*;
using ReOpt_ptr = ReOpt*;
using ReLoop_ptr = ReLoop*;
using ReComp_ptr = ReComp*;
using ReDiff_ptr = ReDiff*;
using ToRegex_ptr = ToRegex*;
using Unknown_ptr = UnknownTerm*;
using Sort_ptr = Sort*;
using SortList = std::vector<Sort_ptr>;
using SortList_ptr = SortList*;
using TVariable_ptr = TVariable*;
using TBool_ptr = TBool*;
using TInt_ptr = TInt*;
using TString_ptr = TString*;
using TRegExp_ptr = TRegExp*;
using Attribute_ptr = Attribute*;
using AttributeList = std::vector<Attribute_ptr>;
using AttributeList_ptr = AttributeList*;
using SortedVar_ptr = SortedVar*;
using SortedVarList = std::vector<SortedVar_ptr>;
using SortedVarList_ptr = SortedVarList*;
using VarBinding_ptr = VarBinding*;
using VarBindingList = std::vector<VarBinding_ptr>;
using VarBindingList_ptr = VarBindingList*;
using QualIdentifier_ptr = QualIdentifier*;
using AsQualIdentifier_ptr = AsQualIdentifier*;
using TermConstant_ptr = TermConstant*;
using Identifier_ptr = Identifier*;
using Primitive_ptr = Primitive*;
using Variable_ptr = Variable*;
using NumeralList = std::vector<Primitive_ptr>;
using NumeralList_ptr = NumeralList*;

using Visitor_ptr = Visitor*;
using Visitable_ptr = Visitable*;

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SMT_TYPEDEFS_H_ */
