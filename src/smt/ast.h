/*
 * ast.h
 *
 *  Created on: Nov 21, 2014
 *      Author: baki
 */

// TODO add specialized functions
#ifndef SMT_AST_H_
#define SMT_AST_H_

#include <iostream>
#include <string>
#include <sstream>
#include <cstdint>
#include <vector>
#include <stdexcept>

#include <glog/logging.h>
#include "typedefs.h"
#include "Visitable.h"
#include "Visitor.h"

namespace Vlab {
namespace SMT {

static const int AST_VLOG_LEVEL = 20;

class Script: public Visitable {
public:
  Script(CommandList_ptr);
  Script(const Script&);
  virtual Script_ptr clone() const;
  virtual ~Script();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  CommandList_ptr command_list;
};

class Command: public Visitable {
public:
  enum class Type
    : int {
      NONE = 0,
    SET_LOGIC,
    SET_OPTION,
    SET_INFO,
    DECLARE_SORT,
    DEFINE_SORT,
    DECLARE_FUN,
    DEFINE_FUN,
    PUSH,
    POP,
    ASSERT,
    CHECK_SAT,
    CHECK_SAT_AND_COUNT,
    GET_ASSERTIONS,
    GET_PROOF,
    GET_UNSAT_CORE,
    GET_VALUE,
    GET_ASSIGNMENT,
    GET_OPTION,
    GET_INFO,
    EXIT
  };

  Command();
  Command(Command::Type type);
  Command(const Command&);
  virtual Command_ptr clone() const;
  virtual ~Command();
  virtual std::string str() const;
  Command::Type getType() const;

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  class Name {
  public:
    static const std::string NONE;
    static const std::string SET_LOGIC;
    static const std::string SET_OPTION;
    static const std::string SET_INFO;
    static const std::string DECLARE_SORT;
    static const std::string DEFINE_SORT;
    static const std::string DECLARE_FUN;
    static const std::string DEFINE_FUN;
    static const std::string PUSH;
    static const std::string POP;
    static const std::string ASSERT;
    static const std::string CHECK_SAT;
    static const std::string CHECK_SAT_AND_COUNT;
    static const std::string GET_ASSERTIONS;
    static const std::string GET_PROOF;
    static const std::string GET_UNSAT_CORE;
    static const std::string GET_VALUE;
    static const std::string GET_ASSIGNMENT;
    static const std::string GET_OPTION;
    static const std::string GET_INFO;
    static const std::string EXIT;
  };

  friend std::ostream& operator<<(std::ostream& os, const Command& command);
protected:
  const Command::Type type;
};

/**
 * ( set-logic <symbol> )
 */
class SetLogic: public Command {
public:
  SetLogic(Primitive_ptr);
  SetLogic(const SetLogic&);
  virtual SetLogic_ptr clone() const;
  virtual ~SetLogic();

  virtual void visit_children(Visitor_ptr);

  Primitive_ptr symbol;
};

/**
 * ( declare-fun <symbol> ( <sort>* ) <sort> )
 */
class DeclareFun: public Command {
public:
  DeclareFun(Primitive_ptr, SortList_ptr, Sort_ptr);
  DeclareFun(const DeclareFun&);
  virtual DeclareFun_ptr clone() const;
  virtual ~DeclareFun();

  virtual void visit_children(Visitor_ptr);

  Primitive_ptr symbol;
  SortList_ptr sort_list;
  Sort_ptr sort;
};

/**
 * ( assert <term> )
 */
class Assert: public Command {
public:
  Assert(Term_ptr);
  Assert(const Assert&);
  virtual Assert_ptr clone() const;
  virtual ~Assert();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
};

/**
 * ( check-sat )
 */
class CheckSat: public Command {
public:
  CheckSat();
  CheckSat(Primitive_ptr);
  CheckSat(const CheckSat&);
  virtual CheckSat_ptr clone() const;
  virtual ~CheckSat();

  virtual void visit_children(Visitor_ptr);

  Primitive_ptr symbol;

};

class CheckSatAndCount: public Command {
public:
  CheckSatAndCount(Primitive_ptr);
  CheckSatAndCount(Primitive_ptr, Primitive_ptr);
  CheckSatAndCount(const CheckSatAndCount&);
  virtual CheckSatAndCount* clone() const;
  virtual ~CheckSatAndCount();

  virtual void visit_children(Visitor_ptr);

  Primitive_ptr bound;
  Primitive_ptr symbol;

};
/* ends commands */

/* start terms */
class Term: public Visitable {
public:
  enum class Type
    : int {
      NONE = 0,
    EXCLAMATION,
    EXISTS,
    FORALL,
    LET,
    TERM,
    AND,
    OR,
    NOT,
    UMINUS,
    MINUS,
    PLUS,
    EQ,
    NOTEQ,
    GT,
    GE,
    LT,
    LE,
    CONCAT,
    IN,
    NOTIN,
    LEN,
    CONTAINS,
    NOTCONTAINS,
    BEGINS,
    NOTBEGINS,
    ENDS,
    NOTENDS,
    INDEXOF,
    LASTINDEXOF,
    CHARAT,
    SUBSTRING,
    TOUPPER,
    TOLOWER,
    TRIM,
    REPLACE,
    COUNT,
    ITE,
    RECONCAT,
    TOREGEX,
    UNKNOWN,
    ASQUALIDENTIFIER,
    QUALIDENTIFIER,
    TERMCONSTANT
  };

  Term();
  Term(Term::Type name);
  Term(const Term&);
  virtual Term_ptr clone() const;
  virtual ~Term();

  virtual std::string str() const;
  Term::Type getType() const;

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  class Name {
  public:
    static const std::string NONE;
    static const std::string EXCLAMATION;
    static const std::string EXISTS;
    static const std::string FORALL;
    static const std::string LET;
    static const std::string TERM;
    static const std::string AND;
    static const std::string OR;
    static const std::string NOT;
    static const std::string UMINUS;
    static const std::string MINUS;
    static const std::string PLUS;
    static const std::string EQ;
    static const std::string NOTEQ;
    static const std::string GT;
    static const std::string GE;
    static const std::string LT;
    static const std::string LE;
    static const std::string CONCAT;
    static const std::string IN;
    static const std::string NOTIN;
    static const std::string LEN;
    static const std::string CONTAINS;
    static const std::string NOTCONTAINS;
    static const std::string BEGINS;
    static const std::string NOTBEGINS;
    static const std::string ENDS;
    static const std::string NOTENDS;
    static const std::string INDEXOF;
    static const std::string LASTINDEXOF;
    static const std::string CHARAT;
    static const std::string SUBSTRING;
    static const std::string TOUPPER;
    static const std::string TOLOWER;
    static const std::string TRIM;
    static const std::string REPLACE;
    static const std::string COUNT;
    static const std::string ITE;
    static const std::string RECONCAT;
    static const std::string TOREGEX;
    static const std::string ASQUALIDENTIFIER;
    static const std::string QUALIDENTIFIER;
    static const std::string TERMCONSTANT;
    static const std::string UNKNOWN;
  };

  friend std::ostream& operator<<(std::ostream& os, const Term& term);
//	friend std::ostream& operator<<(std::ostream& os, const Term_ptr& term);
protected:
  const Term::Type type;
};

class Exclamation: public Term {
public:
  Exclamation(Term_ptr, AttributeList_ptr);
  Exclamation(const Exclamation&);
  virtual Exclamation_ptr clone() const;
  virtual ~Exclamation();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
  AttributeList_ptr attribute_list;
};

class Exists: public Term {
public:
  Exists(SortedVarList_ptr, Term_ptr);
  Exists(const Exists&);
  virtual Exists_ptr clone() const;
  virtual ~Exists();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  SortedVarList_ptr sorted_var_list;
  Term_ptr term;
};

class ForAll: public Term {
public:
  ForAll(SortedVarList_ptr, Term_ptr);
  ForAll(const ForAll&);
  virtual ForAll_ptr clone() const;
  virtual ~ForAll();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  SortedVarList_ptr sorted_var_list;
  Term_ptr term;
};

class Let: public Term {
public:
  Let(VarBindingList_ptr, Term_ptr);
  Let(const Let&);
  virtual Let_ptr clone() const;
  virtual ~Let();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  VarBindingList_ptr var_binding_list;
  Term_ptr term;
};

class And: public Term {
public:
  And(TermList_ptr);
  And(const And&);
  virtual And_ptr clone() const;
  virtual ~And();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  TermList_ptr term_list;

};

class Or: public Term {
public:
  Or(TermList_ptr);
  Or(const Or&);
  virtual Or_ptr clone() const;
  virtual ~Or();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  TermList_ptr term_list;
};

class Not: public Term {
public:
  Not(Term_ptr);
  Not(const Not&);
  virtual Not_ptr clone() const;
  virtual ~Not();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
};

class UMinus: public Term {
public:
  UMinus(Term_ptr);
  UMinus(const UMinus&);
  virtual UMinus_ptr clone() const;
  virtual ~UMinus();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
};

class Minus: public Term {
public:
  Minus(Term_ptr, Term_ptr);
  Minus(const Minus&);
  virtual Minus_ptr clone() const;
  virtual ~Minus();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Plus: public Term {
public:
  Plus(Term_ptr, Term_ptr);
  Plus(const Plus&);
  virtual Plus_ptr clone() const;
  virtual ~Plus();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Eq: public Term {
public:
  Eq(Term_ptr, Term_ptr);
  Eq(const Eq&);
  virtual Eq_ptr clone() const;
  virtual ~Eq();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class NotEq: public Term {
public:
  NotEq(Term_ptr, Term_ptr);
  NotEq(const NotEq&);
  virtual NotEq_ptr clone() const;
  virtual ~NotEq();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Gt: public Term {
public:
  Gt(Term_ptr, Term_ptr);
  Gt(const Gt&);
  virtual Gt_ptr clone() const;
  virtual ~Gt();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Ge: public Term {
public:
  Ge(Term_ptr, Term_ptr);
  Ge(const Ge&);
  virtual Ge_ptr clone() const;
  virtual ~Ge();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Lt: public Term {
public:
  Lt(Term_ptr, Term_ptr);
  Lt(const Lt&);
  virtual Lt_ptr clone() const;
  virtual ~Lt();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Le: public Term {
public:
  Le(Term_ptr, Term_ptr);
  Le(const Le&);
  virtual Le_ptr clone() const;
  virtual ~Le();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Concat: public Term {
public:
  Concat(TermList_ptr);
  Concat(const Concat&);
  virtual Concat_ptr clone() const;
  virtual ~Concat();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  TermList_ptr term_list;
};

class In: public Term {
public:
  In(Term_ptr, Term_ptr);
  In(const In&);
  virtual In_ptr clone() const;
  virtual ~In();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class NotIn: public Term {
public:
  NotIn(Term_ptr, Term_ptr);
  NotIn(const NotIn&);
  virtual NotIn_ptr clone() const;
  virtual ~NotIn();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr left_term;
  Term_ptr right_term;
};

class Len: public Term {
public:
  Len(Term_ptr);
  Len(const Len&);
  virtual Len_ptr clone() const;
  virtual ~Len();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
};

class Contains: public Term {
public:
  Contains(Term_ptr, Term_ptr);
  Contains(const Contains&);
  virtual Contains_ptr clone() const;
  virtual ~Contains();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class NotContains: public Term {
public:
  NotContains(Term_ptr, Term_ptr);
  NotContains(const NotContains&);
  virtual NotContains_ptr clone() const;
  virtual ~NotContains();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class Begins: public Term {
public:
  Begins(Term_ptr, Term_ptr);
  Begins(const Begins&);
  virtual Begins_ptr clone() const;
  virtual ~Begins();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class NotBegins: public Term {
public:
  NotBegins(Term_ptr, Term_ptr);
  NotBegins(const NotBegins&);
  virtual NotBegins_ptr clone() const;
  virtual ~NotBegins();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class Ends: public Term {
public:
  Ends(Term_ptr, Term_ptr);
  Ends(const Ends&);
  virtual Ends_ptr clone() const;
  virtual ~Ends();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class NotEnds: public Term {
public:
  NotEnds(Term_ptr, Term_ptr);
  NotEnds(const NotEnds&);
  virtual NotEnds_ptr clone() const;
  virtual ~NotEnds();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class IndexOf: public Term {
public:
  IndexOf(Term_ptr, Term_ptr);
  IndexOf(const IndexOf&);
  virtual IndexOf_ptr clone() const;
  virtual ~IndexOf();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class LastIndexOf: public Term {
public:
  LastIndexOf(Term_ptr, Term_ptr);
  LastIndexOf(const LastIndexOf&);
  virtual LastIndexOf_ptr clone() const;
  virtual ~LastIndexOf();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
};

class CharAt: public Term {
public:
  CharAt(Term_ptr, Term_ptr);
  CharAt(const CharAt&);
  virtual CharAt_ptr clone() const;
  virtual ~CharAt();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr index_term;
};

class SubString: public Term {
public:
  SubString(Term_ptr, Term_ptr);
  SubString(Term_ptr, Term_ptr, Term_ptr);
  SubString(const SubString&);
  virtual SubString_ptr clone() const;
  virtual ~SubString();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr start_index_term;
  Term_ptr end_index_term;
};

class ToUpper: public Term {
public:
  ToUpper(Term_ptr);
  ToUpper(const ToUpper&);
  virtual ToUpper_ptr clone() const;
  virtual ~ToUpper();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
};

class ToLower: public Term {
public:
  ToLower(Term_ptr);
  ToLower(const ToLower&);
  virtual ToLower_ptr clone() const;
  virtual ~ToLower();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
};

class Trim: public Term {
public:
  Trim(Term_ptr);
  Trim(const Trim&);
  virtual Trim_ptr clone() const;
  virtual ~Trim();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
};

class Replace: public Term {
public:
  Replace(Term_ptr, Term_ptr, Term_ptr);
  Replace(const Replace&);
  virtual Replace_ptr clone() const;
  virtual ~Replace();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr search_term;
  Term_ptr replace_term;
};

class Count: public Term {
public:
  Count(Term_ptr, Term_ptr);
  Count(const Count&);
  virtual Count_ptr clone() const;
  virtual ~Count();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr subject_term;
  Term_ptr bound_term;
};

class Ite: public Term {
public:
  Ite(Term_ptr, Term_ptr, Term_ptr);
  Ite(const Ite&);
  virtual Ite_ptr clone() const;
  virtual ~Ite();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr cond;
  Term_ptr then_branch;
  Term_ptr else_branch;
};

class ReConcat: public Term {
public:
  ReConcat(TermList_ptr);
  ReConcat(const ReConcat&);
  virtual ReConcat_ptr clone() const;
  virtual ~ReConcat();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  TermList_ptr term_list;
  // ToRegex specifically
};

class ToRegex: public Term {
public:
  ToRegex(Term_ptr);
  ToRegex(const ToRegex&);
  virtual ToRegex_ptr clone() const;
  virtual ~ToRegex();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
};

class UnknownTerm: public Term {
public:
  UnknownTerm(Term_ptr, TermList_ptr);
  UnknownTerm(const UnknownTerm&);
  virtual UnknownTerm* clone() const;
  virtual ~UnknownTerm();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Term_ptr term;
  TermList_ptr term_list;
};

/**
 * "(" "as" identifier sort ")"
 * | identifier
 */
class QualIdentifier: public Term {
public:
  QualIdentifier(Identifier_ptr);
  QualIdentifier(const QualIdentifier&);
  virtual QualIdentifier_ptr clone() const;
  virtual ~QualIdentifier();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  std::string getVarName();

  Identifier_ptr identifier;

};

class AsQualIdentifier: public Term {
public:
  AsQualIdentifier(Identifier_ptr, Sort_ptr);
  AsQualIdentifier(const AsQualIdentifier&);
  virtual AsQualIdentifier_ptr clone() const;
  virtual ~AsQualIdentifier();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Identifier_ptr identifier;
  Sort_ptr sort;
};

class Primitive: public Visitable {
public:
  enum class Type
    : int {
      NONE = 0, BOOL, BINARY, DECIMAL, HEXADECIMAL, KEYWORD, NUMERAL, STRING, REGEX, SYMBOL
  };

  Primitive(const std::string data, const Primitive::Type type);
  Primitive(const Primitive&);
  virtual Primitive_ptr clone() const;
  virtual ~Primitive();
  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);
  std::string str() const;

  std::string getData() const;
  void setData(std::string data);
  Primitive::Type getType() const;
  void setType(Primitive::Type type);

  class Name {
  public:
    static const std::string NONE;
    static const std::string BOOL;
    static const std::string BINARY;
    static const std::string DECIMAL;
    static const std::string HEXADECIMAL;
    static const std::string KEYWORD;
    static const std::string NUMERAL;
    static const std::string STRING;
    static const std::string REGEX;
    static const std::string SYMBOL;
  };

  friend std::ostream& operator<<(std::ostream& os, const Primitive& primitive);
protected:
  std::string data;
  Primitive::Type type;
};

class TermConstant: public Term {
public:
  TermConstant(Primitive_ptr);
  TermConstant(const TermConstant&);
  virtual TermConstant_ptr clone() const;
  virtual ~TermConstant();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  std::string getValue() const;
  Primitive::Type getValueType() const;

  Primitive_ptr primitive;
};

/**
 *  : "(" identifier sort_list_ ")"
 *  | identifier
 *  | type
 */
class Sort: public Visitable {
public:
  Sort(Identifier_ptr);
  Sort(Identifier_ptr, SortList_ptr);
  Sort(TVariable_ptr);
  Sort(const Sort&);
  virtual Sort_ptr clone() const;
  virtual ~Sort();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Identifier_ptr identifier;
  SortList_ptr sort_list;
  TVariable_ptr var_type;

};

class TVariable: public Visitable {
public:
  enum class Type
    : int {
      NONE = 0, BOOL, INT, STRING
  };

  TVariable(TVariable::Type type);
  TVariable(const TVariable&);
  virtual TVariable_ptr clone() const;
  virtual ~TVariable();

  virtual std::string str() const;
  virtual TVariable::Type getType() const;

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  class Name {
  public:
    static const std::string NONE;
    static const std::string BOOL;
    static const std::string INT;
    static const std::string STRING;
  };

  friend std::ostream& operator<<(std::ostream& os, const TVariable& t_variable);
protected:
  const TVariable::Type type;
};

class TBool: public TVariable {
public:
  TBool();
  TBool(const TBool&);
  virtual TBool_ptr clone() const;
  virtual ~TBool();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);
};

class TInt: public TVariable {
public:
  TInt();
  TInt(const TInt&);
  virtual TInt_ptr clone() const;
  virtual ~TInt();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

};

class TString: public TVariable {
public:
  TString();
  TString(const TString&);
  virtual TString_ptr clone() const;
  virtual ~TString();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);
};

/**
 * : KEYWORD attribute_value
 * | KEYWORD
 */
class Attribute: public Visitable {
public:
  Attribute();
  Attribute(const Attribute&);
  virtual Attribute_ptr clone() const;
  virtual ~Attribute();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

};

/**
 * "(" SYMBOL sort ")"
 */
class SortedVar: public Visitable {
public:
  SortedVar(Primitive_ptr, Sort_ptr);
  SortedVar(const SortedVar&);
  virtual SortedVar_ptr clone() const;
  virtual ~SortedVar();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Primitive_ptr symbol;
  Sort_ptr sort;
};

/**
 * "(" SYMBOL term ")"
 */
class VarBinding: public Visitable {
public:
  VarBinding(Primitive_ptr, Term_ptr);
  VarBinding(const VarBinding&);
  virtual VarBinding_ptr clone() const;
  virtual ~VarBinding();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  Primitive_ptr symbol;
  Term_ptr term;
};

/**
 *  "(" "_" SYMBOL numeral_list_ ")"
 * | SYMBOL
 */
class Identifier: public Visitable {
public:
  Identifier(Primitive_ptr);
  Identifier(Primitive_ptr, Primitive_ptr, NumeralList_ptr);
  Identifier(const Identifier&);
  virtual Identifier_ptr clone() const;
  virtual ~Identifier();

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

  std::string getName();
  Primitive::Type getType();

  Primitive_ptr underscore;
  Primitive_ptr symbol;
  NumeralList_ptr numeral_list;
};

class Variable: public TVariable {
public:
  Variable(std::string name, Type);
  Variable(Primitive_ptr, Type);
  Variable(std::string name, Type, bool is_symbolic);
  Variable(Primitive_ptr, Type, bool is_symbolic);
  Variable(const Variable&);
  virtual Variable_ptr clone() const;
  virtual ~Variable();

  virtual std::string str() const;

  std::string getName() const;
  Variable::Type getType() const;
  bool isSymbolic() const;
  void setSymbolic(bool is_symbolic);

  virtual void accept(Visitor_ptr);
  virtual void visit_children(Visitor_ptr);

protected:
  std::string name;
  bool is_symbolic;
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SMT_AST_H_ */
