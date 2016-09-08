/*
 * ast.h
 *
 *  Created on: Nov 21, 2014
 *      Author: baki
 */

#ifndef SMT_AST_H_
#define SMT_AST_H_

#include <iostream>
#include <stdio.h>
#include <sstream>
#include <stdarg.h>
#include <stdexcept>
#include <string>
#include <vector>

#include <glog/logging.h>

#include "typedefs.h"
#include "Visitable.h"
#include "Visitor.h"


namespace Vlab {
namespace SMT {

static const int VLOG_LEVEL = 31;

class Script : public Visitable {
 public:
  Script(CommandList_ptr);
  Script(const Script&);
  virtual Script_ptr clone() const;
  virtual ~Script();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  CommandList_ptr command_list;
};

class Command : public Visitable {
 public:
  enum class Type
    : unsigned char {
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
    GET_MODEL,
    EXIT
  };

  Command();
  Command(Command::Type type);
  Command(const Command&);
  virtual Command_ptr clone() const;
  virtual ~Command();
  virtual std::string str() const;
  virtual Command::Type getType() const;

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  friend std::ostream& operator<<(std::ostream& os, const Command& command);
 protected:
  const Command::Type type;
};

/**
 * ( set-logic <symbol> )
 */
class SetLogic : public Command {
 public:
  SetLogic(Primitive_ptr);
  SetLogic(const SetLogic&);
  virtual SetLogic_ptr clone() const override;
  virtual ~SetLogic();
  virtual std::string str() const override;
  virtual void visit_children(Visitor_ptr) override;

  Primitive_ptr symbol;
};

/**
 * ( declare-fun <symbol> ( <sort>* ) <sort> )
 */
class DeclareFun : public Command {
 public:
  DeclareFun(Primitive_ptr, SortList_ptr, Sort_ptr);
  DeclareFun(const DeclareFun&);
  virtual DeclareFun_ptr clone() const override;
  virtual ~DeclareFun();
  virtual std::string str() const override;
  virtual void visit_children(Visitor_ptr) override;

  Primitive_ptr symbol;
  SortList_ptr sort_list;
  Sort_ptr sort;
};

/**
 * ( assert <term> )
 */
class Assert : public Command {
 public:
  Assert(Term_ptr);
  Assert(const Assert&);
  virtual Assert_ptr clone() const override;
  virtual ~Assert();
  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

/**
 * ( check-sat )
 */
class CheckSat : public Command {
 public:
  CheckSat();
  CheckSat(Primitive_ptr);
  CheckSat(const CheckSat&);
  virtual CheckSat_ptr clone() const override;
  virtual ~CheckSat();
  virtual std::string str() const override;
  virtual void visit_children(Visitor_ptr) override;

  Primitive_ptr symbol;

};

class CheckSatAndCount : public Command {
 public:
  CheckSatAndCount(Primitive_ptr);
  CheckSatAndCount(Primitive_ptr, Primitive_ptr);
  CheckSatAndCount(const CheckSatAndCount&);
  virtual CheckSatAndCount* clone() const override;
  virtual ~CheckSatAndCount();
  virtual std::string str() const override;
  virtual void visit_children(Visitor_ptr) override;

  Primitive_ptr bound;
  Primitive_ptr symbol;

};
/* ends commands */

/* start terms */
/**
 * TODO Avoid Using Type Information, refactor usages and remove it
 */
class Term : public Visitable {
 public:
  enum class Type
    : unsigned char {
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
    TIMES,
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
    TOSTRING,
    TOINT,
    REPLACE,
    COUNT,
    ITE,
    RECONCAT,
    REUNION,
    REINTER,
    RESTAR,
    REPLUS,
    REOPT,
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
  Term::Type type() const;

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  friend std::ostream& operator<<(std::ostream& os, const Term& term);
//  friend std::ostream& operator<<(std::ostream& os, const Term_ptr& term);
 protected:
  const Term::Type type_;
};

class Exclamation : public Term {
 public:
  Exclamation(Term_ptr, AttributeList_ptr);
  Exclamation(const Exclamation&);
  virtual Exclamation_ptr clone() const override;
  virtual ~Exclamation();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
  AttributeList_ptr attribute_list;
};

class Exists : public Term {
 public:
  Exists(SortedVarList_ptr, Term_ptr);
  Exists(const Exists&);
  virtual Exists_ptr clone() const override;
  virtual ~Exists();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  SortedVarList_ptr sorted_var_list;
  Term_ptr term;
};

class ForAll : public Term {
 public:
  ForAll(SortedVarList_ptr, Term_ptr);
  ForAll(const ForAll&);
  virtual ForAll_ptr clone() const override;
  virtual ~ForAll();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  SortedVarList_ptr sorted_var_list;
  Term_ptr term;
};

class Let : public Term {
 public:
  Let(VarBindingList_ptr, Term_ptr);
  Let(const Let&);
  virtual Let_ptr clone() const override;
  virtual ~Let();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  VarBindingList_ptr var_binding_list;
  Term_ptr term;
};

class And : public Term {
 public:
  And(TermList_ptr);
  And(const And&);
  virtual And_ptr clone() const override;
  virtual ~And();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class Or : public Term {
 public:
  Or(TermList_ptr);
  Or(const Or&);
  virtual Or_ptr clone() const override;
  virtual ~Or();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class Not : public Term {
 public:
  Not(Term_ptr);
  Not(const Not&);
  virtual Not_ptr clone() const override;
  virtual ~Not();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class UMinus : public Term {
 public:
  UMinus(Term_ptr);
  UMinus(const UMinus&);
  virtual UMinus_ptr clone() const override;
  virtual ~UMinus();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class Minus : public Term {
 public:
  Minus(Term_ptr, Term_ptr);
  Minus(const Minus&);
  virtual Minus_ptr clone() const override;
  virtual ~Minus();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Plus : public Term {
 public:
  Plus(TermList_ptr);
  Plus(const Plus&);
  virtual Plus_ptr clone() const override;
  virtual ~Plus();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class Times : public Term {
 public:
  Times(TermList_ptr);
  Times(const Times&);
  virtual Times_ptr clone() const override;
  virtual ~Times();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class Eq : public Term {
 public:
  Eq(Term_ptr, Term_ptr);
  Eq(const Eq&);
  virtual Eq_ptr clone() const override;
  virtual ~Eq();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class NotEq : public Term {
 public:
  NotEq(Term_ptr, Term_ptr);
  NotEq(const NotEq&);
  virtual NotEq_ptr clone() const override;
  virtual ~NotEq();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Gt : public Term {
 public:
  Gt(Term_ptr, Term_ptr);
  Gt(const Gt&);
  virtual Gt_ptr clone() const override;
  virtual ~Gt();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Ge : public Term {
 public:
  Ge(Term_ptr, Term_ptr);
  Ge(const Ge&);
  virtual Ge_ptr clone() const override;
  virtual ~Ge();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Lt : public Term {
 public:
  Lt(Term_ptr, Term_ptr);
  Lt(const Lt&);
  virtual Lt_ptr clone() const override;
  virtual ~Lt();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Le : public Term {
 public:
  Le(Term_ptr, Term_ptr);
  Le(const Le&);
  virtual Le_ptr clone() const override;
  virtual ~Le();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Concat : public Term {
 public:
  Concat(TermList_ptr);
  Concat(const Concat&);
  virtual Concat_ptr clone() const override;
  virtual ~Concat();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class In : public Term {
 public:
  In(Term_ptr, Term_ptr);
  In(const In&);
  virtual In_ptr clone() const override;
  virtual ~In();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class NotIn : public Term {
 public:
  NotIn(Term_ptr, Term_ptr);
  NotIn(const NotIn&);
  virtual NotIn_ptr clone() const override;
  virtual ~NotIn();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr left_term;
  Term_ptr right_term;
};

class Len : public Term {
 public:
  Len(Term_ptr);
  Len(const Len&);
  virtual Len_ptr clone() const override;
  virtual ~Len();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class Contains : public Term {
 public:
  Contains(Term_ptr, Term_ptr);
  Contains(const Contains&);
  virtual Contains_ptr clone() const override;
  virtual ~Contains();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
};

class NotContains : public Term {
 public:
  NotContains(Term_ptr, Term_ptr);
  NotContains(const NotContains&);
  virtual NotContains_ptr clone() const override;
  virtual ~NotContains();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
};

class Begins : public Term {
 public:
  Begins(Term_ptr, Term_ptr);
  Begins(const Begins&);
  virtual Begins_ptr clone() const override;
  virtual ~Begins();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
};

class NotBegins : public Term {
 public:
  NotBegins(Term_ptr, Term_ptr);
  NotBegins(const NotBegins&);
  virtual NotBegins_ptr clone() const override;
  virtual ~NotBegins();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
};

class Ends : public Term {
 public:
  Ends(Term_ptr, Term_ptr);
  Ends(const Ends&);
  virtual Ends_ptr clone() const override;
  virtual ~Ends();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
};

class NotEnds : public Term {
 public:
  NotEnds(Term_ptr, Term_ptr);
  NotEnds(const NotEnds&);
  virtual NotEnds_ptr clone() const override;
  virtual ~NotEnds();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
};

class IndexOf : public Term {
 public:
  enum class Mode
    : int {
      NONE = 0,
    DEFAULT,  // from index is nullptr,
    FROMINDEX,          // from index is a numeral
    FROMFIRSTOF,        // from index is string term to find first occurance
    FROMLASTOF,         // from index is string term to find last occurance
  };
  IndexOf(Term_ptr, Term_ptr);
  IndexOf(Term_ptr, Term_ptr, Term_ptr, Mode mode = Mode::FROMINDEX);
  IndexOf(const IndexOf&);
  virtual IndexOf_ptr clone() const override;
  virtual ~IndexOf();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Mode getMode();
  void setMode(Mode mode);

  Term_ptr subject_term;
  Term_ptr search_term;
  Term_ptr from_index;
  Mode mode;
};

class LastIndexOf : public Term {
 public:
  enum class Mode
    : int {
      NONE = 0,
    DEFAULT,            // from index is nullptr,
    FROMINDEX,          // from index is a numeral
    FROMFIRSTOF,        // from index is string term to find first occurance
    FROMLASTOF,         // from index is string term to find last occurance
  };
  LastIndexOf(Term_ptr, Term_ptr);
  LastIndexOf(Term_ptr, Term_ptr, Term_ptr, Mode mode = Mode::FROMINDEX);
  LastIndexOf(const LastIndexOf&);
  virtual LastIndexOf_ptr clone() const override;
  virtual ~LastIndexOf();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Mode getMode();
  void setMode(Mode mode);

  Term_ptr subject_term;
  Term_ptr search_term;
  Term_ptr from_index;
  Mode mode;
};

class CharAt : public Term {
 public:
  CharAt(Term_ptr, Term_ptr);
  CharAt(const CharAt&);
  virtual CharAt_ptr clone() const override;
  virtual ~CharAt();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr index_term;
};

class SubString : public Term {
 public:
  enum class Mode
    : int {
      NONE = 0,            // used only to check for optimizations
    FROMINDEX,             // start index is a numeral
    FROMFIRSTOF,           // start index is string term to find first occurance
    FROMLASTOF,            // start index is string term to find last occurance
    FROMINDEXTOINDEX,      // start index is numeral, end index is numeral
    FROMINDEXTOFIRSTOF,    // start index is numeral, end index is string term to find first occurance
    FROMINDEXTOLASTOF,     // start index is numeral, end index is string term to find last occurance
    FROMFIRSTOFTOINDEX,    // start index is string term, end index is numeral
    FROMFIRSTOFTOFIRSTOF,  // start index is string term, end index is string term
    FROMFIRSTOFTOLASTOF,   // start index is string term, end index is string term
    FROMLASTOFTOINDEX,     // start index is string term, end index is numeral
    FROMLASTOFTOFIRSTOF,   // start index is string term, end index is string term
    FROMLASTOFTOLASTOF,    // start index is string term, end index is string term
    LASTINDEXLENGTH        // last index is the length of the substring, conversion required

  };
  SubString(Term_ptr, Term_ptr, Mode mode = Mode::FROMINDEX);
  SubString(Term_ptr, Term_ptr, Term_ptr, Mode mode = Mode::FROMINDEXTOINDEX);
  SubString(const SubString&);
  virtual SubString_ptr clone() const override;
  virtual ~SubString();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Mode getMode();
  void setMode(Mode mode);

  Term_ptr subject_term;
  Term_ptr start_index_term;
  Term_ptr end_index_term;
  Mode mode;
};

class ToUpper : public Term {
 public:
  ToUpper(Term_ptr);
  ToUpper(const ToUpper&);
  virtual ToUpper_ptr clone() const override;
  virtual ~ToUpper();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
};

class ToLower : public Term {
 public:
  ToLower(Term_ptr);
  ToLower(const ToLower&);
  virtual ToLower_ptr clone() const override;
  virtual ~ToLower();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
};

class Trim : public Term {
 public:
  Trim(Term_ptr);
  Trim(const Trim&);
  virtual Trim_ptr clone() const override;
  virtual ~Trim();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
};

class ToString : public Term {
 public:
  ToString(Term_ptr);
  ToString(const ToString&);
  virtual ToString_ptr clone() const override;
  virtual ~ToString();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
};

class ToInt : public Term {
 public:
  ToInt(Term_ptr);
  ToInt(const ToInt&);
  virtual ToInt_ptr clone() const override;
  virtual ~ToInt();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
};

class Replace : public Term {
 public:
  Replace(Term_ptr, Term_ptr, Term_ptr);
  Replace(const Replace&);
  virtual Replace_ptr clone() const override;
  virtual ~Replace();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr search_term;
  Term_ptr replace_term;
};

class Count : public Term {
 public:
  Count(Term_ptr, Term_ptr);
  Count(const Count&);
  virtual Count_ptr clone() const override;
  virtual ~Count();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr subject_term;
  Term_ptr bound_term;
};

class Ite : public Term {
 public:
  Ite(Term_ptr, Term_ptr, Term_ptr);
  Ite(const Ite&);
  virtual Ite_ptr clone() const override;
  virtual ~Ite();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr cond;
  Term_ptr then_branch;
  Term_ptr else_branch;
};

class ReConcat : public Term {
 public:
  ReConcat(TermList_ptr);
  ReConcat(const ReConcat&);
  virtual ReConcat_ptr clone() const override;
  virtual ~ReConcat();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
  // ToRegex specifically
};

class ReUnion : public Term {
 public:
  ReUnion(TermList_ptr);
  ReUnion(const ReUnion&);
  virtual ReUnion_ptr clone() const override;
  virtual ~ReUnion();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class ReInter : public Term {
 public:
  ReInter(TermList_ptr);
  ReInter(const ReInter&);
  virtual ReInter_ptr clone() const override;
  virtual ~ReInter();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  TermList_ptr term_list;
};

class ReStar : public Term {
 public:
  ReStar(Term_ptr);
  ReStar(const ReStar&);
  virtual ReStar_ptr clone() const override;
  virtual ~ReStar();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class RePlus : public Term {
 public:
  RePlus(Term_ptr);
  RePlus(const RePlus&);
  virtual RePlus_ptr clone() const override;
  virtual ~RePlus();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class ReOpt : public Term {
 public:
  ReOpt(Term_ptr);
  ReOpt(const ReOpt&);
  virtual ReOpt_ptr clone() const override;
  virtual ~ReOpt();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class ToRegex : public Term {
 public:
  ToRegex(Term_ptr);
  ToRegex(const ToRegex&);
  virtual ToRegex_ptr clone() const override;
  virtual ~ToRegex();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
};

class UnknownTerm : public Term {
 public:
  UnknownTerm(Term_ptr, TermList_ptr);
  UnknownTerm(const UnknownTerm&);
  virtual UnknownTerm* clone() const override;
  virtual ~UnknownTerm();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Term_ptr term;
  TermList_ptr term_list;
};

/**
 * "(" "as" identifier sort ")"
 * | identifier
 */
class QualIdentifier : public Term {
 public:
  QualIdentifier(Identifier_ptr);
  QualIdentifier(const QualIdentifier&);
  virtual QualIdentifier_ptr clone() const override;
  virtual ~QualIdentifier();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  std::string getVarName();

  Identifier_ptr identifier;

};

class AsQualIdentifier : public Term {
 public:
  AsQualIdentifier(Identifier_ptr, Sort_ptr);
  AsQualIdentifier(const AsQualIdentifier&);
  virtual AsQualIdentifier_ptr clone() const override;
  virtual ~AsQualIdentifier();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Identifier_ptr identifier;
  Sort_ptr sort;
};

class Primitive : public Visitable {
 public:
  enum class Type
    : int {
      NONE = 0,
    BOOL,
    BINARY,
    DECIMAL,
    HEXADECIMAL,
    KEYWORD,
    NUMERAL,
    STRING,
    REGEX,
    SYMBOL
  };

  Primitive(const std::string data, const Primitive::Type type);
  Primitive(const Primitive&);
  virtual Primitive_ptr clone() const;
  virtual ~Primitive();
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;
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

class TermConstant : public Term {
 public:
  TermConstant(Primitive_ptr);
  TermConstant(const TermConstant&);
  virtual TermConstant_ptr clone() const override;
  virtual ~TermConstant();

  virtual std::string str() const override;
  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  std::string getValue() const;
  Primitive::Type getValueType() const;

  Primitive_ptr primitive;
};

/**
 *  : "(" identifier sort_list_ ")"
 *  | identifier
 *  | type
 */
class Sort : public Visitable {
 public:
  Sort(Identifier_ptr);
  Sort(Identifier_ptr, SortList_ptr);
  Sort(TVariable_ptr);
  Sort(const Sort&);
  virtual Sort_ptr clone() const;
  virtual ~Sort();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Identifier_ptr identifier;
  SortList_ptr sort_list;
  TVariable_ptr var_type;

};

class TVariable : public Visitable {
 public:
  enum class Type
    : int {
      NONE = 0,
    BOOL,
    INT,
    STRING
  };

  TVariable(TVariable::Type type);
  TVariable(const TVariable&);
  virtual TVariable_ptr clone() const;
  virtual ~TVariable();

  virtual std::string str() const;
  virtual TVariable::Type getType() const;

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  friend std::ostream& operator<<(std::ostream& os, const TVariable& t_variable);
 protected:
  const TVariable::Type type;
};

class TBool : public TVariable {
 public:
  TBool();
  TBool(const TBool&);
  virtual TBool_ptr clone() const override;
  virtual ~TBool();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;
};

class TInt : public TVariable {
 public:
  TInt();
  TInt(const TInt&);
  virtual TInt_ptr clone() const override;
  virtual ~TInt();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

};

class TString : public TVariable {
 public:
  TString();
  TString(const TString&);
  virtual TString_ptr clone() const override;
  virtual ~TString();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;
};

/**
 * : KEYWORD attribute_value
 * | KEYWORD
 */
class Attribute : public Visitable {
 public:
  Attribute();
  Attribute(const Attribute&);
  virtual Attribute_ptr clone() const;
  virtual ~Attribute();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

};

/**
 * "(" SYMBOL sort ")"
 */
class SortedVar : public Visitable {
 public:
  SortedVar(Primitive_ptr, Sort_ptr);
  SortedVar(const SortedVar&);
  virtual SortedVar_ptr clone() const;
  virtual ~SortedVar();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Primitive_ptr symbol;
  Sort_ptr sort;
};

/**
 * "(" SYMBOL term ")"
 */
class VarBinding : public Visitable {
 public:
  VarBinding(Primitive_ptr, Term_ptr);
  VarBinding(const VarBinding&);
  virtual VarBinding_ptr clone() const;
  virtual ~VarBinding();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  Primitive_ptr symbol;
  Term_ptr term;
};

/**
 *  "(" "_" SYMBOL numeral_list_ ")"
 * | SYMBOL
 */
class Identifier : public Visitable {
 public:
  Identifier(Primitive_ptr);
  Identifier(Primitive_ptr, Primitive_ptr, NumeralList_ptr);
  Identifier(const Identifier&);
  virtual Identifier_ptr clone() const;
  virtual ~Identifier();

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  std::string getName();
  Primitive::Type getType();

  Primitive_ptr underscore;
  Primitive_ptr symbol;
  NumeralList_ptr numeral_list;
};

class Variable : public TVariable {
 public:
  Variable(std::string name, Type);
  Variable(Primitive_ptr, Type);
  Variable(std::string name, Type, bool is_symbolic);
  Variable(Primitive_ptr, Type, bool is_symbolic);
  Variable(const Variable&);
  virtual Variable_ptr clone() const override;
  virtual ~Variable();

  virtual std::string str() const override;

  std::string getName() const;
  Variable::Type getType() const;

  bool isSymbolic() const;
  void setSymbolic(bool is_symbolic);
  bool isLocalLetVar() const;
  void setLocalLetVar(bool is_local_let_var);
  void set_group_var(bool is_group_var);

  virtual void accept(Visitor_ptr) override;
  virtual void visit_children(Visitor_ptr) override;

  static const std::string SYMBOLIC_VAR_PREFIX;
  static const std::string LOCAL_VAR_PREFIX;
 protected:
  std::string name;
  bool is_symbolic;
  bool is_local_let_var;
};

/**
 * HELPER FUNCTIONS
 *
 * Syntactic transformations can be made available to parser, in that case we will not be able to
 * see original parsed tree
 */

TermConstant_ptr ReRangeToRegex(Term_ptr left, Term_ptr right);
SMT::Or_ptr TransformIteToOr(SMT::Term_ptr ite_condition, SMT::Term_ptr ite_then_branch, SMT::Term_ptr ite_else_branch);
TermList_ptr CreateTermList(int, ...);

} /* namespace SMT */
} /* namespace Vlab */

#endif /* SMT_AST_H_ */
