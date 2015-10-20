/*
 * ast.cpp
 *
 *  Created on: Nov 21, 2014
 *      Author: baki
 */

#include "ast.h"

namespace Vlab {
namespace SMT {

Script::Script(CommandList_ptr commands)
        : command_list(commands) {
}

Script::Script(const Script& other) {
  command_list = new CommandList();
  for (auto& cmd : *(other.command_list)) {
    command_list->push_back(cmd->clone());
  }
}
Script_ptr Script::clone() const {
  return new Script(*this);
}
Script::~Script() {
  DVLOG(AST_VLOG_LEVEL) << "Script deallocated.";
  deallocate_list(command_list);
  delete command_list;
}

void Script::accept(Visitor_ptr v) {
  v->visitScript(this);
}

void Script::visit_children(Visitor_ptr v) {
  v->visit_list(command_list);
}

const std::string Command::Name::NONE = "none";
const std::string Command::Name::SET_LOGIC = "set-logic";
const std::string Command::Name::SET_OPTION = "set-option";
const std::string Command::Name::SET_INFO = "set-info";
const std::string Command::Name::DECLARE_SORT = "declare-sort";
const std::string Command::Name::DEFINE_SORT = "define-sort";
const std::string Command::Name::DECLARE_FUN = "declare-fun";
const std::string Command::Name::DEFINE_FUN = "define-fun";
const std::string Command::Name::PUSH = "push";
const std::string Command::Name::POP = "pop";
const std::string Command::Name::ASSERT = "assert";
const std::string Command::Name::CHECK_SAT = "check-sat";
const std::string Command::Name::CHECK_SAT_AND_COUNT = "check-sat-and-count";
const std::string Command::Name::GET_ASSERTIONS = "get-assertions";
const std::string Command::Name::GET_PROOF = "get-proof";
const std::string Command::Name::GET_UNSAT_CORE = "get-unsat-core";
const std::string Command::Name::GET_VALUE = "get-value";
const std::string Command::Name::GET_ASSIGNMENT = "get-assignment";
const std::string Command::Name::GET_OPTION = "get-option";
const std::string Command::Name::GET_INFO = "get-info";
const std::string Command::Name::EXIT = "exit";

Command::Command()
        : type(Command::Type::NONE) {
}
Command::Command(Command::Type type)
        : type(type) {
}
Command::Command(const Command& other)
        : type(other.type) {
}
Command_ptr Command::clone() const {
  return new Command(*this);
}
Command::~Command() {
  DVLOG(AST_VLOG_LEVEL) << "Command( " << *this << " ) deallocated.";
}
std::string Command::str() const {
  switch (type) {
  case Command::Type::NONE:
    return Command::Name::NONE;
  case Command::Type::SET_LOGIC:
    return Command::Name::SET_LOGIC;
  case Command::Type::SET_OPTION:
    return Command::Name::SET_OPTION;
  case Command::Type::SET_INFO:
    return Command::Name::SET_INFO;
  case Command::Type::DECLARE_SORT:
    return Command::Name::DECLARE_SORT;
  case Command::Type::DEFINE_SORT:
    return Command::Name::DEFINE_SORT;
  case Command::Type::DECLARE_FUN:
    return Command::Name::DECLARE_FUN;
  case Command::Type::DEFINE_FUN:
    return Command::Name::DEFINE_FUN;
  case Command::Type::PUSH:
    return Command::Name::PUSH;
  case Command::Type::POP:
    return Command::Name::POP;
  case Command::Type::ASSERT:
    return Command::Name::ASSERT;
  case Command::Type::CHECK_SAT:
    return Command::Name::CHECK_SAT;
  case Command::Type::CHECK_SAT_AND_COUNT:
    return Command::Name::CHECK_SAT_AND_COUNT;
  case Command::Type::GET_ASSERTIONS:
    return Command::Name::GET_ASSERTIONS;
  case Command::Type::GET_PROOF:
    return Command::Name::GET_PROOF;
  case Command::Type::GET_UNSAT_CORE:
    return Command::Name::GET_UNSAT_CORE;
  case Command::Type::GET_VALUE:
    return Command::Name::GET_VALUE;
  case Command::Type::GET_ASSIGNMENT:
    return Command::Name::GET_ASSIGNMENT;
  case Command::Type::GET_OPTION:
    return Command::Name::GET_OPTION;
  case Command::Type::GET_INFO:
    return Command::Name::GET_INFO;
  case Command::Type::EXIT:
    return Command::Name::EXIT;
  default:
    LOG(FATAL)<< "Unknown command!";
    return "";
  }
}
Command::Type Command::getType() const {
  return type;
}
void Command::accept(Visitor_ptr v) {
  v->visitCommand(this);
}
void Command::visit_children(Visitor_ptr v) {
}

std::ostream& operator<<(std::ostream& os, const Command& command) {
  return os << command.str();
}

SetLogic::SetLogic(Primitive_ptr symbol)
        : Command(Command::Type::SET_LOGIC), symbol(symbol) {
}
SetLogic::SetLogic(const SetLogic& other)
        : Command(other.type) {
  symbol = other.symbol->clone();
}
SetLogic* SetLogic::clone() const {
  return new SetLogic(*this);
}
SetLogic::~SetLogic() {
  delete symbol;
}

void SetLogic::visit_children(Visitor_ptr v) {
  v->visit(symbol);
}

DeclareFun::DeclareFun(Primitive_ptr symbol, SortList_ptr sort_list, Sort_ptr sort)
        : Command(Command::Type::DECLARE_FUN), symbol(symbol), sort_list(sort_list), sort(sort) {
}
DeclareFun::DeclareFun(const DeclareFun& other)
        : Command(other.type) {
  symbol = other.symbol->clone();
  if (other.sort_list == nullptr) {
    sort_list = nullptr;
  } else {
    sort_list = new SortList();
    for (auto& el : *(other.sort_list)) {
      sort_list->push_back(el->clone());
    }
  }
  sort = other.sort->clone();
}
DeclareFun* DeclareFun::clone() const {
  return new DeclareFun(*this);
}
DeclareFun::~DeclareFun() {
  delete symbol;
  deallocate_list(sort_list);
  delete sort_list;
  delete sort;
}
void DeclareFun::visit_children(Visitor_ptr v) {
  v->visit(symbol);
  v->visit_list(sort_list);
  v->visit(sort);
}

Assert::Assert(Term_ptr term)
        : Command(Command::Type::ASSERT), term(term) {
}
Assert::Assert(const Assert& other)
        : Command(other.type) {
  term = other.term->clone();
}
Assert_ptr Assert::clone() const {
  return new Assert(*this);
}
Assert::~Assert() {
  delete term;
}

void Assert::accept(Visitor_ptr v) {
  v->visitAssert(this);
}

void Assert::visit_children(Visitor_ptr v) {
  v->visit(term);
}

CheckSat::CheckSat()
        : Command(Command::Type::CHECK_SAT), symbol(nullptr) {
}
CheckSat::CheckSat(Primitive_ptr symbol)
        : Command(Command::Type::CHECK_SAT), symbol(symbol) {
}
CheckSat::CheckSat(const CheckSat& other)
        : Command(other.type) {
  symbol = (other.symbol == nullptr) ? other.symbol : other.symbol->clone();
}
CheckSat* CheckSat::clone() const {
  return new CheckSat(*this);
}
CheckSat::~CheckSat() {
  delete symbol;
}

void CheckSat::visit_children(Visitor_ptr v) {
  v->visit(symbol);
}

CheckSatAndCount::CheckSatAndCount(Primitive_ptr bound)
        : Command(Command::Type::CHECK_SAT_AND_COUNT), bound(bound), symbol(nullptr) {
}

CheckSatAndCount::CheckSatAndCount(Primitive_ptr bound, Primitive_ptr symbol)
        : Command(Command::Type::CHECK_SAT_AND_COUNT), bound(bound), symbol(symbol) {
}

CheckSatAndCount::CheckSatAndCount(const CheckSatAndCount& other)
        : Command(other.type) {
  bound = other.bound->clone();
  symbol = (other.symbol == nullptr) ? other.symbol : other.symbol->clone();
}

CheckSatAndCount* CheckSatAndCount::clone() const {
  return new CheckSatAndCount(*this);
}

CheckSatAndCount::~CheckSatAndCount() {
  delete bound;
  delete symbol;
}

void CheckSatAndCount::visit_children(Visitor_ptr v) {
  v->visit(bound);
  v->visit(symbol);
}

/* ends commands */

/* Terms */

const std::string Term::Name::NONE = "none";
const std::string Term::Name::EXCLAMATION = "!";
const std::string Term::Name::EXISTS = "exists";
const std::string Term::Name::FORALL = "forall";
const std::string Term::Name::LET = "let";
const std::string Term::Name::TERM = "term";
const std::string Term::Name::AND = "and";
const std::string Term::Name::OR = "or";
const std::string Term::Name::NOT = "not";
const std::string Term::Name::UMINUS = "uminus";
const std::string Term::Name::MINUS = "-";
const std::string Term::Name::PLUS = "+";
const std::string Term::Name::TIMES = "*";
const std::string Term::Name::EQ = "=";
const std::string Term::Name::NOTEQ = "!=";
const std::string Term::Name::GT = ">";
const std::string Term::Name::GE = ">=";
const std::string Term::Name::LT = "<";
const std::string Term::Name::LE = "<=";
const std::string Term::Name::CONCAT = "concat";
const std::string Term::Name::IN = "in";
const std::string Term::Name::NOTIN = "notIn";
const std::string Term::Name::LEN = "len";
const std::string Term::Name::CONTAINS = "contains";
const std::string Term::Name::NOTCONTAINS = "notContains";
const std::string Term::Name::BEGINS = "begins";
const std::string Term::Name::NOTBEGINS = "notBegins";
const std::string Term::Name::ENDS = "ends";
const std::string Term::Name::NOTENDS = "notEnds";
const std::string Term::Name::INDEXOF = "indexOf";
const std::string Term::Name::LASTINDEXOF= "lastIndexOf";
const std::string Term::Name::CHARAT = "charAt";
const std::string Term::Name::SUBSTRING = "subString";
const std::string Term::Name::SUBSTRINGFIRSTOF = "subStringFirstOf";
const std::string Term::Name::SUBSTRINGLASTOF = "subStringLastOf";
const std::string Term::Name::TOUPPER = "toUpper";
const std::string Term::Name::TOLOWER = "toLower";
const std::string Term::Name::TRIM = "trim";
const std::string Term::Name::REPLACE = "replace";
const std::string Term::Name::COUNT = "count";
const std::string Term::Name::ITE = "ite";
const std::string Term::Name::RECONCAT = "re.++";
const std::string Term::Name::TOREGEX = "str.to.re";
const std::string Term::Name::ASQUALIDENTIFIER = "as";
const std::string Term::Name::QUALIDENTIFIER = "qual identifier";
const std::string Term::Name::TERMCONSTANT = "term constant";
const std::string Term::Name::UNKNOWN = "unknown";

Term::Term()
        : type(Term::Type::TERM) {
}
Term::Term(Term::Type type)
        : type(type) {
}
Term::Term(const Term& other)
        : type(other.type) {
}
Term_ptr Term::clone() const {
  return new Term(*this);
}
Term::~Term() {
  DVLOG(AST_VLOG_LEVEL) << "Term( " << this->str() << " ) deallocated.";
}

std::string Term::str() const {
  switch (type) {
  case Term::Type::NONE:
    return Term::Name::NONE;
  case Term::Type::EXCLAMATION:
    return Term::Name::EXCLAMATION;
  case Term::Type::EXISTS:
    return Term::Name::EXISTS;
  case Term::Type::FORALL:
    return Term::Name::FORALL;
  case Term::Type::LET:
    return Term::Name::LET;
  case Term::Type::TERM:
    return Term::Name::TERM;
  case Term::Type::AND:
    return Term::Name::AND;
  case Term::Type::OR:
    return Term::Name::OR;
  case Term::Type::NOT:
    return Term::Name::NOT;
  case Term::Type::UMINUS:
    return Term::Name::UMINUS;
  case Term::Type::MINUS:
    return Term::Name::MINUS;
  case Term::Type::PLUS:
    return Term::Name::PLUS;
  case Term::Type::TIMES:
    return Term::Name::TIMES;
  case Term::Type::EQ:
    return Term::Name::EQ;
  case Term::Type::NOTEQ:
    return Term::Name::NOTEQ;
  case Term::Type::GT:
    return Term::Name::GT;
  case Term::Type::GE:
    return Term::Name::GE;
  case Term::Type::LT:
    return Term::Name::LT;
  case Term::Type::LE:
    return Term::Name::LE;
  case Term::Type::CONCAT:
    return Term::Name::CONCAT;
  case Term::Type::IN:
    return Term::Name::IN;
  case Term::Type::NOTIN:
    return Term::Name::NOTIN;
  case Term::Type::LEN:
    return Term::Name::LEN;
  case Term::Type::CONTAINS:
    return Term::Name::CONTAINS;
  case Term::Type::NOTCONTAINS:
    return Term::Name::NOTCONTAINS;
  case Term::Type::BEGINS:
    return Term::Name::BEGINS;
  case Term::Type::NOTBEGINS:
    return Term::Name::NOTBEGINS;
  case Term::Type::ENDS:
    return Term::Name::ENDS;
  case Term::Type::NOTENDS:
    return Term::Name::NOTENDS;
  case Term::Type::INDEXOF:
    return Term::Name::INDEXOF;
  case Term::Type::LASTINDEXOF:
    return Term::Name::LASTINDEXOF;
  case Term::Type::CHARAT:
    return Term::Name::CHARAT;
  case Term::Type::SUBSTRING:
    return Term::Name::SUBSTRING;
  case Term::Type::SUBSTRINGFIRSTOF:
    return Term::Name::SUBSTRINGFIRSTOF;
  case Term::Type::SUBSTRINGLASTOF:
    return Term::Name::SUBSTRINGLASTOF;
  case Term::Type::TOUPPER:
    return Term::Name::TOUPPER;
  case Term::Type::TOLOWER:
    return Term::Name::TOLOWER;
  case Term::Type::TRIM:
    return Term::Name::TRIM;
  case Term::Type::REPLACE:
    return Term::Name::REPLACE;
  case Term::Type::COUNT:
    return Term::Name::COUNT;
  case Term::Type::ITE:
    return Term::Name::ITE;
  case Term::Type::RECONCAT:
    return Term::Name::RECONCAT;
  case Term::Type::TOREGEX:
    return Term::Name::TOREGEX;
  case Term::Type::ASQUALIDENTIFIER:
    return Term::Name::ASQUALIDENTIFIER;
  case Term::Type::QUALIDENTIFIER:
    return Term::Name::QUALIDENTIFIER;
  case Term::Type::TERMCONSTANT:
    return Term::Name::TERMCONSTANT;
  case Term::Type::UNKNOWN:
    return Term::Name::UNKNOWN;
  default:
    LOG(FATAL)<< "Unknown term!";
    return "";
  }
}

void Term::accept(Visitor_ptr v) {
  v->visitTerm(this);
}
void Term::visit_children(Visitor_ptr v) {
  LOG(FATAL)<< "Unhandled term production rule!";
}

Term::Type Term::getType() const {
  return type;
}

std::ostream& operator<<(std::ostream& os, const Term& term) {
  return os << term.str();
}

//std::ostream& operator<<(std::ostream& os, const Term_ptr& term) {
//	return os << term->str();
//}

Exclamation::Exclamation(Term_ptr term, AttributeList_ptr attribute_list)
        : Term(Term::Type::EXCLAMATION), term(term), attribute_list(attribute_list) {
}

Exclamation::Exclamation(const Exclamation& other)
        : Term(other.type) {
  term = other.term->clone();
  attribute_list = new AttributeList();
  for (auto& attribute : *(other.attribute_list)) {
    attribute_list->push_back(attribute->clone());
  }
}

Exclamation_ptr Exclamation::clone() const {
  return new Exclamation(*this);
}

Exclamation::~Exclamation() {
  delete term;
  deallocate_list(attribute_list);
  delete attribute_list;
}

void Exclamation::accept(Visitor_ptr v) {
  v->visitExclamation(this);
}

void Exclamation::visit_children(Visitor_ptr v) {
  v->visit(term);
  v->visit_list(attribute_list);
}

Exists::Exists(SortedVarList_ptr sorted_var_list, Term_ptr term)
        : Term(Term::Type::EXISTS), sorted_var_list(sorted_var_list), term(term) {
}

Exists::Exists(const Exists& other)
        : Term(other.type) {
  sorted_var_list = new SortedVarList();
  for (auto& sorted_var : *(other.sorted_var_list)) {
    sorted_var_list->push_back(sorted_var->clone());
  }
  term = other.term->clone();
}

Exists_ptr Exists::clone() const {
  return new Exists(*this);
}

Exists::~Exists() {
  deallocate_list(sorted_var_list);
  delete sorted_var_list;
  delete term;
}

void Exists::accept(Visitor_ptr v) {
  v->visitExists(this);
}

void Exists::visit_children(Visitor_ptr v) {
  v->visit_list(sorted_var_list);
  v->visit(term);
}

ForAll::ForAll(SortedVarList_ptr sorted_var_list, Term_ptr term)
        : Term(Term::Type::FORALL), sorted_var_list(sorted_var_list), term(term) {
}

ForAll::ForAll(const ForAll& other)
        : Term(other.type) {
  sorted_var_list = new SortedVarList();
  for (auto& sorted_var : *(other.sorted_var_list)) {
    sorted_var_list->push_back(sorted_var->clone());
  }
  term = other.term->clone();
}

ForAll_ptr ForAll::clone() const {
  return new ForAll(*this);
}

ForAll::~ForAll() {
  deallocate_list(sorted_var_list);
  delete sorted_var_list;
  delete term;
}

void ForAll::accept(Visitor_ptr v) {
  v->visitForAll(this);
}

void ForAll::visit_children(Visitor_ptr v) {
  v->visit_list(sorted_var_list);
  v->visit(term);
}

Let::Let(VarBindingList_ptr var_binding_list, Term_ptr term)
        : Term(Term::Type::LET), var_binding_list(var_binding_list), term(term) {
}

Let::Let(const Let& other)
        : Term(other.type) {
  var_binding_list = new VarBindingList();
  for (auto& var_binding : *(other.var_binding_list)) {
    var_binding_list->push_back(var_binding->clone());
  }
  term = other.term->clone();
}

Let_ptr Let::clone() const {
  return new Let(*this);
}

Let::~Let() {
  deallocate_list(var_binding_list);
  delete var_binding_list;
  delete term;
}

void Let::accept(Visitor_ptr v) {
  v->visitLet(this);
}

void Let::visit_children(Visitor_ptr v) {
  v->visit_list(var_binding_list);
  v->visit(term);
}

And::And(TermList_ptr term_list)
        : Term(Term::Type::AND), term_list(term_list) {
}
And::And(const And& other)
        : Term(other.type) {
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
And_ptr And::clone() const {
  return new And(*this);
}
And::~And() {
  deallocate_list(term_list);
  delete term_list;
}

void And::accept(Visitor_ptr v) {
  v->visitAnd(this);
}
void And::visit_children(Visitor_ptr v) {
  v->visit_list(term_list);
}

Or::Or(TermList_ptr term_list)
        : Term(Term::Type::OR), term_list(term_list) {
}
Or::Or(const Or& other)
        : Term(other.type) {
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
Or_ptr Or::clone() const {
  return new Or(*this);
}
Or::~Or() {
  deallocate_list(term_list);
  delete term_list;
}

void Or::accept(Visitor_ptr v) {
  v->visitOr(this);
}
void Or::visit_children(Visitor_ptr v) {
  v->visit_list(term_list);
}

Not::Not(Term_ptr term)
        : Term(Term::Type::NOT), term(term) {
}
Not::Not(const Not& other)
        : Term(other.type) {
  term = other.term->clone();
}
Not_ptr Not::clone() const {
  return new Not(*this);
}
Not::~Not() {
  delete term;
}

void Not::accept(Visitor_ptr v) {
  v->visitNot(this);
}
void Not::visit_children(Visitor_ptr v) {
  v->visit(term);
}

UMinus::UMinus(Term_ptr term)
        : Term(Term::Type::UMINUS), term(term) {
}
UMinus::UMinus(const UMinus& other)
        : Term(other.type) {
  term = other.term->clone();
}
UMinus_ptr UMinus::clone() const {
  return new UMinus(*this);
}
UMinus::~UMinus() {
  delete term;
}

void UMinus::accept(Visitor_ptr v) {
  v->visitUMinus(this);
}
void UMinus::visit_children(Visitor_ptr v) {
  v->visit(term);
}

Minus::Minus(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::MINUS), left_term(left_term), right_term(right_term) {
}
Minus::Minus(const Minus& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
Minus_ptr Minus::clone() const {
  return new Minus(*this);
}
Minus::~Minus() {
  delete left_term;
  delete right_term;
}

void Minus::accept(Visitor_ptr v) {
  v->visitMinus(this);
}
void Minus::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Plus::Plus(TermList_ptr term_list)
        : Term(Term::Type::PLUS), term_list(term_list) {
}
Plus::Plus(const Plus& other)
        : Term(other.type) {
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
Plus_ptr Plus::clone() const {
  return new Plus(*this);
}
Plus::~Plus() {
  deallocate_list(term_list);
  delete term_list;
}

void Plus::accept(Visitor_ptr v) {
  v->visitPlus(this);
}
void Plus::visit_children(Visitor_ptr v) {
  v->visit_list(term_list);
}

Times::Times(TermList_ptr term_list)
        : Term(Term::Type::TIMES), term_list(term_list) {
}
Times::Times(const Times& other)
        : Term(other.type) {
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
Times_ptr Times::clone() const {
  return new Times(*this);
}
Times::~Times() {
  deallocate_list(term_list);
  delete term_list;
}

void Times::accept(Visitor_ptr v) {
  v->visitTimes(this);
}
void Times::visit_children(Visitor_ptr v) {
  v->visit_list(term_list);
}

Eq::Eq(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::EQ), left_term(left_term), right_term(right_term) {
}
Eq::Eq(const Eq& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
Eq_ptr Eq::clone() const {
  return new Eq(*this);
}
Eq::~Eq() {
  delete left_term;
  delete right_term;
}

void Eq::accept(Visitor_ptr v) {
  v->visitEq(this);
}
void Eq::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

NotEq::NotEq(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::NOTEQ), left_term(left_term), right_term(right_term) {
}
NotEq::NotEq(const NotEq& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
NotEq_ptr NotEq::clone() const {
  return new NotEq(*this);
}
NotEq::~NotEq() {
  delete left_term;
  delete right_term;
}

void NotEq::accept(Visitor_ptr v) {
  v->visitNotEq(this);
}
void NotEq::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Gt::Gt(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::GT), left_term(left_term), right_term(right_term) {
}
Gt::Gt(const Gt& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}

Gt_ptr Gt::clone() const {
  return new Gt(*this);
}
Gt::~Gt() {
  delete left_term, delete right_term;
}

void Gt::accept(Visitor_ptr v) {
  v->visitGt(this);
}
void Gt::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Ge::Ge(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::GE), left_term(left_term), right_term(right_term) {
}
Ge::Ge(const Ge& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
Ge_ptr Ge::clone() const {
  return new Ge(*this);
}
Ge::~Ge() {
  delete left_term, delete right_term;
}

void Ge::accept(Visitor_ptr v) {
  v->visitGe(this);
}
void Ge::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Lt::Lt(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::LT), left_term(left_term), right_term(right_term) {
}
Lt::Lt(const Lt& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
Lt_ptr Lt::clone() const {
  return new Lt(*this);
}
Lt::~Lt() {
  delete left_term, delete right_term;
}

void Lt::accept(Visitor_ptr v) {
  v->visitLt(this);
}
void Lt::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Le::Le(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::LE), left_term(left_term), right_term(right_term) {
}
Le::Le(const Le& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
Le_ptr Le::clone() const {
  return new Le(*this);
}
Le::~Le() {
  delete left_term, delete right_term;
}

void Le::accept(Visitor_ptr v) {
  v->visitLe(this);
}
void Le::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Concat::Concat(TermList_ptr term_list)
        : Term(Term::Type::CONCAT), term_list(term_list) {
}
Concat::Concat(const Concat& other)
        : Term(other.type) {
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
Concat_ptr Concat::clone() const {
  return new Concat(*this);
}
Concat::~Concat() {
  deallocate_list(term_list);
  delete term_list;
}

void Concat::accept(Visitor_ptr v) {
  v->visitConcat(this);
}
void Concat::visit_children(Visitor_ptr v) {
  v->visit_list(term_list);
}

In::In(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::IN), left_term(left_term), right_term(right_term) {
}
In::In(const In& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
In_ptr In::clone() const {
  return new In(*this);
}
In::~In() {
  delete left_term, delete right_term;
}

void In::accept(Visitor_ptr v) {
  v->visitIn(this);
}
void In::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

NotIn::NotIn(Term_ptr left_term, Term_ptr right_term)
        : Term(Term::Type::NOTIN), left_term(left_term), right_term(right_term) {
}
NotIn::NotIn(const NotIn& other)
        : Term(other.type) {
  left_term = other.left_term->clone();
  right_term = other.right_term->clone();
}
NotIn_ptr NotIn::clone() const {
  return new NotIn(*this);
}
NotIn::~NotIn() {
  delete left_term, delete right_term;
}

void NotIn::accept(Visitor_ptr v) {
  v->visitNotIn(this);
}
void NotIn::visit_children(Visitor_ptr v) {
  v->visit(left_term);
  v->visit(right_term);
}

Len::Len(Term_ptr term)
        : Term(Term::Type::LEN), term(term) {
}
Len::Len(const Len& other)
        : Term(other.type) {
  term = other.term->clone();
}
Len_ptr Len::clone() const {
  return new Len(*this);
}
Len::~Len() {
  delete term;
}

void Len::accept(Visitor_ptr v) {
  v->visitLen(this);
}
void Len::visit_children(Visitor_ptr v) {
  v->visit(term);
}

Contains::Contains(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::CONTAINS), subject_term(subject_term), search_term(search_term) {
}

Contains::Contains(const Contains& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}

Contains_ptr Contains::clone() const {
  return new Contains(*this);
}

Contains::~Contains() {
  delete subject_term;
  delete search_term;
}

void Contains::accept(Visitor_ptr v) {
  v->visitContains(this);
}

void Contains::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

NotContains::NotContains(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::NOTCONTAINS), subject_term(subject_term), search_term(search_term) {
}

NotContains::NotContains(const NotContains& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}

NotContains_ptr NotContains::clone() const {
  return new NotContains(*this);
}

NotContains::~NotContains() {
  delete subject_term;
  delete search_term;
}

void NotContains::accept(Visitor_ptr v) {
  v->visitNotContains(this);
}

void NotContains::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

Begins::Begins(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::BEGINS), subject_term(subject_term), search_term(search_term) {
}

Begins::Begins(const Begins& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}
Begins_ptr Begins::clone() const {
  return new Begins(*this);
}

Begins::~Begins() {
  delete subject_term;
  delete search_term;
}

void Begins::accept(Visitor_ptr v) {
  v->visitBegins(this);
}

void Begins::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

NotBegins::NotBegins(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::NOTBEGINS), subject_term(subject_term), search_term(search_term) {
}

NotBegins::NotBegins(const NotBegins& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}
NotBegins_ptr NotBegins::clone() const {
  return new NotBegins(*this);
}

NotBegins::~NotBegins() {
  delete subject_term;
  delete search_term;
}

void NotBegins::accept(Visitor_ptr v) {
  v->visitNotBegins(this);
}

void NotBegins::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

Ends::Ends(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::ENDS), subject_term(subject_term), search_term(search_term) {
}

Ends::Ends(const Ends& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}

Ends_ptr Ends::clone() const {
  return new Ends(*this);
}

Ends::~Ends() {
  delete subject_term;
  delete search_term;
}

void Ends::accept(Visitor_ptr v) {
  v->visitEnds(this);
}

void Ends::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

NotEnds::NotEnds(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::NOTENDS), subject_term(subject_term), search_term(search_term) {
}

NotEnds::NotEnds(const NotEnds& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}

NotEnds_ptr NotEnds::clone() const {
  return new NotEnds(*this);
}

NotEnds::~NotEnds() {
  delete subject_term;
  delete search_term;
}

void NotEnds::accept(Visitor_ptr v) {
  v->visitNotEnds(this);
}

void NotEnds::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

IndexOf::IndexOf(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::INDEXOF), subject_term(subject_term), search_term(search_term) {
}

IndexOf::IndexOf(const IndexOf& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}

IndexOf_ptr IndexOf::clone() const {
  return new IndexOf(*this);
}

IndexOf::~IndexOf() {
  delete subject_term;
  delete search_term;
}

void IndexOf::accept(Visitor_ptr v) {
  v->visitIndexOf(this);
}

void IndexOf::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

LastIndexOf::LastIndexOf(Term_ptr subject_term, Term_ptr search_term)
        : Term(Term::Type::LASTINDEXOF), subject_term(subject_term), search_term(search_term) {
}

LastIndexOf::LastIndexOf(const LastIndexOf& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
}

LastIndexOf_ptr LastIndexOf::clone() const {
  return new LastIndexOf(*this);
}

LastIndexOf::~LastIndexOf() {
  delete subject_term;
  delete search_term;
}

void LastIndexOf::accept(Visitor_ptr v) {
  v->visitLastIndexOf(this);
}

void LastIndexOf::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
}

CharAt::CharAt(Term_ptr subject_term, Term_ptr index_term)
        : Term(Term::Type::CHARAT), subject_term(subject_term), index_term(index_term) {
}

CharAt::CharAt(const CharAt& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  index_term = other.index_term->clone();
}

CharAt_ptr CharAt::clone() const {
  return new CharAt(*this);
}

CharAt::~CharAt() {
  delete subject_term;
  delete index_term;
}

void CharAt::accept(Visitor_ptr v) {
  v->visitCharAt(this);
}

void CharAt::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(index_term);
}

SubString::SubString(Term_ptr subject_term, Term_ptr start_index_term)
        : Term(Term::Type::SUBSTRING), subject_term (subject_term),
          start_index_term (start_index_term), end_index_term (nullptr) {
}

SubString::SubString(Term_ptr subject_term, Term_ptr start_index_term, Term_ptr end_index_term)
        : Term(Term::Type::SUBSTRING), subject_term (subject_term),
          start_index_term (start_index_term), end_index_term (end_index_term) {
}

SubString::SubString(const SubString& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  start_index_term = other.start_index_term->clone();
  if (end_index_term not_eq nullptr) {
    end_index_term = other.end_index_term->clone();
  }
}

SubString_ptr SubString::clone() const {
  return new SubString(*this);
}

SubString::~SubString() {
  delete subject_term;
  delete start_index_term;
  delete end_index_term;
}

void SubString::accept(Visitor_ptr v) {
  v->visitSubString(this);
}

void SubString::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(start_index_term);
  v->visit(end_index_term);
}

SubStringFirstOf::SubStringFirstOf(Term_ptr subject_term, Term_ptr start_index_term)
        : Term(Term::Type::SUBSTRINGFIRSTOF), subject_term (subject_term),
          start_index_term (start_index_term) {
}

SubStringFirstOf::SubStringFirstOf(const SubStringFirstOf& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  start_index_term = other.start_index_term->clone();
}

SubStringFirstOf_ptr SubStringFirstOf::clone() const {
  return new SubStringFirstOf(*this);
}

SubStringFirstOf::~SubStringFirstOf() {
  delete subject_term;
  delete start_index_term;
}

void SubStringFirstOf::accept(Visitor_ptr v) {
  v->visitSubStringFirstOf(this);
}

void SubStringFirstOf::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(start_index_term);
}

SubStringLastOf::SubStringLastOf(Term_ptr subject_term, Term_ptr start_index_term)
        : Term(Term::Type::SUBSTRINGLASTOF), subject_term (subject_term),
          start_index_term (start_index_term) {
}

SubStringLastOf::SubStringLastOf(const SubStringLastOf& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  start_index_term = other.start_index_term->clone();
}

SubStringLastOf_ptr SubStringLastOf::clone() const {
  return new SubStringLastOf(*this);
}

SubStringLastOf::~SubStringLastOf() {
  delete subject_term;
  delete start_index_term;
}

void SubStringLastOf::accept(Visitor_ptr v) {
  v->visitSubStringLastOf(this);
}

void SubStringLastOf::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(start_index_term);
}

ToUpper::ToUpper(Term_ptr subject_term)
        : Term(Term::Type::TOUPPER), subject_term(subject_term) {
}

ToUpper::ToUpper(const ToUpper& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
}

ToUpper_ptr ToUpper::clone() const {
  return new ToUpper(*this);
}

ToUpper::~ToUpper() {
  delete subject_term;
}

void ToUpper::accept(Visitor_ptr v) {
  v->visitToUpper(this);
}

void ToUpper::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
}

ToLower::ToLower(Term_ptr subject_term)
        : Term(Term::Type::TOLOWER), subject_term(subject_term) {
}

ToLower::ToLower(const ToLower& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
}

ToLower_ptr ToLower::clone() const {
  return new ToLower(*this);
}

ToLower::~ToLower() {
  delete subject_term;
}

void ToLower::accept(Visitor_ptr v) {
  v->visitToLower(this);
}

void ToLower::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
}

Trim::Trim(Term_ptr subject_term)
        : Term(Term::Type::TRIM), subject_term(subject_term) {
}

Trim::Trim(const Trim& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
}

Trim_ptr Trim::clone() const {
  return new Trim(*this);
}

Trim::~Trim() {
  delete subject_term;
}

void Trim::accept(Visitor_ptr v) {
  v->visitTrim(this);
}

void Trim::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
}

Replace::Replace(Term_ptr subject_term, Term_ptr search_term, Term_ptr replace_term)
        : Term(Term::Type::REPLACE), subject_term(subject_term), search_term(search_term), replace_term(replace_term) {
}

Replace::Replace(const Replace& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  search_term = other.search_term->clone();
  replace_term = other.replace_term->clone();
}

Replace_ptr Replace::clone() const {
  return new Replace(*this);
}

Replace::~Replace() {
  delete subject_term;
  delete search_term;
  delete replace_term;
}

void Replace::accept(Visitor_ptr v) {
  v->visitReplace(this);
}

void Replace::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(search_term);
  v->visit(replace_term);
}

Count::Count(Term_ptr bound_term, Term_ptr subject_term)
        : Term(Term::Type::COUNT), subject_term(subject_term), bound_term(bound_term) {
}

Count::Count(const Count& other)
        : Term(other.type) {
  subject_term = other.subject_term->clone();
  bound_term = other.bound_term->clone();
}

Count_ptr Count::clone() const {
  return new Count(*this);
}

Count::~Count() {
  delete subject_term;
  delete bound_term;
}

void Count::accept(Visitor_ptr v) {
  v->visitCount(this);
}
void Count::visit_children(Visitor_ptr v) {
  v->visit(subject_term);
  v->visit(bound_term);
}

Ite::Ite(Term_ptr cond, Term_ptr then_branch, Term_ptr else_branch)
        : Term(Term::Type::ITE), cond(cond), then_branch(then_branch), else_branch(else_branch) {
}
Ite::Ite(const Ite& other)
        : Term(other.type) {
  cond = other.cond->clone();
  then_branch = other.then_branch->clone();
  else_branch = other.else_branch->clone();
}
Ite_ptr Ite::clone() const {
  return new Ite(*this);
}
Ite::~Ite() {
  delete cond;
  delete then_branch;
  delete else_branch;
}

void Ite::accept(Visitor_ptr v) {
  v->visitIte(this);
}
void Ite::visit_children(Visitor_ptr v) {
  v->visit(cond);
  v->visit(then_branch);
  v->visit(else_branch);
}

ReConcat::ReConcat(TermList_ptr term_list)
        : Term(Term::Type::RECONCAT), term_list(term_list) {
}
ReConcat::ReConcat(const ReConcat& other)
        : Term(other.type) {
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
ReConcat_ptr ReConcat::clone() const {
  return new ReConcat(*this);
}
ReConcat::~ReConcat() {
  deallocate_list(term_list);
  delete term_list;
}

void ReConcat::accept(Visitor_ptr v) {
  v->visitReConcat(this);
}
void ReConcat::visit_children(Visitor_ptr v) {
  v->visit_list(term_list);
}

ToRegex::ToRegex(Term_ptr term)
        : Term(Term::Type::TOREGEX), term(term) {
}
ToRegex::ToRegex(const ToRegex& other)
        : Term(other.type) {
  term = other.term->clone();
}
ToRegex_ptr ToRegex::clone() const {
  return new ToRegex(*this);
}
ToRegex::~ToRegex() {
  delete term;
}

void ToRegex::accept(Visitor_ptr v) {
  v->visitToRegex(this);
}
void ToRegex::visit_children(Visitor_ptr v) {
  v->visit(term);
}

UnknownTerm::UnknownTerm(Term_ptr term, TermList_ptr term_list)
        : Term(Term::Type::UNKNOWN), term(term), term_list(term_list) {
}
UnknownTerm::UnknownTerm(const UnknownTerm& other)
        : Term(other.type) {
  term = other.term->clone();
  term_list = new TermList();
  for (auto& term : *(other.term_list)) {
    term_list->push_back(term->clone());
  }
}
UnknownTerm* UnknownTerm::clone() const {
  return new UnknownTerm(*this);
}
UnknownTerm::~UnknownTerm() {
  delete term;
  deallocate_list(term_list);
  delete term_list;
}

void UnknownTerm::accept(Visitor_ptr v) {
  v->visitUnknownTerm(this);
}
void UnknownTerm::visit_children(Visitor_ptr v) {
  v->visit(term);
  v->visit_list(term_list);
}

AsQualIdentifier::AsQualIdentifier(Identifier_ptr identifier, Sort_ptr sort)
        : Term(Term::Type::ASQUALIDENTIFIER), identifier(identifier), sort(sort) {
}
AsQualIdentifier::AsQualIdentifier(const AsQualIdentifier& other)
        : Term(other.type) {
  identifier = other.identifier->clone();
  sort = other.sort->clone();
}
AsQualIdentifier_ptr AsQualIdentifier::clone() const {
  return new AsQualIdentifier(*this);
}
AsQualIdentifier::~AsQualIdentifier() {
  delete identifier;
  delete sort;
}

void AsQualIdentifier::accept(Visitor_ptr v) {
  v->visitAsQualIdentifier(this);
}
void AsQualIdentifier::visit_children(Visitor_ptr v) {
  v->visit(identifier);
  v->visit(sort);
}

QualIdentifier::QualIdentifier(Identifier_ptr identifier)
        : Term(Term::Type::QUALIDENTIFIER), identifier(identifier) {
}
QualIdentifier::QualIdentifier(const QualIdentifier& other)
        : Term(other.type) {
  identifier = other.identifier->clone();
}
QualIdentifier_ptr QualIdentifier::clone() const {
  return new QualIdentifier(*this);
}
QualIdentifier::~QualIdentifier() {
  delete identifier;
}

std::string QualIdentifier::getVarName() {
  return identifier->getName();
}

void QualIdentifier::accept(Visitor_ptr v) {
  v->visitQualIdentifier(this);
}
void QualIdentifier::visit_children(Visitor_ptr v) {
  v->visit(identifier);
}

TermConstant::TermConstant(Primitive_ptr primitive)
        : Term(Term::Type::TERMCONSTANT), primitive(primitive) {
}
TermConstant::TermConstant(const TermConstant& other)
        : Term(other.type) {
  primitive = other.primitive->clone();
}
TermConstant_ptr TermConstant::clone() const {
  return new TermConstant(*this);
}
TermConstant::~TermConstant() {
  delete primitive;
}

void TermConstant::accept(Visitor_ptr v) {
  v->visitTermConstant(this);
}
void TermConstant::visit_children(Visitor_ptr v) {
  v->visit(primitive);
}

std::string TermConstant::getValue() const {
  return primitive->getData();
}

Primitive::Type TermConstant::getValueType() const {
  return primitive->getType();
}

/* ends Terms */

Sort::Sort(TVariable_ptr type)
        : identifier(nullptr), sort_list(nullptr), var_type(type) {
}
Sort::Sort(Identifier_ptr identifier)
        : identifier(identifier), sort_list(nullptr), var_type(nullptr) {
}
Sort::Sort(Identifier_ptr identifier, SortList_ptr sort_list)
        : identifier(identifier), sort_list(sort_list), var_type(nullptr) {
}
Sort::Sort(const Sort& other) {
  identifier = nullptr;
  if (other.identifier != nullptr) {
    identifier = other.identifier->clone();
  }
  sort_list = nullptr;
  if (other.sort_list != nullptr) {
    sort_list = new SortList();
    for (auto& sort : *(other.sort_list)) {
      sort_list->push_back(sort->clone());
    }
  }
  var_type = nullptr;
  if (other.var_type != nullptr) {
    var_type = other.var_type->clone();
  }
}
Sort_ptr Sort::clone() const {
  return new Sort(*this);
}
Sort::~Sort() {
  delete identifier;
  deallocate_list(sort_list);
  delete sort_list;
  delete var_type;
}

void Sort::accept(Visitor_ptr v) {
  v->visitSort(this);
}

void Sort::visit_children(Visitor_ptr v) {
  v->visit(identifier);
  v->visit_list(sort_list);
  v->visit(var_type);
}

Attribute::Attribute() {
}
Attribute::Attribute(const Attribute& other) {
}
Attribute_ptr Attribute::clone() const {
  return new Attribute(*this);
}
Attribute::~Attribute() {
}

void Attribute::accept(Visitor_ptr v) {
}

void Attribute::visit_children(Visitor_ptr v) {
  throw std::runtime_error("Add attribute implementation!");
}

SortedVar::SortedVar(Primitive_ptr symbol, Sort_ptr sort)
        : symbol(symbol), sort(sort) {
}
SortedVar::SortedVar(const SortedVar& other) {
  symbol = other.symbol->clone();
  sort = other.sort->clone();
}
SortedVar_ptr SortedVar::clone() const {
  return new SortedVar(*this);
}
SortedVar::~SortedVar() {
  delete symbol;
  delete sort;
}

void SortedVar::accept(Visitor_ptr v) {
  v->visitSortedVar(this);
}

void SortedVar::visit_children(Visitor_ptr v) {
  v->visit(symbol);
  v->visit(sort);
}

VarBinding::VarBinding(Primitive_ptr symbol, Term_ptr term)
        : symbol(symbol), term(term) {
}
VarBinding::VarBinding(const VarBinding& other) {
  symbol = other.symbol->clone();
  term = other.term->clone();
}
VarBinding_ptr VarBinding::clone() const {
  return new VarBinding(*this);
}
VarBinding::~VarBinding() {
  delete symbol;
  delete term;
}

void VarBinding::accept(Visitor_ptr v) {
  v->visitVarBinding(this);
}

void VarBinding::visit_children(Visitor_ptr v) {
  v->visit(symbol);
  v->visit(term);
}

Identifier::Identifier(Primitive_ptr symbol)
        : underscore(nullptr), symbol(symbol), numeral_list(nullptr) {
}

Identifier::Identifier(Primitive_ptr underscore, Primitive_ptr symbol, NumeralList_ptr numeral_list)
        : underscore(underscore), symbol(symbol), numeral_list(numeral_list) {
}
Identifier::Identifier(const Identifier& other) {
  underscore = nullptr;
  if (other.underscore != nullptr) {
    underscore = other.underscore->clone();
  }
  symbol = nullptr;
  if (other.symbol != nullptr) {
    symbol = other.symbol->clone();
  }
  numeral_list = nullptr;
  if (other.numeral_list != nullptr) {
    numeral_list = new NumeralList();
    for (auto& num : *(other.numeral_list)) {
      numeral_list->push_back(num->clone());
    }
  }
}
Identifier_ptr Identifier::clone() const {
  return new Identifier(*this);
}
Identifier::~Identifier() {
  delete underscore;
  delete symbol;
  deallocate_list(numeral_list);
  delete numeral_list;

}

void Identifier::accept(Visitor_ptr v) {
  v->visitIdentifier(this);
}

void Identifier::visit_children(Visitor_ptr v) {
  v->visit(underscore);
  v->visit(symbol);
  v->visit_list(numeral_list);
}

Primitive::Type Identifier::getType() {
  return symbol->getType();
}

std::string Identifier::getName() {
  return symbol->getData();
}

const std::string Primitive::Name::NONE = "NONE";
const std::string Primitive::Name::BOOL = "BOOL";
const std::string Primitive::Name::BINARY = "BINARY";
const std::string Primitive::Name::DECIMAL = "DECIMAL";
const std::string Primitive::Name::HEXADECIMAL = "HEXADECIMAL";
const std::string Primitive::Name::KEYWORD = "KEYWORD";
const std::string Primitive::Name::NUMERAL = "NUMERAL";
const std::string Primitive::Name::STRING = "STRING";
const std::string Primitive::Name::REGEX = "REGEX";
const std::string Primitive::Name::SYMBOL = "SYMBOL";

Primitive::Primitive(const std::string data, const Primitive::Type type)
        : data(data), type(type) {
}
Primitive::Primitive(const Primitive& other) {
  data = other.data;
  type = other.type;
}
Primitive_ptr Primitive::clone() const {
  return new Primitive(*this);
}
Primitive::~Primitive() {
  DVLOG(AST_VLOG_LEVEL) << "Primitive( " << *this << " ) deallocated.";
}

std::string Primitive::str() const {
  std::stringstream ss;
  ss << data << ":<";

  switch (type) {
  case Primitive::Type::NONE:
    ss << Primitive::Name::NONE;
    break;
  case Primitive::Type::BOOL:
    ss << Primitive::Name::BOOL;
    break;
  case Primitive::Type::BINARY:
    ss << Primitive::Name::BINARY;
    break;
  case Primitive::Type::DECIMAL:
    ss << Primitive::Name::DECIMAL;
    break;
  case Primitive::Type::HEXADECIMAL:
    ss << Primitive::Name::HEXADECIMAL;
    break;
  case Primitive::Type::KEYWORD:
    ss << Primitive::Name::KEYWORD;
    break;
  case Primitive::Type::NUMERAL:
    ss << Primitive::Name::NUMERAL;
    break;
  case Primitive::Type::STRING:
    ss << Primitive::Name::STRING;
    break;
  case Primitive::Type::SYMBOL:
    ss << Primitive::Name::SYMBOL;
    break;
  case Primitive::Type::REGEX:
    ss << Primitive::Name::REGEX;
    break;
  default:
    LOG(FATAL)<< "Unknown primitive!";
    break;
  }
  ss << ">";

  return ss.str();
}

std::string Primitive::getData() const {
  return data;
}
void Primitive::setData(std::string data) {
  this->data = data;
}
Primitive::Type Primitive::getType() const {
  return type;
}
void Primitive::setType(Primitive::Type type) {
  this->type = type;
}

void Primitive::accept(Visitor_ptr v) {
  v->visitPrimitive(this);
}

void Primitive::visit_children(Visitor_ptr v) {
}

std::ostream& operator<<(std::ostream& os, const Primitive& primitive) {
  return os << primitive.str();
}

const std::string TVariable::Name::NONE = "none";
const std::string TVariable::Name::BOOL = "Bool";
const std::string TVariable::Name::INT = "Int";
const std::string TVariable::Name::STRING = "String";

TVariable::TVariable(TVariable::Type type)
        : type(type) {
}
TVariable::TVariable(const TVariable& other)
        : type(other.type) {
}
TVariable_ptr TVariable::clone() const {
  return new TVariable(*this);
}
TVariable::~TVariable() {
}

std::string TVariable::str() const {
  switch (type) {
  case TVariable::Type::NONE:
    return TVariable::Name::NONE;
  case TVariable::Type::BOOL:
    return TVariable::Name::BOOL;
  case TVariable::Type::INT:
    return TVariable::Name::INT;
  case TVariable::Type::STRING:
    return TVariable::Name::STRING;
  default:
    LOG(FATAL)<< "Unknown variable type!";
    return "";
  }
}
TVariable::Type TVariable::getType() const {
  return type;
}

void TVariable::accept(Visitor_ptr v) {
  v->visitTVariable(this);
}
void TVariable::visit_children(Visitor_ptr v) {
}

std::ostream& operator<<(std::ostream& os, const TVariable& t_variable) {
  return os << t_variable.str();
}

TBool::TBool()
        : TVariable(TVariable::Type::BOOL) {
}
TBool::TBool(const TBool& other)
        : TVariable(TVariable::Type::BOOL) {
}
TBool_ptr TBool::clone() const {
  return new TBool(*this);
}
TBool::~TBool() {
}

void TBool::accept(Visitor_ptr v) {
  v->visitTBool(this);
}
void TBool::visit_children(Visitor_ptr v) {
}

TInt::TInt()
        : TVariable(TVariable::Type::INT) {
}
TInt::TInt(const TInt& other)
        : TVariable(TVariable::Type::INT) {
}
TInt_ptr TInt::clone() const {
  return new TInt(*this);
}
TInt::~TInt() {
}

void TInt::accept(Visitor_ptr v) {
  v->visitTInt(this);
}
void TInt::visit_children(Visitor_ptr v) {
}

TString::TString()
        : TVariable(TVariable::Type::STRING) {
}
TString::TString(const TString& other)
        : TVariable(TVariable::Type::STRING) {
}
TString_ptr TString::clone() const {
  return new TString(*this);
}
TString::~TString() {
}

void TString::accept(Visitor_ptr v) {
  v->visitTString(this);
}
void TString::visit_children(Visitor_ptr v) {
}

Variable::Variable(std::string name, Variable::Type type)
        : TVariable(type), name(name), is_symbolic(name.find("var_") == 0) {
}
Variable::Variable(Primitive_ptr primitive, Variable::Type type)
        : TVariable(type), name(primitive->getData()), is_symbolic(name.find("var_") == 0) {
}
Variable::Variable(std::string name, Variable::Type type, bool is_symbolic)
        : TVariable(type), name(name), is_symbolic(is_symbolic) {
}
Variable::Variable(Primitive_ptr primitive, Variable::Type type, bool is_symbolic)
        : TVariable(type), name(primitive->getData()), is_symbolic(is_symbolic) {
}
Variable::Variable(const Variable& other)
        : TVariable(other.type) {
  name = other.name;
  is_symbolic = other.is_symbolic;
}

Variable_ptr Variable::clone() const {
  return new Variable(*this);
}
Variable::~Variable() {
}

std::string Variable::str() const {
  std::stringstream ss;
  ss << name << ":<" << TVariable::str() << ">";
  std::string tmp = (is_symbolic) ? " (symbolic)" : " (?)";
  ss << tmp;
  return ss.str();
}

std::string Variable::getName() const {
  return name;
}

Variable::Type Variable::getType() const {
  return type;
}

bool Variable::isSymbolic() const {
  return is_symbolic;
}

void Variable::setSymbolic(bool is_symbolic) {
  this->is_symbolic = is_symbolic;
}

void Variable::accept(Visitor_ptr v) {
  v->visitVariable(this);
}

void Variable::visit_children(Visitor_ptr v) {
}

} /* namespace SMT */
} /* namespace Vlab */
