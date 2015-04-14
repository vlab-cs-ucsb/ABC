// A Bison parser, made by GNU Bison 3.0.2.

// Skeleton implementation for Bison LALR(1) parsers in C++

// Copyright (C) 2002-2013 Free Software Foundation, Inc.

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

// As a special exception, you may create a larger work that contains
// part or all of the Bison parser skeleton and distribute that work
// under terms of your choice, so long as that work isn't itself a
// parser generator using the skeleton or a modified version thereof
// as a parser skeleton.  Alternatively, if you modify or redistribute
// the parser skeleton itself, you may (at your option) remove this
// special exception, which will cause the skeleton and the resulting
// Bison output files to be licensed under the GNU General Public
// License without this special exception.

// This special exception was added by the Free Software Foundation in
// version 2.2 of Bison.


// First part of user declarations.

#line 37 "parser.cpp" // lalr1.cc:399

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

#include "parser.hpp"

// User implementation prologue.

#line 51 "parser.cpp" // lalr1.cc:407
// Unqualified %code blocks.
#line 34 "parser.ypp" // lalr1.cc:408


#include "Scanner.h"

#define yylex scanner.yylex_next_symbol


#line 61 "parser.cpp" // lalr1.cc:408


#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> // FIXME: INFRINGES ON USER NAME SPACE.
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K].location)
/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

# ifndef YYLLOC_DEFAULT
#  define YYLLOC_DEFAULT(Current, Rhs, N)                               \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).begin  = YYRHSLOC (Rhs, 1).begin;                   \
          (Current).end    = YYRHSLOC (Rhs, N).end;                     \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).begin = (Current).end = YYRHSLOC (Rhs, 0).end;      \
        }                                                               \
    while (/*CONSTCOND*/ false)
# endif


// Suppress unused-variable warnings by "using" E.
#define YYUSE(E) ((void) (E))

// Enable debugging if requested.
#if YYDEBUG

// A pseudo ostream that takes yydebug_ into account.
# define YYCDEBUG if (yydebug_) (*yycdebug_)

# define YY_SYMBOL_PRINT(Title, Symbol)         \
  do {                                          \
    if (yydebug_)                               \
    {                                           \
      *yycdebug_ << Title << ' ';               \
      yy_print_ (*yycdebug_, Symbol);           \
      *yycdebug_ << std::endl;                  \
    }                                           \
  } while (false)

# define YY_REDUCE_PRINT(Rule)          \
  do {                                  \
    if (yydebug_)                       \
      yy_reduce_print_ (Rule);          \
  } while (false)

# define YY_STACK_PRINT()               \
  do {                                  \
    if (yydebug_)                       \
      yystack_print_ ();                \
  } while (false)

#else // !YYDEBUG

# define YYCDEBUG if (false) std::cerr
# define YY_SYMBOL_PRINT(Title, Symbol)  YYUSE(Symbol)
# define YY_REDUCE_PRINT(Rule)           static_cast<void>(0)
# define YY_STACK_PRINT()                static_cast<void>(0)

#endif // !YYDEBUG

#define yyerrok         (yyerrstatus_ = 0)
#define yyclearin       (yyempty = true)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYRECOVERING()  (!!yyerrstatus_)

#line 9 "parser.ypp" // lalr1.cc:474
namespace  Vlab  {
#line 147 "parser.cpp" // lalr1.cc:474

  /* Return YYSTR after stripping away unnecessary quotes and
     backslashes, so that it's suitable for yyerror.  The heuristic is
     that double-quoting is unnecessary unless the string contains an
     apostrophe, a comma, or backslash (other than backslash-backslash).
     YYSTR is taken from yytname.  */
  std::string
   Parser ::yytnamerr_ (const char *yystr)
  {
    if (*yystr == '"')
      {
        std::string yyr = "";
        char const *yyp = yystr;

        for (;;)
          switch (*++yyp)
            {
            case '\'':
            case ',':
              goto do_not_strip_quotes;

            case '\\':
              if (*++yyp != '\\')
                goto do_not_strip_quotes;
              // Fall through.
            default:
              yyr += *yyp;
              break;

            case '"':
              return yyr;
            }
      do_not_strip_quotes: ;
      }

    return yystr;
  }


  /// Build a parser object.
   Parser :: Parser  (smtlib::Script*& script_yyarg, Scanner& scanner_yyarg)
    :
#if YYDEBUG
      yydebug_ (false),
      yycdebug_ (&std::cerr),
#endif
      script (script_yyarg),
      scanner (scanner_yyarg)
  {}

   Parser ::~ Parser  ()
  {}


  /*---------------.
  | Symbol types.  |
  `---------------*/



  // by_state.
  inline
   Parser ::by_state::by_state ()
    : state (empty)
  {}

  inline
   Parser ::by_state::by_state (const by_state& other)
    : state (other.state)
  {}

  inline
  void
   Parser ::by_state::move (by_state& that)
  {
    state = that.state;
    that.state = empty;
  }

  inline
   Parser ::by_state::by_state (state_type s)
    : state (s)
  {}

  inline
   Parser ::symbol_number_type
   Parser ::by_state::type_get () const
  {
    return state == empty ? 0 : yystos_[state];
  }

  inline
   Parser ::stack_symbol_type::stack_symbol_type ()
  {}


  inline
   Parser ::stack_symbol_type::stack_symbol_type (state_type s, symbol_type& that)
    : super_type (s, that.location)
  {
      switch (that.type_get ())
    {
      case 74: // attribute_list_
        value.move< smtlib::AttributeList_ptr > (that.value);
        break;

      case 75: // attribute
        value.move< smtlib::Attribute_ptr > (that.value);
        break;

      case 59: // command_list
        value.move< smtlib::CommandList_ptr > (that.value);
        break;

      case 60: // command
        value.move< smtlib::Command_ptr > (that.value);
        break;

      case 81: // identifier
        value.move< smtlib::Identifier_ptr > (that.value);
        break;

      case 82: // numeral_list_
        value.move< smtlib::NumeralList_ptr > (that.value);
        break;

      case 86: // spec_constant
        value.move< smtlib::Primitive_ptr > (that.value);
        break;

      case 77: // sort_list
      case 78: // sort_list_
        value.move< smtlib::SortList_ptr > (that.value);
        break;

      case 79: // sort
        value.move< smtlib::Sort_ptr > (that.value);
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        value.move< smtlib::SortedVarList_ptr > (that.value);
        break;

      case 69: // sorted_var
        value.move< smtlib::SortedVar_ptr > (that.value);
        break;

      case 65: // term_list_
        value.move< smtlib::TermList_ptr > (that.value);
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        value.move< smtlib::Term_ptr > (that.value);
        break;

      case 70: // var_binding_list_
        value.move< smtlib::VarBindingList_ptr > (that.value);
        break;

      case 71: // var_binding
        value.move< smtlib::VarBinding_ptr > (that.value);
        break;

      case 80: // var_type
        value.move< smtlib::VarType_ptr > (that.value);
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        value.move< std::string > (that.value);
        break;

      default:
        break;
    }

    // that is emptied.
    that.type = empty;
  }

  inline
   Parser ::stack_symbol_type&
   Parser ::stack_symbol_type::operator= (const stack_symbol_type& that)
  {
    state = that.state;
      switch (that.type_get ())
    {
      case 74: // attribute_list_
        value.copy< smtlib::AttributeList_ptr > (that.value);
        break;

      case 75: // attribute
        value.copy< smtlib::Attribute_ptr > (that.value);
        break;

      case 59: // command_list
        value.copy< smtlib::CommandList_ptr > (that.value);
        break;

      case 60: // command
        value.copy< smtlib::Command_ptr > (that.value);
        break;

      case 81: // identifier
        value.copy< smtlib::Identifier_ptr > (that.value);
        break;

      case 82: // numeral_list_
        value.copy< smtlib::NumeralList_ptr > (that.value);
        break;

      case 86: // spec_constant
        value.copy< smtlib::Primitive_ptr > (that.value);
        break;

      case 77: // sort_list
      case 78: // sort_list_
        value.copy< smtlib::SortList_ptr > (that.value);
        break;

      case 79: // sort
        value.copy< smtlib::Sort_ptr > (that.value);
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        value.copy< smtlib::SortedVarList_ptr > (that.value);
        break;

      case 69: // sorted_var
        value.copy< smtlib::SortedVar_ptr > (that.value);
        break;

      case 65: // term_list_
        value.copy< smtlib::TermList_ptr > (that.value);
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        value.copy< smtlib::Term_ptr > (that.value);
        break;

      case 70: // var_binding_list_
        value.copy< smtlib::VarBindingList_ptr > (that.value);
        break;

      case 71: // var_binding
        value.copy< smtlib::VarBinding_ptr > (that.value);
        break;

      case 80: // var_type
        value.copy< smtlib::VarType_ptr > (that.value);
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        value.copy< std::string > (that.value);
        break;

      default:
        break;
    }

    location = that.location;
    return *this;
  }


  template <typename Base>
  inline
  void
   Parser ::yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const
  {
    if (yymsg)
      YY_SYMBOL_PRINT (yymsg, yysym);
  }

#if YYDEBUG
  template <typename Base>
  void
   Parser ::yy_print_ (std::ostream& yyo,
                                     const basic_symbol<Base>& yysym) const
  {
    std::ostream& yyoutput = yyo;
    YYUSE (yyoutput);
    symbol_number_type yytype = yysym.type_get ();
    yyo << (yytype < yyntokens_ ? "token" : "nterm")
        << ' ' << yytname_[yytype] << " ("
        << yysym.location << ": ";
    switch (yytype)
    {
            case 50: // "binary"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 457 "parser.cpp" // lalr1.cc:617
        break;

      case 51: // "decimal"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 464 "parser.cpp" // lalr1.cc:617
        break;

      case 52: // "hexadecimal"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 471 "parser.cpp" // lalr1.cc:617
        break;

      case 53: // "keyword"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 478 "parser.cpp" // lalr1.cc:617
        break;

      case 54: // "number"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 485 "parser.cpp" // lalr1.cc:617
        break;

      case 55: // "string"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 492 "parser.cpp" // lalr1.cc:617
        break;

      case 56: // "symbol"

#line 133 "parser.ypp" // lalr1.cc:617
        { yyoutput << yysym.value.template as< std::string > (); }
#line 499 "parser.cpp" // lalr1.cc:617
        break;


      default:
        break;
    }
    yyo << ')';
  }
#endif

  inline
  void
   Parser ::yypush_ (const char* m, state_type s, symbol_type& sym)
  {
    stack_symbol_type t (s, sym);
    yypush_ (m, t);
  }

  inline
  void
   Parser ::yypush_ (const char* m, stack_symbol_type& s)
  {
    if (m)
      YY_SYMBOL_PRINT (m, s);
    yystack_.push (s);
  }

  inline
  void
   Parser ::yypop_ (unsigned int n)
  {
    yystack_.pop (n);
  }

#if YYDEBUG
  std::ostream&
   Parser ::debug_stream () const
  {
    return *yycdebug_;
  }

  void
   Parser ::set_debug_stream (std::ostream& o)
  {
    yycdebug_ = &o;
  }


   Parser ::debug_level_type
   Parser ::debug_level () const
  {
    return yydebug_;
  }

  void
   Parser ::set_debug_level (debug_level_type l)
  {
    yydebug_ = l;
  }
#endif // YYDEBUG

  inline  Parser ::state_type
   Parser ::yy_lr_goto_state_ (state_type yystate, int yysym)
  {
    int yyr = yypgoto_[yysym - yyntokens_] + yystate;
    if (0 <= yyr && yyr <= yylast_ && yycheck_[yyr] == yystate)
      return yytable_[yyr];
    else
      return yydefgoto_[yysym - yyntokens_];
  }

  inline bool
   Parser ::yy_pact_value_is_default_ (int yyvalue)
  {
    return yyvalue == yypact_ninf_;
  }

  inline bool
   Parser ::yy_table_value_is_error_ (int yyvalue)
  {
    return yyvalue == yytable_ninf_;
  }

  int
   Parser ::parse ()
  {
    /// Whether yyla contains a lookahead.
    bool yyempty = true;

    // State.
    int yyn;
    /// Length of the RHS of the rule being reduced.
    int yylen = 0;

    // Error handling.
    int yynerrs_ = 0;
    int yyerrstatus_ = 0;

    /// The lookahead symbol.
    symbol_type yyla;

    /// The locations where the error started and ended.
    stack_symbol_type yyerror_range[3];

    /// The return value of parse ().
    int yyresult;

    // FIXME: This shoud be completely indented.  It is not yet to
    // avoid gratuitous conflicts when merging into the master branch.
    try
      {
    YYCDEBUG << "Starting parse" << std::endl;


    // User initialization code.
    #line 29 "/home/baki/workspaces/default/ABC/src/parser/parser.ypp" // lalr1.cc:725
{

}

#line 620 "parser.cpp" // lalr1.cc:725

    /* Initialize the stack.  The initial state will be set in
       yynewstate, since the latter expects the semantical and the
       location values to have been already stored, initialize these
       stacks with a primary value.  */
    yystack_.clear ();
    yypush_ (YY_NULLPTR, 0, yyla);

    // A new symbol was pushed on the stack.
  yynewstate:
    YYCDEBUG << "Entering state " << yystack_[0].state << std::endl;

    // Accept?
    if (yystack_[0].state == yyfinal_)
      goto yyacceptlab;

    goto yybackup;

    // Backup.
  yybackup:

    // Try to take a decision without lookahead.
    yyn = yypact_[yystack_[0].state];
    if (yy_pact_value_is_default_ (yyn))
      goto yydefault;

    // Read a lookahead token.
    if (yyempty)
      {
        YYCDEBUG << "Reading a token: ";
        try
          {
            symbol_type yylookahead (yylex ());
            yyla.move (yylookahead);
          }
        catch (const syntax_error& yyexc)
          {
            error (yyexc);
            goto yyerrlab1;
          }
        yyempty = false;
      }
    YY_SYMBOL_PRINT ("Next token is", yyla);

    /* If the proper action on seeing token YYLA.TYPE is to reduce or
       to detect an error, take that action.  */
    yyn += yyla.type_get ();
    if (yyn < 0 || yylast_ < yyn || yycheck_[yyn] != yyla.type_get ())
      goto yydefault;

    // Reduce or error.
    yyn = yytable_[yyn];
    if (yyn <= 0)
      {
        if (yy_table_value_is_error_ (yyn))
          goto yyerrlab;
        yyn = -yyn;
        goto yyreduce;
      }

    // Discard the token being shifted.
    yyempty = true;

    // Count tokens shifted since error; after three, turn off error status.
    if (yyerrstatus_)
      --yyerrstatus_;

    // Shift the lookahead token.
    yypush_ ("Shifting", yyn, yyla);
    goto yynewstate;

  /*-----------------------------------------------------------.
  | yydefault -- do the default action for the current state.  |
  `-----------------------------------------------------------*/
  yydefault:
    yyn = yydefact_[yystack_[0].state];
    if (yyn == 0)
      goto yyerrlab;
    goto yyreduce;

  /*-----------------------------.
  | yyreduce -- Do a reduction.  |
  `-----------------------------*/
  yyreduce:
    yylen = yyr2_[yyn];
    {
      stack_symbol_type yylhs;
      yylhs.state = yy_lr_goto_state_(yystack_[yylen].state, yyr1_[yyn]);
      /* Variants are always initialized to an empty instance of the
         correct type. The default '$$ = $1' action is NOT applied
         when using variants.  */
        switch (yyr1_[yyn])
    {
      case 74: // attribute_list_
        yylhs.value.build< smtlib::AttributeList_ptr > ();
        break;

      case 75: // attribute
        yylhs.value.build< smtlib::Attribute_ptr > ();
        break;

      case 59: // command_list
        yylhs.value.build< smtlib::CommandList_ptr > ();
        break;

      case 60: // command
        yylhs.value.build< smtlib::Command_ptr > ();
        break;

      case 81: // identifier
        yylhs.value.build< smtlib::Identifier_ptr > ();
        break;

      case 82: // numeral_list_
        yylhs.value.build< smtlib::NumeralList_ptr > ();
        break;

      case 86: // spec_constant
        yylhs.value.build< smtlib::Primitive_ptr > ();
        break;

      case 77: // sort_list
      case 78: // sort_list_
        yylhs.value.build< smtlib::SortList_ptr > ();
        break;

      case 79: // sort
        yylhs.value.build< smtlib::Sort_ptr > ();
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        yylhs.value.build< smtlib::SortedVarList_ptr > ();
        break;

      case 69: // sorted_var
        yylhs.value.build< smtlib::SortedVar_ptr > ();
        break;

      case 65: // term_list_
        yylhs.value.build< smtlib::TermList_ptr > ();
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        yylhs.value.build< smtlib::Term_ptr > ();
        break;

      case 70: // var_binding_list_
        yylhs.value.build< smtlib::VarBindingList_ptr > ();
        break;

      case 71: // var_binding
        yylhs.value.build< smtlib::VarBinding_ptr > ();
        break;

      case 80: // var_type
        yylhs.value.build< smtlib::VarType_ptr > ();
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        yylhs.value.build< std::string > ();
        break;

      default:
        break;
    }


      // Compute the default @$.
      {
        slice<stack_symbol_type, stack_type> slice (yystack_, yylen);
        YYLLOC_DEFAULT (yylhs.location, slice, yylen);
      }

      // Perform the reduction.
      YY_REDUCE_PRINT (yyn);
      try
        {
          switch (yyn)
            {
  case 2:
#line 140 "parser.ypp" // lalr1.cc:847
    { script = new smtlib::Script(yystack_[0].value.as< smtlib::CommandList_ptr > ()); }
#line 812 "parser.cpp" // lalr1.cc:847
    break;

  case 3:
#line 144 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::CommandList_ptr > () -> push_back(yystack_[0].value.as< smtlib::Command_ptr > ()); yylhs.value.as< smtlib::CommandList_ptr > () = yystack_[1].value.as< smtlib::CommandList_ptr > (); }
#line 818 "parser.cpp" // lalr1.cc:847
    break;

  case 4:
#line 145 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::CommandList_ptr > () = new smtlib::CommandList(); }
#line 824 "parser.cpp" // lalr1.cc:847
    break;

  case 5:
#line 149 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::SetLogic(new smtlib::Primitive(yystack_[1].value.as< std::string > (), smtlib::Primitive::SYMBOL)); }
#line 830 "parser.cpp" // lalr1.cc:847
    break;

  case 6:
#line 150 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 836 "parser.cpp" // lalr1.cc:847
    break;

  case 7:
#line 151 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 842 "parser.cpp" // lalr1.cc:847
    break;

  case 8:
#line 152 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 848 "parser.cpp" // lalr1.cc:847
    break;

  case 9:
#line 153 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 854 "parser.cpp" // lalr1.cc:847
    break;

  case 10:
#line 154 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::DeclareFun(new smtlib::Primitive(yystack_[5].value.as< std::string > (), smtlib::Primitive::SYMBOL), yystack_[3].value.as< smtlib::SortList_ptr > (), yystack_[1].value.as< smtlib::Sort_ptr > ());}
#line 860 "parser.cpp" // lalr1.cc:847
    break;

  case 11:
#line 155 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 866 "parser.cpp" // lalr1.cc:847
    break;

  case 12:
#line 156 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 872 "parser.cpp" // lalr1.cc:847
    break;

  case 13:
#line 157 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 878 "parser.cpp" // lalr1.cc:847
    break;

  case 14:
#line 158 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Assert(yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 884 "parser.cpp" // lalr1.cc:847
    break;

  case 15:
#line 159 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::CheckSat(); }
#line 890 "parser.cpp" // lalr1.cc:847
    break;

  case 16:
#line 160 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 896 "parser.cpp" // lalr1.cc:847
    break;

  case 17:
#line 161 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 902 "parser.cpp" // lalr1.cc:847
    break;

  case 18:
#line 162 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 908 "parser.cpp" // lalr1.cc:847
    break;

  case 19:
#line 163 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 914 "parser.cpp" // lalr1.cc:847
    break;

  case 20:
#line 164 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 920 "parser.cpp" // lalr1.cc:847
    break;

  case 21:
#line 165 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 926 "parser.cpp" // lalr1.cc:847
    break;

  case 22:
#line 166 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 932 "parser.cpp" // lalr1.cc:847
    break;

  case 23:
#line 167 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Command_ptr > () = new smtlib::Command(); }
#line 938 "parser.cpp" // lalr1.cc:847
    break;

  case 24:
#line 171 "parser.ypp" // lalr1.cc:847
    { std::cout << "attribute" << std::endl; }
#line 944 "parser.cpp" // lalr1.cc:847
    break;

  case 25:
#line 175 "parser.ypp" // lalr1.cc:847
    { std::cout << yystack_[0].value.as< std::string > () << std::endl; }
#line 950 "parser.cpp" // lalr1.cc:847
    break;

  case 29:
#line 185 "parser.ypp" // lalr1.cc:847
    { std::cout << yystack_[0].value.as< std::string > () << std::endl; }
#line 956 "parser.cpp" // lalr1.cc:847
    break;

  case 30:
#line 197 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::TermList_ptr > () -> push_back(yystack_[0].value.as< smtlib::Term_ptr > ()); yylhs.value.as< smtlib::TermList_ptr > () = yystack_[1].value.as< smtlib::TermList_ptr > ();}
#line 962 "parser.cpp" // lalr1.cc:847
    break;

  case 31:
#line 198 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::TermList_ptr > () = new smtlib::TermList(); yylhs.value.as< smtlib::TermList_ptr > () -> push_back(yystack_[0].value.as< smtlib::Term_ptr > ());}
#line 968 "parser.cpp" // lalr1.cc:847
    break;

  case 32:
#line 202 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Term("!"); }
#line 974 "parser.cpp" // lalr1.cc:847
    break;

  case 33:
#line 203 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Term("exists"); }
#line 980 "parser.cpp" // lalr1.cc:847
    break;

  case 34:
#line 204 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Term("forall"); }
#line 986 "parser.cpp" // lalr1.cc:847
    break;

  case 35:
#line 205 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Term("let"); }
#line 992 "parser.cpp" // lalr1.cc:847
    break;

  case 36:
#line 206 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::And(yystack_[1].value.as< smtlib::TermList_ptr > ()); }
#line 998 "parser.cpp" // lalr1.cc:847
    break;

  case 37:
#line 207 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Not(yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1004 "parser.cpp" // lalr1.cc:847
    break;

  case 38:
#line 208 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::UMinus(yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1010 "parser.cpp" // lalr1.cc:847
    break;

  case 39:
#line 209 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Minus(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1016 "parser.cpp" // lalr1.cc:847
    break;

  case 40:
#line 210 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Plus(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1022 "parser.cpp" // lalr1.cc:847
    break;

  case 41:
#line 211 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Eq(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1028 "parser.cpp" // lalr1.cc:847
    break;

  case 42:
#line 212 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Gt(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1034 "parser.cpp" // lalr1.cc:847
    break;

  case 43:
#line 213 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Ge(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1040 "parser.cpp" // lalr1.cc:847
    break;

  case 44:
#line 214 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Lt(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1046 "parser.cpp" // lalr1.cc:847
    break;

  case 45:
#line 215 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Le(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1052 "parser.cpp" // lalr1.cc:847
    break;

  case 46:
#line 216 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Ite(yystack_[3].value.as< smtlib::Term_ptr > (), yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1058 "parser.cpp" // lalr1.cc:847
    break;

  case 47:
#line 217 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::ReConcat(yystack_[1].value.as< smtlib::TermList_ptr > ()); }
#line 1064 "parser.cpp" // lalr1.cc:847
    break;

  case 48:
#line 218 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::ReOr(yystack_[1].value.as< smtlib::TermList_ptr > ()); }
#line 1070 "parser.cpp" // lalr1.cc:847
    break;

  case 49:
#line 219 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Concat(yystack_[1].value.as< smtlib::TermList_ptr > ()); }
#line 1076 "parser.cpp" // lalr1.cc:847
    break;

  case 50:
#line 220 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::In(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1082 "parser.cpp" // lalr1.cc:847
    break;

  case 51:
#line 221 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::Len(yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1088 "parser.cpp" // lalr1.cc:847
    break;

  case 52:
#line 222 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::ToRegex(yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1094 "parser.cpp" // lalr1.cc:847
    break;

  case 53:
#line 223 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::UnknownTerm(yystack_[2].value.as< smtlib::Term_ptr > (), yystack_[1].value.as< smtlib::TermList_ptr > ()); }
#line 1100 "parser.cpp" // lalr1.cc:847
    break;

  case 54:
#line 224 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = yystack_[0].value.as< smtlib::Term_ptr > (); }
#line 1106 "parser.cpp" // lalr1.cc:847
    break;

  case 55:
#line 225 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = yystack_[0].value.as< smtlib::Term_ptr > (); }
#line 1112 "parser.cpp" // lalr1.cc:847
    break;

  case 56:
#line 229 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortedVarList_ptr > () = yystack_[0].value.as< smtlib::SortedVarList_ptr > (); }
#line 1118 "parser.cpp" // lalr1.cc:847
    break;

  case 57:
#line 230 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortedVarList_ptr > () = new smtlib::SortedVarList(); }
#line 1124 "parser.cpp" // lalr1.cc:847
    break;

  case 58:
#line 234 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::SortedVarList_ptr > () -> push_back(yystack_[0].value.as< smtlib::SortedVar_ptr > ()); yylhs.value.as< smtlib::SortedVarList_ptr > () = yystack_[1].value.as< smtlib::SortedVarList_ptr > (); }
#line 1130 "parser.cpp" // lalr1.cc:847
    break;

  case 59:
#line 235 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortedVarList_ptr > () = new smtlib::SortedVarList(); yylhs.value.as< smtlib::SortedVarList_ptr > () -> push_back(yystack_[0].value.as< smtlib::SortedVar_ptr > ()); }
#line 1136 "parser.cpp" // lalr1.cc:847
    break;

  case 60:
#line 239 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortedVar_ptr > () = new smtlib::SortedVar(new smtlib::Primitive(yystack_[2].value.as< std::string > (), smtlib::Primitive::SYMBOL), yystack_[1].value.as< smtlib::Sort_ptr > ()); }
#line 1142 "parser.cpp" // lalr1.cc:847
    break;

  case 61:
#line 243 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::VarBindingList_ptr > () -> push_back(yystack_[0].value.as< smtlib::VarBinding_ptr > ()); yylhs.value.as< smtlib::VarBindingList_ptr > () = yystack_[1].value.as< smtlib::VarBindingList_ptr > (); }
#line 1148 "parser.cpp" // lalr1.cc:847
    break;

  case 62:
#line 244 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::VarBindingList_ptr > () = new smtlib::VarBindingList(); yylhs.value.as< smtlib::VarBindingList_ptr > () -> push_back(yystack_[0].value.as< smtlib::VarBinding_ptr > ()); }
#line 1154 "parser.cpp" // lalr1.cc:847
    break;

  case 63:
#line 248 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::VarBinding_ptr > () = new smtlib::VarBinding(new smtlib::Primitive(yystack_[2].value.as< std::string > (), smtlib::Primitive::SYMBOL), yystack_[1].value.as< smtlib::Term_ptr > ()); }
#line 1160 "parser.cpp" // lalr1.cc:847
    break;

  case 64:
#line 252 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::AsQualIdentifier(yystack_[2].value.as< smtlib::Identifier_ptr > (), yystack_[1].value.as< smtlib::Sort_ptr > ()); }
#line 1166 "parser.cpp" // lalr1.cc:847
    break;

  case 65:
#line 253 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::QualIdentifier(yystack_[0].value.as< smtlib::Identifier_ptr > ()); }
#line 1172 "parser.cpp" // lalr1.cc:847
    break;

  case 66:
#line 257 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Term_ptr > () = new smtlib::TermConstant(yystack_[0].value.as< smtlib::Primitive_ptr > ()); }
#line 1178 "parser.cpp" // lalr1.cc:847
    break;

  case 67:
#line 262 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::AttributeList_ptr > ()->push_back(yystack_[0].value.as< smtlib::Attribute_ptr > ()); yylhs.value.as< smtlib::AttributeList_ptr > () = yystack_[1].value.as< smtlib::AttributeList_ptr > (); }
#line 1184 "parser.cpp" // lalr1.cc:847
    break;

  case 68:
#line 263 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::AttributeList_ptr > () = new smtlib::AttributeList(); yylhs.value.as< smtlib::AttributeList_ptr > ()->push_back(yystack_[0].value.as< smtlib::Attribute_ptr > ()); }
#line 1190 "parser.cpp" // lalr1.cc:847
    break;

  case 69:
#line 267 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Attribute_ptr > () = new smtlib::Attribute(); }
#line 1196 "parser.cpp" // lalr1.cc:847
    break;

  case 70:
#line 268 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Attribute_ptr > () = new smtlib::Attribute(); }
#line 1202 "parser.cpp" // lalr1.cc:847
    break;

  case 72:
#line 273 "parser.ypp" // lalr1.cc:847
    { std::cout << yystack_[0].value.as< std::string > () << std::endl; }
#line 1208 "parser.cpp" // lalr1.cc:847
    break;

  case 74:
#line 280 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortList_ptr > () = yystack_[0].value.as< smtlib::SortList_ptr > (); }
#line 1214 "parser.cpp" // lalr1.cc:847
    break;

  case 75:
#line 281 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortList_ptr > () = nullptr; }
#line 1220 "parser.cpp" // lalr1.cc:847
    break;

  case 76:
#line 285 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::SortList_ptr > ()->push_back(yystack_[0].value.as< smtlib::Sort_ptr > ()); yylhs.value.as< smtlib::SortList_ptr > () = yystack_[1].value.as< smtlib::SortList_ptr > (); }
#line 1226 "parser.cpp" // lalr1.cc:847
    break;

  case 77:
#line 286 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::SortList_ptr > () = new smtlib::SortList(); yylhs.value.as< smtlib::SortList_ptr > ()->push_back(yystack_[0].value.as< smtlib::Sort_ptr > ()); }
#line 1232 "parser.cpp" // lalr1.cc:847
    break;

  case 78:
#line 290 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Sort_ptr > () = new smtlib::Sort(yystack_[2].value.as< smtlib::Identifier_ptr > (), yystack_[1].value.as< smtlib::SortList_ptr > ()); }
#line 1238 "parser.cpp" // lalr1.cc:847
    break;

  case 79:
#line 291 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Sort_ptr > () = new smtlib::Sort(yystack_[0].value.as< smtlib::Identifier_ptr > ()); }
#line 1244 "parser.cpp" // lalr1.cc:847
    break;

  case 80:
#line 292 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Sort_ptr > () = new smtlib::Sort(yystack_[0].value.as< smtlib::VarType_ptr > ()); }
#line 1250 "parser.cpp" // lalr1.cc:847
    break;

  case 81:
#line 296 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::VarType_ptr > () = new smtlib::TBool(); }
#line 1256 "parser.cpp" // lalr1.cc:847
    break;

  case 82:
#line 297 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::VarType_ptr > () = new smtlib::TInt(); }
#line 1262 "parser.cpp" // lalr1.cc:847
    break;

  case 83:
#line 298 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::VarType_ptr > () = new smtlib::TString(); }
#line 1268 "parser.cpp" // lalr1.cc:847
    break;

  case 84:
#line 304 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Identifier_ptr > () = new smtlib::Identifier(new smtlib::Primitive("_", ""), new smtlib::Primitive(yystack_[2].value.as< std::string > (), smtlib::Primitive::SYMBOL), yystack_[1].value.as< smtlib::NumeralList_ptr > ()); }
#line 1274 "parser.cpp" // lalr1.cc:847
    break;

  case 85:
#line 305 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Identifier_ptr > () = new smtlib::Identifier(new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::SYMBOL)); }
#line 1280 "parser.cpp" // lalr1.cc:847
    break;

  case 86:
#line 309 "parser.ypp" // lalr1.cc:847
    { yystack_[1].value.as< smtlib::NumeralList_ptr > () -> push_back(new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::SYMBOL)); yylhs.value.as< smtlib::NumeralList_ptr > () = yystack_[1].value.as< smtlib::NumeralList_ptr > (); }
#line 1286 "parser.cpp" // lalr1.cc:847
    break;

  case 87:
#line 310 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::NumeralList_ptr > () = new smtlib::NumeralList(); yylhs.value.as< smtlib::NumeralList_ptr > () -> push_back(new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::SYMBOL)); }
#line 1292 "parser.cpp" // lalr1.cc:847
    break;

  case 88:
#line 315 "parser.ypp" // lalr1.cc:847
    {  }
#line 1298 "parser.cpp" // lalr1.cc:847
    break;

  case 89:
#line 316 "parser.ypp" // lalr1.cc:847
    {  }
#line 1304 "parser.cpp" // lalr1.cc:847
    break;

  case 90:
#line 320 "parser.ypp" // lalr1.cc:847
    { }
#line 1310 "parser.cpp" // lalr1.cc:847
    break;

  case 91:
#line 321 "parser.ypp" // lalr1.cc:847
    {  }
#line 1316 "parser.cpp" // lalr1.cc:847
    break;

  case 92:
#line 325 "parser.ypp" // lalr1.cc:847
    {  }
#line 1322 "parser.cpp" // lalr1.cc:847
    break;

  case 93:
#line 326 "parser.ypp" // lalr1.cc:847
    {  }
#line 1328 "parser.cpp" // lalr1.cc:847
    break;

  case 94:
#line 327 "parser.ypp" // lalr1.cc:847
    {  }
#line 1334 "parser.cpp" // lalr1.cc:847
    break;

  case 95:
#line 328 "parser.ypp" // lalr1.cc:847
    {  }
#line 1340 "parser.cpp" // lalr1.cc:847
    break;

  case 96:
#line 332 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Primitive_ptr > () = new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::NUMERAL); }
#line 1346 "parser.cpp" // lalr1.cc:847
    break;

  case 97:
#line 333 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Primitive_ptr > () = new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::DECIMAL); }
#line 1352 "parser.cpp" // lalr1.cc:847
    break;

  case 98:
#line 334 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Primitive_ptr > () = new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::HEXADECIMAL); }
#line 1358 "parser.cpp" // lalr1.cc:847
    break;

  case 99:
#line 335 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Primitive_ptr > () = new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::BINARY); }
#line 1364 "parser.cpp" // lalr1.cc:847
    break;

  case 100:
#line 336 "parser.ypp" // lalr1.cc:847
    { yylhs.value.as< smtlib::Primitive_ptr > () = new smtlib::Primitive(yystack_[0].value.as< std::string > (), smtlib::Primitive::STRING); }
#line 1370 "parser.cpp" // lalr1.cc:847
    break;


#line 1374 "parser.cpp" // lalr1.cc:847
            default:
              break;
            }
        }
      catch (const syntax_error& yyexc)
        {
          error (yyexc);
          YYERROR;
        }
      YY_SYMBOL_PRINT ("-> $$ =", yylhs);
      yypop_ (yylen);
      yylen = 0;
      YY_STACK_PRINT ();

      // Shift the result of the reduction.
      yypush_ (YY_NULLPTR, yylhs);
    }
    goto yynewstate;

  /*--------------------------------------.
  | yyerrlab -- here on detecting error.  |
  `--------------------------------------*/
  yyerrlab:
    // If not already recovering from an error, report this error.
    if (!yyerrstatus_)
      {
        ++yynerrs_;
        error (yyla.location, yysyntax_error_ (yystack_[0].state,
                                           yyempty ? yyempty_ : yyla.type_get ()));
      }


    yyerror_range[1].location = yyla.location;
    if (yyerrstatus_ == 3)
      {
        /* If just tried and failed to reuse lookahead token after an
           error, discard it.  */

        // Return failure if at end of input.
        if (yyla.type_get () == yyeof_)
          YYABORT;
        else if (!yyempty)
          {
            yy_destroy_ ("Error: discarding", yyla);
            yyempty = true;
          }
      }

    // Else will try to reuse lookahead token after shifting the error token.
    goto yyerrlab1;


  /*---------------------------------------------------.
  | yyerrorlab -- error raised explicitly by YYERROR.  |
  `---------------------------------------------------*/
  yyerrorlab:

    /* Pacify compilers like GCC when the user code never invokes
       YYERROR and the label yyerrorlab therefore never appears in user
       code.  */
    if (false)
      goto yyerrorlab;
    yyerror_range[1].location = yystack_[yylen - 1].location;
    /* Do not reclaim the symbols of the rule whose action triggered
       this YYERROR.  */
    yypop_ (yylen);
    yylen = 0;
    goto yyerrlab1;

  /*-------------------------------------------------------------.
  | yyerrlab1 -- common code for both syntax error and YYERROR.  |
  `-------------------------------------------------------------*/
  yyerrlab1:
    yyerrstatus_ = 3;   // Each real token shifted decrements this.
    {
      stack_symbol_type error_token;
      for (;;)
        {
          yyn = yypact_[yystack_[0].state];
          if (!yy_pact_value_is_default_ (yyn))
            {
              yyn += yyterror_;
              if (0 <= yyn && yyn <= yylast_ && yycheck_[yyn] == yyterror_)
                {
                  yyn = yytable_[yyn];
                  if (0 < yyn)
                    break;
                }
            }

          // Pop the current state because it cannot handle the error token.
          if (yystack_.size () == 1)
            YYABORT;

          yyerror_range[1].location = yystack_[0].location;
          yy_destroy_ ("Error: popping", yystack_[0]);
          yypop_ ();
          YY_STACK_PRINT ();
        }

      yyerror_range[2].location = yyla.location;
      YYLLOC_DEFAULT (error_token.location, yyerror_range, 2);

      // Shift the error token.
      error_token.state = yyn;
      yypush_ ("Shifting", error_token);
    }
    goto yynewstate;

    // Accept.
  yyacceptlab:
    yyresult = 0;
    goto yyreturn;

    // Abort.
  yyabortlab:
    yyresult = 1;
    goto yyreturn;

  yyreturn:
    if (!yyempty)
      yy_destroy_ ("Cleanup: discarding lookahead", yyla);

    /* Do not reclaim the symbols of the rule whose action triggered
       this YYABORT or YYACCEPT.  */
    yypop_ (yylen);
    while (1 < yystack_.size ())
      {
        yy_destroy_ ("Cleanup: popping", yystack_[0]);
        yypop_ ();
      }

    return yyresult;
  }
    catch (...)
      {
        YYCDEBUG << "Exception caught: cleaning lookahead and stack"
                 << std::endl;
        // Do not try to display the values of the reclaimed symbols,
        // as their printer might throw an exception.
        if (!yyempty)
          yy_destroy_ (YY_NULLPTR, yyla);

        while (1 < yystack_.size ())
          {
            yy_destroy_ (YY_NULLPTR, yystack_[0]);
            yypop_ ();
          }
        throw;
      }
  }

  void
   Parser ::error (const syntax_error& yyexc)
  {
    error (yyexc.location, yyexc.what());
  }

  // Generate an error message.
  std::string
   Parser ::yysyntax_error_ (state_type yystate, symbol_number_type yytoken) const
  {
    std::string yyres;
    // Number of reported tokens (one for the "unexpected", one per
    // "expected").
    size_t yycount = 0;
    // Its maximum.
    enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
    // Arguments of yyformat.
    char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];

    /* There are many possibilities here to consider:
       - If this state is a consistent state with a default action, then
         the only way this function was invoked is if the default action
         is an error action.  In that case, don't check for expected
         tokens because there are none.
       - The only way there can be no lookahead present (in yytoken) is
         if this state is a consistent state with a default action.
         Thus, detecting the absence of a lookahead is sufficient to
         determine that there is no unexpected or expected token to
         report.  In that case, just report a simple "syntax error".
       - Don't assume there isn't a lookahead just because this state is
         a consistent state with a default action.  There might have
         been a previous inconsistent state, consistent state with a
         non-default action, or user semantic action that manipulated
         yyla.  (However, yyla is currently not documented for users.)
       - Of course, the expected token list depends on states to have
         correct lookahead information, and it depends on the parser not
         to perform extra reductions after fetching a lookahead from the
         scanner and before detecting a syntax error.  Thus, state
         merging (from LALR or IELR) and default reductions corrupt the
         expected token list.  However, the list is correct for
         canonical LR with one exception: it will still contain any
         token that will not be accepted due to an error action in a
         later state.
    */
    if (yytoken != yyempty_)
      {
        yyarg[yycount++] = yytname_[yytoken];
        int yyn = yypact_[yystate];
        if (!yy_pact_value_is_default_ (yyn))
          {
            /* Start YYX at -YYN if negative to avoid negative indexes in
               YYCHECK.  In other words, skip the first -YYN actions for
               this state because they are default actions.  */
            int yyxbegin = yyn < 0 ? -yyn : 0;
            // Stay within bounds of both yycheck and yytname.
            int yychecklim = yylast_ - yyn + 1;
            int yyxend = yychecklim < yyntokens_ ? yychecklim : yyntokens_;
            for (int yyx = yyxbegin; yyx < yyxend; ++yyx)
              if (yycheck_[yyx + yyn] == yyx && yyx != yyterror_
                  && !yy_table_value_is_error_ (yytable_[yyx + yyn]))
                {
                  if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                    {
                      yycount = 1;
                      break;
                    }
                  else
                    yyarg[yycount++] = yytname_[yyx];
                }
          }
      }

    char const* yyformat = YY_NULLPTR;
    switch (yycount)
      {
#define YYCASE_(N, S)                         \
        case N:                               \
          yyformat = S;                       \
        break
        YYCASE_(0, YY_("syntax error"));
        YYCASE_(1, YY_("syntax error, unexpected %s"));
        YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
        YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
        YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
        YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
      }

    // Argument number.
    size_t yyi = 0;
    for (char const* yyp = yyformat; *yyp; ++yyp)
      if (yyp[0] == '%' && yyp[1] == 's' && yyi < yycount)
        {
          yyres += yytnamerr_ (yyarg[yyi++]);
          ++yyp;
        }
      else
        yyres += *yyp;
    return yyres;
  }


  const short int  Parser ::yypact_ninf_ = -131;

  const signed char  Parser ::yytable_ninf_ = -1;

  const short int
   Parser ::yypact_[] =
  {
    -131,    18,    13,  -131,   249,  -131,   216,    19,   -28,   -25,
     -24,   -16,    31,    37,    39,    -8,    -4,    75,    77,   216,
      28,    34,    29,    38,    38,   152,  -131,  -131,  -131,  -131,
    -131,  -131,    97,  -131,  -131,  -131,  -131,  -131,    81,    49,
     114,   116,  -131,  -131,  -131,  -131,   117,   118,  -131,  -131,
       1,  -131,   121,   133,   134,   223,   135,   136,  -131,    -5,
     216,    64,    16,   138,   139,   140,   216,   216,   216,   216,
     216,   216,   216,   216,   216,   216,   216,   216,   216,   216,
     216,   216,   216,  -131,   181,   142,   144,    92,  -131,  -131,
    -131,  -131,  -131,  -131,  -131,    80,  -131,  -131,  -131,  -131,
    -131,    38,    95,   145,   181,   144,   144,   147,    44,   148,
     141,   216,   216,   216,   216,   216,   216,   216,   177,   195,
     202,   216,   150,   178,   209,    14,  -131,  -131,  -131,   179,
     181,  -131,  -131,  -131,  -131,   100,   182,   144,  -131,  -131,
     190,   129,    80,  -131,  -131,   196,    80,  -131,  -131,    25,
    -131,  -131,    23,   197,     6,     8,   146,    11,  -131,  -131,
    -131,  -131,   199,   203,   210,   211,   212,   213,   214,   216,
    -131,  -131,  -131,   217,  -131,  -131,  -131,   181,   181,  -131,
     181,   181,  -131,   181,  -131,   218,  -131,  -131,  -131,  -131,
    -131,  -131,  -131,   216,   216,   216,   216,  -131,  -131,  -131,
    -131,  -131,  -131,  -131,  -131,   219,  -131,    30,   220,   221,
     216,   226,  -131,   230,   231,   232,   234,  -131,  -131,  -131,
    -131,   235,  -131,  -131,  -131,  -131,  -131,  -131
  };

  const unsigned char
   Parser ::yydefact_[] =
  {
       4,     0,     2,     1,     0,     3,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    99,    97,    98,    96,
     100,    85,     0,    54,    55,    65,    66,    15,     0,     0,
       0,     0,    23,    16,    20,    25,     0,     0,    17,    18,
       0,    31,     0,     0,     0,    70,     0,     0,    24,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,    14,    75,     0,    57,    27,    22,    21,
      19,    30,    13,    12,     5,    89,    72,    69,    73,     7,
       6,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,    81,    82,    83,     0,
      74,    77,    80,    79,     8,     0,     0,    56,    59,    29,
       0,    26,    89,    93,    94,     0,    88,    91,    95,     0,
      68,    87,     0,     0,     0,     0,     0,     0,    62,    36,
      37,    38,     0,     0,     0,     0,     0,     0,     0,     0,
      47,    48,    49,     0,    51,    52,    53,     0,     0,    76,
       0,     0,    58,     0,    28,     0,    71,    90,    32,    67,
      84,    86,    64,     0,     0,     0,     0,    61,    39,    40,
      41,    42,    43,    44,    45,     0,    50,     0,     0,     0,
       0,     0,    92,     0,     0,     0,     0,    46,    78,    10,
      60,     0,     9,    33,    34,    63,    35,    11
  };

  const short int
   Parser ::yypgoto_[] =
  {
    -131,  -131,  -131,  -131,  -131,  -131,  -131,  -131,   -40,    -6,
    -131,   -84,  -130,  -131,    63,   215,  -131,  -131,   -21,  -131,
    -131,    65,   -91,  -131,   -54,  -131,    99,  -131,    98,   -49
  };

  const short int
   Parser ::yydefgoto_[] =
  {
      -1,     1,     2,     5,    57,    46,   140,   141,    50,    51,
     136,   137,   138,   157,   158,    33,    34,   149,    56,    97,
     129,   130,   131,   132,    35,   152,   145,   146,   147,    36
  };

  const unsigned char
   Parser ::yytable_[] =
  {
      32,    61,    62,    58,    25,    90,    98,   182,   104,   135,
     193,   135,   194,   153,   156,   196,     4,   103,     3,   103,
      61,   154,   155,    37,   182,   182,   108,   190,    38,   188,
     133,    39,    40,   125,   218,    42,   118,   119,   120,   179,
      41,    43,   124,    44,    91,    45,   148,    25,   159,    47,
     133,    26,    27,    28,   101,    29,    30,    31,   126,   127,
     128,   109,   110,   111,   112,   113,   114,   115,   116,   117,
      31,   177,    31,   121,   122,   123,   133,   191,    55,    48,
     150,    49,    52,   142,    84,    54,    31,   208,    53,   209,
     210,    55,   211,   148,    26,    27,    28,   148,    29,    30,
      31,    83,    91,    85,   162,   163,   164,   165,   166,   167,
     168,   169,    91,    91,    91,   173,   179,    86,    91,    87,
     102,    88,    89,   133,   133,    92,   133,   133,   189,   133,
      26,    27,    28,   143,    29,    30,   144,    93,    94,    99,
     100,   105,   106,   107,    25,   161,   134,   135,   139,   151,
     156,    61,   160,   133,   174,    59,   180,    60,    61,    62,
      63,    64,    65,   205,    66,    67,    68,    69,    70,    71,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      25,   170,   175,   178,   125,   184,   181,   213,   214,   215,
     216,    26,    27,    28,   183,    29,    30,    31,    25,   171,
     186,   192,   195,   198,   221,    25,   172,   199,    31,   126,
     127,   128,    25,   176,   200,   201,   202,   203,   204,    25,
     197,   206,   212,   217,   219,   220,    95,    26,    27,    28,
     222,    29,    30,    31,   223,   224,   225,    31,   226,   227,
      82,   185,   207,     0,   187,    26,    27,    28,     0,    29,
      30,    31,    26,    27,    28,     0,    29,    30,    31,    26,
      27,    28,     0,    29,    30,    31,    26,    27,    28,     0,
      29,    30,    31,    26,    27,    28,     0,    29,    30,    96,
       6,     7,     8,     9,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24
  };

  const short int
   Parser ::yycheck_[] =
  {
       6,     6,     7,    24,     3,     4,    55,   137,    62,     3,
       4,     3,     4,   104,     3,     4,     3,     3,     0,     3,
       6,   105,   106,     4,   154,   155,    66,     4,    56,     4,
      84,    56,    56,     3,     4,     4,    76,    77,    78,   130,
      56,     4,    82,     4,    50,    53,    95,     3,     4,    53,
     104,    50,    51,    52,    60,    54,    55,    56,    28,    29,
      30,    67,    68,    69,    70,    71,    72,    73,    74,    75,
      56,   125,    56,    79,    80,    81,   130,    54,    53,     4,
     101,     4,    54,     3,     3,    56,    56,   178,    54,   180,
     181,    53,   183,   142,    50,    51,    52,   146,    54,    55,
      56,     4,   108,    54,   110,   111,   112,   113,   114,   115,
     116,   117,   118,   119,   120,   121,   207,     3,   124,     3,
      56,     4,     4,   177,   178,     4,   180,   181,   149,   183,
      50,    51,    52,    53,    54,    55,    56,     4,     4,     4,
       4,     3,     3,     3,     3,     4,     4,     3,    56,    54,
       3,     6,     4,   207,     4,     3,    56,     5,     6,     7,
       8,     9,    10,   169,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
       3,     4,     4,     4,     3,    56,     4,   193,   194,   195,
     196,    50,    51,    52,     4,    54,    55,    56,     3,     4,
       4,     4,    56,     4,   210,     3,     4,     4,    56,    28,
      29,    30,     3,     4,     4,     4,     4,     4,     4,     3,
     157,     4,     4,     4,     4,     4,     3,    50,    51,    52,
       4,    54,    55,    56,     4,     4,     4,    56,     4,     4,
      25,   142,   177,    -1,   146,    50,    51,    52,    -1,    54,
      55,    56,    50,    51,    52,    -1,    54,    55,    56,    50,
      51,    52,    -1,    54,    55,    56,    50,    51,    52,    -1,
      54,    55,    56,    50,    51,    52,    -1,    54,    55,    56,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49
  };

  const unsigned char
   Parser ::yystos_[] =
  {
       0,    58,    59,     0,     3,    60,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,     3,    50,    51,    52,    54,
      55,    56,    66,    72,    73,    81,    86,     4,    56,    56,
      56,    56,     4,     4,     4,    53,    62,    53,     4,     4,
      65,    66,    54,    54,    56,    53,    75,    61,    75,     3,
       5,     6,     7,     8,     9,    10,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    72,     4,     3,    54,     3,     3,     4,     4,
       4,    66,     4,     4,     4,     3,    56,    76,    86,     4,
       4,    66,    56,     3,    81,     3,     3,     3,    65,    66,
      66,    66,    66,    66,    66,    66,    66,    66,    65,    65,
      65,    66,    66,    66,    65,     3,    28,    29,    30,    77,
      78,    79,    80,    81,     4,     3,    67,    68,    69,    56,
      63,    64,     3,    53,    56,    83,    84,    85,    86,    74,
      75,    54,    82,    79,    68,    68,     3,    70,    71,     4,
       4,     4,    66,    66,    66,    66,    66,    66,    66,    66,
       4,     4,     4,    66,     4,     4,     4,    81,     4,    79,
      56,     4,    69,     4,    56,    83,     4,    85,     4,    75,
       4,    54,     4,     4,     4,    56,     4,    71,     4,     4,
       4,     4,     4,     4,     4,    66,     4,    78,    79,    79,
      79,    79,     4,    66,    66,    66,    66,     4,     4,     4,
       4,    66,     4,     4,     4,     4,     4,     4
  };

  const unsigned char
   Parser ::yyr1_[] =
  {
       0,    57,    58,    59,    59,    60,    60,    60,    60,    60,
      60,    60,    60,    60,    60,    60,    60,    60,    60,    60,
      60,    60,    60,    60,    61,    62,    63,    63,    64,    64,
      65,    65,    66,    66,    66,    66,    66,    66,    66,    66,
      66,    66,    66,    66,    66,    66,    66,    66,    66,    66,
      66,    66,    66,    66,    66,    66,    67,    67,    68,    68,
      69,    70,    70,    71,    72,    72,    73,    74,    74,    75,
      75,    76,    76,    76,    77,    77,    78,    78,    79,    79,
      79,    80,    80,    80,    81,    81,    82,    82,    83,    83,
      84,    84,    85,    85,    85,    85,    86,    86,    86,    86,
      86
  };

  const unsigned char
   Parser ::yyr2_[] =
  {
       0,     2,     1,     2,     0,     4,     4,     4,     5,     8,
       8,     9,     4,     4,     4,     3,     3,     3,     3,     4,
       3,     4,     4,     3,     1,     1,     1,     0,     2,     1,
       2,     1,     5,     7,     7,     7,     4,     4,     4,     5,
       5,     5,     5,     5,     5,     5,     6,     4,     4,     4,
       5,     4,     4,     4,     1,     1,     1,     0,     2,     1,
       4,     2,     1,     4,     5,     1,     1,     2,     1,     2,
       1,     3,     1,     1,     1,     0,     2,     1,     4,     1,
       1,     1,     1,     1,     5,     1,     2,     1,     1,     0,
       2,     1,     3,     1,     1,     1,     1,     1,     1,     1,
       1
  };



  // YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
  // First, the terminals, then, starting at \a yyntokens_, nonterminals.
  const char*
  const  Parser ::yytname_[] =
  {
  "\"end of file\"", "error", "$undefined", "\"(\"", "\")\"", "\"!\"",
  "\"_\"", "\"as\"", "\"exists\"", "\"forall\"", "\"let\"", "\"par\"",
  "\"and\"", "\"not\"", "\"-\"", "\"+\"", "\"=\"", "\">\"", "\">=\"",
  "\"<\"", "\"<=\"", "\"ite\"", "\"re.++\"", "\"re.or\"", "\"str.++\"",
  "\"str.in.re\"", "\"str.len\"", "\"str.to.re\"", "\"TBool\"", "\"TInt\"",
  "\"TString\"", "\"assert\"", "\"check-sat\"", "\"declare-fun\"",
  "\"declare-sort\"", "\"define-fun\"", "\"define-sort\"", "\"exit\"",
  "\"get-assertions\"", "\"get-assignment\"", "\"get-info\"",
  "\"get-option\"", "\"get-proof\"", "\"get-unsat-core\"", "\"get-value\"",
  "\"pop\"", "\"push\"", "\"set-logic\"", "\"set-info\"", "\"set-option\"",
  "\"binary\"", "\"decimal\"", "\"hexadecimal\"", "\"keyword\"",
  "\"number\"", "\"string\"", "\"symbol\"", "$accept", "script",
  "command_list", "command", "option", "info_flag", "symbol_list",
  "symbol_list_", "term_list_", "term", "sorted_var_list",
  "sorted_var_list_", "sorted_var", "var_binding_list_", "var_binding",
  "qual_identifier", "term_constant", "attribute_list_", "attribute",
  "attribute_value", "sort_list", "sort_list_", "sort", "var_type",
  "identifier", "numeral_list_", "s_expr_list", "s_expr_list_", "s_expr",
  "spec_constant", YY_NULLPTR
  };

#if YYDEBUG
  const unsigned short int
   Parser ::yyrline_[] =
  {
       0,   140,   140,   144,   145,   149,   150,   151,   152,   153,
     154,   155,   156,   157,   158,   159,   160,   161,   162,   163,
     164,   165,   166,   167,   171,   175,   179,   180,   184,   185,
     197,   198,   202,   203,   204,   205,   206,   207,   208,   209,
     210,   211,   212,   213,   214,   215,   216,   217,   218,   219,
     220,   221,   222,   223,   224,   225,   229,   230,   234,   235,
     239,   243,   244,   248,   252,   253,   257,   262,   263,   267,
     268,   272,   273,   274,   280,   281,   285,   286,   290,   291,
     292,   296,   297,   298,   304,   305,   309,   310,   315,   316,
     320,   321,   325,   326,   327,   328,   332,   333,   334,   335,
     336
  };

  // Print the state stack on the debug stream.
  void
   Parser ::yystack_print_ ()
  {
    *yycdebug_ << "Stack now";
    for (stack_type::const_iterator
           i = yystack_.begin (),
           i_end = yystack_.end ();
         i != i_end; ++i)
      *yycdebug_ << ' ' << i->state;
    *yycdebug_ << std::endl;
  }

  // Report on the debug stream that the rule \a yyrule is going to be reduced.
  void
   Parser ::yy_reduce_print_ (int yyrule)
  {
    unsigned int yylno = yyrline_[yyrule];
    int yynrhs = yyr2_[yyrule];
    // Print the symbols being reduced, and their result.
    *yycdebug_ << "Reducing stack by rule " << yyrule - 1
               << " (line " << yylno << "):" << std::endl;
    // The symbols being reduced.
    for (int yyi = 0; yyi < yynrhs; yyi++)
      YY_SYMBOL_PRINT ("   $" << yyi + 1 << " =",
                       yystack_[(yynrhs) - (yyi + 1)]);
  }
#endif // YYDEBUG


#line 9 "parser.ypp" // lalr1.cc:1155
} //  Vlab 
#line 1912 "parser.cpp" // lalr1.cc:1155
#line 344 "parser.ypp" // lalr1.cc:1156


void
Vlab::Parser::error (const location_type& l,
                          const std::string& m)
{
  std::cerr << l << ": " << m << std::endl;
}
