// A Bison parser, made by GNU Bison 3.0.2.

// Skeleton interface for Bison LALR(1) parsers in C++

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

/**
 ** \file y.tab.h
 ** Define the  Vlab ::parser class.
 */

// C++ LALR(1) parser skeleton written by Akim Demaille.

#ifndef YY_YY_PARSER_HPP_INCLUDED
# define YY_YY_PARSER_HPP_INCLUDED
// //                    "%code requires" blocks.
#line 12 "parser.ypp" // lalr1.cc:372

#include <string>
#include <cstdlib>

#include "../smt/ast.h"

  namespace Vlab  {
    class Scanner;
  }
	namespace smtlib = Vlab::SMT;

#line 56 "parser.hpp" // lalr1.cc:372

# include <cassert>
# include <vector>
# include <iostream>
# include <stdexcept>
# include <string>
# include "stack.hh"
# include "location.hh"
#include <typeinfo>
#ifndef YYASSERT
# include <cassert>
# define YYASSERT assert
#endif


#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 1
#endif

#line 9 "parser.ypp" // lalr1.cc:372
namespace  Vlab  {
#line 132 "parser.hpp" // lalr1.cc:372



  /// A char[S] buffer to store and retrieve objects.
  ///
  /// Sort of a variant, but does not keep track of the nature
  /// of the stored data, since that knowledge is available
  /// via the current state.
  template <size_t S>
  struct variant
  {
    /// Type of *this.
    typedef variant<S> self_type;

    /// Empty construction.
    variant ()
      : yytname_ (YY_NULLPTR)
    {}

    /// Construct and fill.
    template <typename T>
    variant (const T& t)
      : yytname_ (typeid (T).name ())
    {
      YYASSERT (sizeof (T) <= S);
      new (yyas_<T> ()) T (t);
    }

    /// Destruction, allowed only if empty.
    ~variant ()
    {
      YYASSERT (!yytname_);
    }

    /// Instantiate an empty \a T in here.
    template <typename T>
    T&
    build ()
    {
      YYASSERT (!yytname_);
      YYASSERT (sizeof (T) <= S);
      yytname_ = typeid (T).name ();
      return *new (yyas_<T> ()) T;
    }

    /// Instantiate a \a T in here from \a t.
    template <typename T>
    T&
    build (const T& t)
    {
      YYASSERT (!yytname_);
      YYASSERT (sizeof (T) <= S);
      yytname_ = typeid (T).name ();
      return *new (yyas_<T> ()) T (t);
    }

    /// Accessor to a built \a T.
    template <typename T>
    T&
    as ()
    {
      YYASSERT (yytname_ == typeid (T).name ());
      YYASSERT (sizeof (T) <= S);
      return *yyas_<T> ();
    }

    /// Const accessor to a built \a T (for %printer).
    template <typename T>
    const T&
    as () const
    {
      YYASSERT (yytname_ == typeid (T).name ());
      YYASSERT (sizeof (T) <= S);
      return *yyas_<T> ();
    }

    /// Swap the content with \a other, of same type.
    ///
    /// Both variants must be built beforehand, because swapping the actual
    /// data requires reading it (with as()), and this is not possible on
    /// unconstructed variants: it would require some dynamic testing, which
    /// should not be the variant's responsability.
    /// Swapping between built and (possibly) non-built is done with
    /// variant::move ().
    template <typename T>
    void
    swap (self_type& other)
    {
      YYASSERT (yytname_);
      YYASSERT (yytname_ == other.yytname_);
      std::swap (as<T> (), other.as<T> ());
    }

    /// Move the content of \a other to this.
    ///
    /// Destroys \a other.
    template <typename T>
    void
    move (self_type& other)
    {
      build<T> ();
      swap<T> (other);
      other.destroy<T> ();
    }

    /// Copy the content of \a other to this.
    template <typename T>
    void
    copy (const self_type& other)
    {
      build<T> (other.as<T> ());
    }

    /// Destroy the stored \a T.
    template <typename T>
    void
    destroy ()
    {
      as<T> ().~T ();
      yytname_ = YY_NULLPTR;
    }

  private:
    /// Prohibit blind copies.
    self_type& operator=(const self_type&);
    variant (const self_type&);

    /// Accessor to raw memory as \a T.
    template <typename T>
    T*
    yyas_ ()
    {
      void *yyp = yybuffer_.yyraw;
      return static_cast<T*> (yyp);
     }

    /// Const accessor to raw memory as \a T.
    template <typename T>
    const T*
    yyas_ () const
    {
      const void *yyp = yybuffer_.yyraw;
      return static_cast<const T*> (yyp);
     }

    union
    {
      /// Strongest alignment constraints.
      long double yyalign_me;
      /// A buffer large enough to store any of the semantic values.
      char yyraw[S];
    } yybuffer_;

    /// Whether the content is built: if defined, the name of the stored type.
    const char *yytname_;
  };


  /// A Bison parser.
  class  Parser 
  {
  public:
#ifndef YYSTYPE
    /// An auxiliary type to compute the largest semantic type.
    union union_type
    {
      // attribute_list_
      char dummy1[sizeof(smtlib::AttributeList_ptr)];

      // attribute
      char dummy2[sizeof(smtlib::Attribute_ptr)];

      // command_list
      char dummy3[sizeof(smtlib::CommandList_ptr)];

      // command
      char dummy4[sizeof(smtlib::Command_ptr)];

      // identifier
      char dummy5[sizeof(smtlib::Identifier_ptr)];

      // numeral_list_
      char dummy6[sizeof(smtlib::NumeralList_ptr)];

      // spec_constant
      char dummy7[sizeof(smtlib::Primitive_ptr)];

      // sort_list
      // sort_list_
      char dummy8[sizeof(smtlib::SortList_ptr)];

      // sort
      char dummy9[sizeof(smtlib::Sort_ptr)];

      // sorted_var_list
      // sorted_var_list_
      char dummy10[sizeof(smtlib::SortedVarList_ptr)];

      // sorted_var
      char dummy11[sizeof(smtlib::SortedVar_ptr)];

      // term_list_
      char dummy12[sizeof(smtlib::TermList_ptr)];

      // term
      // qual_identifier
      // term_constant
      char dummy13[sizeof(smtlib::Term_ptr)];

      // var_binding_list_
      char dummy14[sizeof(smtlib::VarBindingList_ptr)];

      // var_binding
      char dummy15[sizeof(smtlib::VarBinding_ptr)];

      // var_type
      char dummy16[sizeof(smtlib::VarType_ptr)];

      // "binary"
      // "decimal"
      // "hexadecimal"
      // "keyword"
      // "number"
      // "string"
      // "symbol"
      char dummy17[sizeof(std::string)];
};

    /// Symbol semantic values.
    typedef variant<sizeof(union_type)> semantic_type;
#else
    typedef YYSTYPE semantic_type;
#endif
    /// Symbol locations.
    typedef location location_type;

    /// Syntax errors thrown from user actions.
    struct syntax_error : std::runtime_error
    {
      syntax_error (const location_type& l, const std::string& m);
      location_type location;
    };

    /// Tokens.
    struct token
    {
      enum yytokentype
      {
        TOK_END = 0,
        TOK_PAREN_O = 258,
        TOK_PAREN_C = 259,
        TOK_BANG = 260,
        TOK_UNDERSCORE = 261,
        TOK_AS = 262,
        TOK_EXISTS = 263,
        TOK_FORALL = 264,
        TOK_LET = 265,
        TOK_PAR = 266,
        TOK_AND = 267,
        TOK_NOT = 268,
        TOK_MINUS = 269,
        TOK_PLUS = 270,
        TOK_EQ = 271,
        TOK_GT = 272,
        TOK_GE = 273,
        TOK_LT = 274,
        TOK_LE = 275,
        TOK_ITE = 276,
        TOK_RE_CONCAT = 277,
        TOK_RE_OR = 278,
        TOK_CONCAT = 279,
        TOK_IN = 280,
        TOK_LEN = 281,
        TOK_TO_REGEX = 282,
        TOK_TBOOL = 283,
        TOK_TINT = 284,
        TOK_TSTRING = 285,
        TOK_ASSERT = 286,
        TOK_CHECK_SAT = 287,
        TOK_DECLARE_FUN = 288,
        TOK_DECLARE_SORT = 289,
        TOK_DEFINE_FUN = 290,
        TOK_DEFINE_SORT = 291,
        TOK_EXIT = 292,
        TOK_GET_ASSERTIONS = 293,
        TOK_GET_ASSIGNMENT = 294,
        TOK_GET_INFO = 295,
        TOK_GET_OPTION = 296,
        TOK_GET_PROOF = 297,
        TOK_GET_UNSAT_CORE = 298,
        TOK_GET_VALUE = 299,
        TOK_POP = 300,
        TOK_PUSH = 301,
        TOK_SET_LOGIC = 302,
        TOK_SET_INFO = 303,
        TOK_SET_OPTION = 304,
        TOK_BINARY = 305,
        TOK_DECIMAL = 306,
        TOK_HEXADECIMAL = 307,
        TOK_KEYWORD = 308,
        TOK_NUMERAL = 309,
        TOK_STRING = 310,
        TOK_SYMBOL = 311
      };
    };

    /// (External) token type, as returned by yylex.
    typedef token::yytokentype token_type;

    /// Internal symbol number.
    typedef int symbol_number_type;

    /// Internal symbol number for tokens (subsumed by symbol_number_type).
    typedef unsigned char token_number_type;

    /// A complete symbol.
    ///
    /// Expects its Base type to provide access to the symbol type
    /// via type_get().
    ///
    /// Provide access to semantic value and location.
    template <typename Base>
    struct basic_symbol : Base
    {
      /// Alias to Base.
      typedef Base super_type;

      /// Default constructor.
      basic_symbol ();

      /// Copy constructor.
      basic_symbol (const basic_symbol& other);

      /// Constructor for valueless symbols, and symbols from each type.

  basic_symbol (typename Base::kind_type t, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::AttributeList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::Attribute_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::CommandList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::Command_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::Identifier_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::NumeralList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::Primitive_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::SortList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::Sort_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::SortedVarList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::SortedVar_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::TermList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::Term_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::VarBindingList_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::VarBinding_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const smtlib::VarType_ptr v, const location_type& l);

  basic_symbol (typename Base::kind_type t, const std::string v, const location_type& l);


      /// Constructor for symbols with semantic value.
      basic_symbol (typename Base::kind_type t,
                    const semantic_type& v,
                    const location_type& l);

      ~basic_symbol ();

      /// Destructive move, \a s is emptied into this.
      void move (basic_symbol& s);

      /// The semantic value.
      semantic_type value;

      /// The location.
      location_type location;

    private:
      /// Assignment operator.
      basic_symbol& operator= (const basic_symbol& other);
    };

    /// Type access provider for token (enum) based symbols.
    struct by_type
    {
      /// Default constructor.
      by_type ();

      /// Copy constructor.
      by_type (const by_type& other);

      /// The symbol type as needed by the constructor.
      typedef token_type kind_type;

      /// Constructor from (external) token numbers.
      by_type (kind_type t);

      /// Steal the symbol type from \a that.
      void move (by_type& that);

      /// The (internal) type number (corresponding to \a type).
      /// -1 when this symbol is empty.
      symbol_number_type type_get () const;

      /// The token.
      token_type token () const;

      enum { empty = 0 };

      /// The symbol type.
      /// -1 when this symbol is empty.
      token_number_type type;
    };

    /// "External" symbols: returned by the scanner.
    typedef basic_symbol<by_type> symbol_type;

    // Symbol constructors declarations.
    static inline
    symbol_type
    make_END (const location_type& l);

    static inline
    symbol_type
    make_PAREN_O (const location_type& l);

    static inline
    symbol_type
    make_PAREN_C (const location_type& l);

    static inline
    symbol_type
    make_BANG (const location_type& l);

    static inline
    symbol_type
    make_UNDERSCORE (const location_type& l);

    static inline
    symbol_type
    make_AS (const location_type& l);

    static inline
    symbol_type
    make_EXISTS (const location_type& l);

    static inline
    symbol_type
    make_FORALL (const location_type& l);

    static inline
    symbol_type
    make_LET (const location_type& l);

    static inline
    symbol_type
    make_PAR (const location_type& l);

    static inline
    symbol_type
    make_AND (const location_type& l);

    static inline
    symbol_type
    make_NOT (const location_type& l);

    static inline
    symbol_type
    make_MINUS (const location_type& l);

    static inline
    symbol_type
    make_PLUS (const location_type& l);

    static inline
    symbol_type
    make_EQ (const location_type& l);

    static inline
    symbol_type
    make_GT (const location_type& l);

    static inline
    symbol_type
    make_GE (const location_type& l);

    static inline
    symbol_type
    make_LT (const location_type& l);

    static inline
    symbol_type
    make_LE (const location_type& l);

    static inline
    symbol_type
    make_ITE (const location_type& l);

    static inline
    symbol_type
    make_RE_CONCAT (const location_type& l);

    static inline
    symbol_type
    make_RE_OR (const location_type& l);

    static inline
    symbol_type
    make_CONCAT (const location_type& l);

    static inline
    symbol_type
    make_IN (const location_type& l);

    static inline
    symbol_type
    make_LEN (const location_type& l);

    static inline
    symbol_type
    make_TO_REGEX (const location_type& l);

    static inline
    symbol_type
    make_TBOOL (const location_type& l);

    static inline
    symbol_type
    make_TINT (const location_type& l);

    static inline
    symbol_type
    make_TSTRING (const location_type& l);

    static inline
    symbol_type
    make_ASSERT (const location_type& l);

    static inline
    symbol_type
    make_CHECK_SAT (const location_type& l);

    static inline
    symbol_type
    make_DECLARE_FUN (const location_type& l);

    static inline
    symbol_type
    make_DECLARE_SORT (const location_type& l);

    static inline
    symbol_type
    make_DEFINE_FUN (const location_type& l);

    static inline
    symbol_type
    make_DEFINE_SORT (const location_type& l);

    static inline
    symbol_type
    make_EXIT (const location_type& l);

    static inline
    symbol_type
    make_GET_ASSERTIONS (const location_type& l);

    static inline
    symbol_type
    make_GET_ASSIGNMENT (const location_type& l);

    static inline
    symbol_type
    make_GET_INFO (const location_type& l);

    static inline
    symbol_type
    make_GET_OPTION (const location_type& l);

    static inline
    symbol_type
    make_GET_PROOF (const location_type& l);

    static inline
    symbol_type
    make_GET_UNSAT_CORE (const location_type& l);

    static inline
    symbol_type
    make_GET_VALUE (const location_type& l);

    static inline
    symbol_type
    make_POP (const location_type& l);

    static inline
    symbol_type
    make_PUSH (const location_type& l);

    static inline
    symbol_type
    make_SET_LOGIC (const location_type& l);

    static inline
    symbol_type
    make_SET_INFO (const location_type& l);

    static inline
    symbol_type
    make_SET_OPTION (const location_type& l);

    static inline
    symbol_type
    make_BINARY (const std::string& v, const location_type& l);

    static inline
    symbol_type
    make_DECIMAL (const std::string& v, const location_type& l);

    static inline
    symbol_type
    make_HEXADECIMAL (const std::string& v, const location_type& l);

    static inline
    symbol_type
    make_KEYWORD (const std::string& v, const location_type& l);

    static inline
    symbol_type
    make_NUMERAL (const std::string& v, const location_type& l);

    static inline
    symbol_type
    make_STRING (const std::string& v, const location_type& l);

    static inline
    symbol_type
    make_SYMBOL (const std::string& v, const location_type& l);


    /// Build a parser object.
     Parser  (smtlib::Script*& script_yyarg, Scanner& scanner_yyarg);
    virtual ~ Parser  ();

    /// Parse.
    /// \returns  0 iff parsing succeeded.
    virtual int parse ();

#if YYDEBUG
    /// The current debugging stream.
    std::ostream& debug_stream () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging stream.
    void set_debug_stream (std::ostream &);

    /// Type for debugging levels.
    typedef int debug_level_type;
    /// The current debugging level.
    debug_level_type debug_level () const YY_ATTRIBUTE_PURE;
    /// Set the current debugging level.
    void set_debug_level (debug_level_type l);
#endif

    /// Report a syntax error.
    /// \param loc    where the syntax error is found.
    /// \param msg    a description of the syntax error.
    virtual void error (const location_type& loc, const std::string& msg);

    /// Report a syntax error.
    void error (const syntax_error& err);

  private:
    /// This class is not copyable.
     Parser  (const  Parser &);
     Parser & operator= (const  Parser &);

    /// State numbers.
    typedef int state_type;

    /// Generate an error message.
    /// \param yystate   the state where the error occurred.
    /// \param yytoken   the lookahead token type, or yyempty_.
    virtual std::string yysyntax_error_ (state_type yystate,
                                         symbol_number_type yytoken) const;

    /// Compute post-reduction state.
    /// \param yystate   the current state
    /// \param yysym     the nonterminal to push on the stack
    state_type yy_lr_goto_state_ (state_type yystate, int yysym);

    /// Whether the given \c yypact_ value indicates a defaulted state.
    /// \param yyvalue   the value to check
    static bool yy_pact_value_is_default_ (int yyvalue);

    /// Whether the given \c yytable_ value indicates a syntax error.
    /// \param yyvalue   the value to check
    static bool yy_table_value_is_error_ (int yyvalue);

    static const short int yypact_ninf_;
    static const signed char yytable_ninf_;

    /// Convert a scanner token number \a t to a symbol number.
    static token_number_type yytranslate_ (token_type t);

    // Tables.
  // YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
  // STATE-NUM.
  static const short int yypact_[];

  // YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
  // Performed when YYTABLE does not specify something else to do.  Zero
  // means the default is an error.
  static const unsigned char yydefact_[];

  // YYPGOTO[NTERM-NUM].
  static const short int yypgoto_[];

  // YYDEFGOTO[NTERM-NUM].
  static const short int yydefgoto_[];

  // YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
  // positive, shift that token.  If negative, reduce the rule whose
  // number is the opposite.  If YYTABLE_NINF, syntax error.
  static const unsigned char yytable_[];

  static const short int yycheck_[];

  // YYSTOS[STATE-NUM] -- The (internal number of the) accessing
  // symbol of state STATE-NUM.
  static const unsigned char yystos_[];

  // YYR1[YYN] -- Symbol number of symbol that rule YYN derives.
  static const unsigned char yyr1_[];

  // YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.
  static const unsigned char yyr2_[];


    /// Convert the symbol name \a n to a form suitable for a diagnostic.
    static std::string yytnamerr_ (const char *n);


    /// For a symbol, its name in clear.
    static const char* const yytname_[];
#if YYDEBUG
  // YYRLINE[YYN] -- Source line where rule number YYN was defined.
  static const unsigned short int yyrline_[];
    /// Report on the debug stream that the rule \a r is going to be reduced.
    virtual void yy_reduce_print_ (int r);
    /// Print the state stack on the debug stream.
    virtual void yystack_print_ ();

    // Debugging.
    int yydebug_;
    std::ostream* yycdebug_;

    /// \brief Display a symbol type, value and location.
    /// \param yyo    The output stream.
    /// \param yysym  The symbol.
    template <typename Base>
    void yy_print_ (std::ostream& yyo, const basic_symbol<Base>& yysym) const;
#endif

    /// \brief Reclaim the memory associated to a symbol.
    /// \param yymsg     Why this token is reclaimed.
    ///                  If null, print nothing.
    /// \param yysym     The symbol.
    template <typename Base>
    void yy_destroy_ (const char* yymsg, basic_symbol<Base>& yysym) const;

  private:
    /// Type access provider for state based symbols.
    struct by_state
    {
      /// Default constructor.
      by_state ();

      /// The symbol type as needed by the constructor.
      typedef state_type kind_type;

      /// Constructor.
      by_state (kind_type s);

      /// Copy constructor.
      by_state (const by_state& other);

      /// Steal the symbol type from \a that.
      void move (by_state& that);

      /// The (internal) type number (corresponding to \a state).
      /// "empty" when empty.
      symbol_number_type type_get () const;

      enum { empty = 0 };

      /// The state.
      state_type state;
    };

    /// "Internal" symbol: element of the stack.
    struct stack_symbol_type : basic_symbol<by_state>
    {
      /// Superclass.
      typedef basic_symbol<by_state> super_type;
      /// Construct an empty symbol.
      stack_symbol_type ();
      /// Steal the contents from \a sym to build this.
      stack_symbol_type (state_type s, symbol_type& sym);
      /// Assignment, needed by push_back.
      stack_symbol_type& operator= (const stack_symbol_type& that);
    };

    /// Stack type.
    typedef stack<stack_symbol_type> stack_type;

    /// The stack.
    stack_type yystack_;

    /// Push a new state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param s    the symbol
    /// \warning the contents of \a s.value is stolen.
    void yypush_ (const char* m, stack_symbol_type& s);

    /// Push a new look ahead token on the state on the stack.
    /// \param m    a debug message to display
    ///             if null, no trace is output.
    /// \param s    the state
    /// \param sym  the symbol (for its value and location).
    /// \warning the contents of \a s.value is stolen.
    void yypush_ (const char* m, state_type s, symbol_type& sym);

    /// Pop \a n symbols the three stacks.
    void yypop_ (unsigned int n = 1);

    // Constants.
    enum
    {
      yyeof_ = 0,
      yylast_ = 298,     ///< Last index in yytable_.
      yynnts_ = 30,  ///< Number of nonterminal symbols.
      yyempty_ = -2,
      yyfinal_ = 3, ///< Termination state number.
      yyterror_ = 1,
      yyerrcode_ = 256,
      yyntokens_ = 57  ///< Number of tokens.
    };


    // User arguments.
    smtlib::Script*& script;
    Scanner& scanner;
  };

  // Symbol number corresponding to token number t.
  inline
   Parser ::token_number_type
   Parser ::yytranslate_ (token_type t)
  {
    static
    const token_number_type
    translate_table[] =
    {
     0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56
    };
    const unsigned int user_token_number_max_ = 311;
    const token_number_type undef_token_ = 2;

    if (static_cast<int>(t) <= yyeof_)
      return yyeof_;
    else if (static_cast<unsigned int> (t) <= user_token_number_max_)
      return translate_table[t];
    else
      return undef_token_;
  }

  inline
   Parser ::syntax_error::syntax_error (const location_type& l, const std::string& m)
    : std::runtime_error (m)
    , location (l)
  {}

  // basic_symbol.
  template <typename Base>
  inline
   Parser ::basic_symbol<Base>::basic_symbol ()
    : value ()
  {}

  template <typename Base>
  inline
   Parser ::basic_symbol<Base>::basic_symbol (const basic_symbol& other)
    : Base (other)
    , value ()
    , location (other.location)
  {
      switch (other.type_get ())
    {
      case 74: // attribute_list_
        value.copy< smtlib::AttributeList_ptr > (other.value);
        break;

      case 75: // attribute
        value.copy< smtlib::Attribute_ptr > (other.value);
        break;

      case 59: // command_list
        value.copy< smtlib::CommandList_ptr > (other.value);
        break;

      case 60: // command
        value.copy< smtlib::Command_ptr > (other.value);
        break;

      case 81: // identifier
        value.copy< smtlib::Identifier_ptr > (other.value);
        break;

      case 82: // numeral_list_
        value.copy< smtlib::NumeralList_ptr > (other.value);
        break;

      case 86: // spec_constant
        value.copy< smtlib::Primitive_ptr > (other.value);
        break;

      case 77: // sort_list
      case 78: // sort_list_
        value.copy< smtlib::SortList_ptr > (other.value);
        break;

      case 79: // sort
        value.copy< smtlib::Sort_ptr > (other.value);
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        value.copy< smtlib::SortedVarList_ptr > (other.value);
        break;

      case 69: // sorted_var
        value.copy< smtlib::SortedVar_ptr > (other.value);
        break;

      case 65: // term_list_
        value.copy< smtlib::TermList_ptr > (other.value);
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        value.copy< smtlib::Term_ptr > (other.value);
        break;

      case 70: // var_binding_list_
        value.copy< smtlib::VarBindingList_ptr > (other.value);
        break;

      case 71: // var_binding
        value.copy< smtlib::VarBinding_ptr > (other.value);
        break;

      case 80: // var_type
        value.copy< smtlib::VarType_ptr > (other.value);
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        value.copy< std::string > (other.value);
        break;

      default:
        break;
    }

  }


  template <typename Base>
  inline
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const semantic_type& v, const location_type& l)
    : Base (t)
    , value ()
    , location (l)
  {
    (void) v;
      switch (this->type_get ())
    {
      case 74: // attribute_list_
        value.copy< smtlib::AttributeList_ptr > (v);
        break;

      case 75: // attribute
        value.copy< smtlib::Attribute_ptr > (v);
        break;

      case 59: // command_list
        value.copy< smtlib::CommandList_ptr > (v);
        break;

      case 60: // command
        value.copy< smtlib::Command_ptr > (v);
        break;

      case 81: // identifier
        value.copy< smtlib::Identifier_ptr > (v);
        break;

      case 82: // numeral_list_
        value.copy< smtlib::NumeralList_ptr > (v);
        break;

      case 86: // spec_constant
        value.copy< smtlib::Primitive_ptr > (v);
        break;

      case 77: // sort_list
      case 78: // sort_list_
        value.copy< smtlib::SortList_ptr > (v);
        break;

      case 79: // sort
        value.copy< smtlib::Sort_ptr > (v);
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        value.copy< smtlib::SortedVarList_ptr > (v);
        break;

      case 69: // sorted_var
        value.copy< smtlib::SortedVar_ptr > (v);
        break;

      case 65: // term_list_
        value.copy< smtlib::TermList_ptr > (v);
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        value.copy< smtlib::Term_ptr > (v);
        break;

      case 70: // var_binding_list_
        value.copy< smtlib::VarBindingList_ptr > (v);
        break;

      case 71: // var_binding
        value.copy< smtlib::VarBinding_ptr > (v);
        break;

      case 80: // var_type
        value.copy< smtlib::VarType_ptr > (v);
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        value.copy< std::string > (v);
        break;

      default:
        break;
    }
}


  // Implementation of basic_symbol constructor for each type.

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const location_type& l)
    : Base (t)
    , value ()
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::AttributeList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::Attribute_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::CommandList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::Command_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::Identifier_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::NumeralList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::Primitive_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::SortList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::Sort_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::SortedVarList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::SortedVar_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::TermList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::Term_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::VarBindingList_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::VarBinding_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const smtlib::VarType_ptr v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}

  template <typename Base>
   Parser ::basic_symbol<Base>::basic_symbol (typename Base::kind_type t, const std::string v, const location_type& l)
    : Base (t)
    , value (v)
    , location (l)
  {}


  template <typename Base>
  inline
   Parser ::basic_symbol<Base>::~basic_symbol ()
  {
    // User destructor.
    symbol_number_type yytype = this->type_get ();
    switch (yytype)
    {
   default:
      break;
    }

    // Type destructor.
    switch (yytype)
    {
      case 74: // attribute_list_
        value.template destroy< smtlib::AttributeList_ptr > ();
        break;

      case 75: // attribute
        value.template destroy< smtlib::Attribute_ptr > ();
        break;

      case 59: // command_list
        value.template destroy< smtlib::CommandList_ptr > ();
        break;

      case 60: // command
        value.template destroy< smtlib::Command_ptr > ();
        break;

      case 81: // identifier
        value.template destroy< smtlib::Identifier_ptr > ();
        break;

      case 82: // numeral_list_
        value.template destroy< smtlib::NumeralList_ptr > ();
        break;

      case 86: // spec_constant
        value.template destroy< smtlib::Primitive_ptr > ();
        break;

      case 77: // sort_list
      case 78: // sort_list_
        value.template destroy< smtlib::SortList_ptr > ();
        break;

      case 79: // sort
        value.template destroy< smtlib::Sort_ptr > ();
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        value.template destroy< smtlib::SortedVarList_ptr > ();
        break;

      case 69: // sorted_var
        value.template destroy< smtlib::SortedVar_ptr > ();
        break;

      case 65: // term_list_
        value.template destroy< smtlib::TermList_ptr > ();
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        value.template destroy< smtlib::Term_ptr > ();
        break;

      case 70: // var_binding_list_
        value.template destroy< smtlib::VarBindingList_ptr > ();
        break;

      case 71: // var_binding
        value.template destroy< smtlib::VarBinding_ptr > ();
        break;

      case 80: // var_type
        value.template destroy< smtlib::VarType_ptr > ();
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        value.template destroy< std::string > ();
        break;

      default:
        break;
    }

  }

  template <typename Base>
  inline
  void
   Parser ::basic_symbol<Base>::move (basic_symbol& s)
  {
    super_type::move(s);
      switch (this->type_get ())
    {
      case 74: // attribute_list_
        value.move< smtlib::AttributeList_ptr > (s.value);
        break;

      case 75: // attribute
        value.move< smtlib::Attribute_ptr > (s.value);
        break;

      case 59: // command_list
        value.move< smtlib::CommandList_ptr > (s.value);
        break;

      case 60: // command
        value.move< smtlib::Command_ptr > (s.value);
        break;

      case 81: // identifier
        value.move< smtlib::Identifier_ptr > (s.value);
        break;

      case 82: // numeral_list_
        value.move< smtlib::NumeralList_ptr > (s.value);
        break;

      case 86: // spec_constant
        value.move< smtlib::Primitive_ptr > (s.value);
        break;

      case 77: // sort_list
      case 78: // sort_list_
        value.move< smtlib::SortList_ptr > (s.value);
        break;

      case 79: // sort
        value.move< smtlib::Sort_ptr > (s.value);
        break;

      case 67: // sorted_var_list
      case 68: // sorted_var_list_
        value.move< smtlib::SortedVarList_ptr > (s.value);
        break;

      case 69: // sorted_var
        value.move< smtlib::SortedVar_ptr > (s.value);
        break;

      case 65: // term_list_
        value.move< smtlib::TermList_ptr > (s.value);
        break;

      case 66: // term
      case 72: // qual_identifier
      case 73: // term_constant
        value.move< smtlib::Term_ptr > (s.value);
        break;

      case 70: // var_binding_list_
        value.move< smtlib::VarBindingList_ptr > (s.value);
        break;

      case 71: // var_binding
        value.move< smtlib::VarBinding_ptr > (s.value);
        break;

      case 80: // var_type
        value.move< smtlib::VarType_ptr > (s.value);
        break;

      case 50: // "binary"
      case 51: // "decimal"
      case 52: // "hexadecimal"
      case 53: // "keyword"
      case 54: // "number"
      case 55: // "string"
      case 56: // "symbol"
        value.move< std::string > (s.value);
        break;

      default:
        break;
    }

    location = s.location;
  }

  // by_type.
  inline
   Parser ::by_type::by_type ()
     : type (empty)
  {}

  inline
   Parser ::by_type::by_type (const by_type& other)
    : type (other.type)
  {}

  inline
   Parser ::by_type::by_type (token_type t)
    : type (yytranslate_ (t))
  {}

  inline
  void
   Parser ::by_type::move (by_type& that)
  {
    type = that.type;
    that.type = empty;
  }

  inline
  int
   Parser ::by_type::type_get () const
  {
    return type;
  }

  inline
   Parser ::token_type
   Parser ::by_type::token () const
  {
    // YYTOKNUM[NUM] -- (External) token number corresponding to the
    // (internal) symbol number NUM (which must be that of a token).  */
    static
    const unsigned short int
    yytoken_number_[] =
    {
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311
    };
    return static_cast<token_type> (yytoken_number_[type]);
  }
  // Implementation of make_symbol for each symbol type.
   Parser ::symbol_type
   Parser ::make_END (const location_type& l)
  {
    return symbol_type (token::TOK_END, l);
  }

   Parser ::symbol_type
   Parser ::make_PAREN_O (const location_type& l)
  {
    return symbol_type (token::TOK_PAREN_O, l);
  }

   Parser ::symbol_type
   Parser ::make_PAREN_C (const location_type& l)
  {
    return symbol_type (token::TOK_PAREN_C, l);
  }

   Parser ::symbol_type
   Parser ::make_BANG (const location_type& l)
  {
    return symbol_type (token::TOK_BANG, l);
  }

   Parser ::symbol_type
   Parser ::make_UNDERSCORE (const location_type& l)
  {
    return symbol_type (token::TOK_UNDERSCORE, l);
  }

   Parser ::symbol_type
   Parser ::make_AS (const location_type& l)
  {
    return symbol_type (token::TOK_AS, l);
  }

   Parser ::symbol_type
   Parser ::make_EXISTS (const location_type& l)
  {
    return symbol_type (token::TOK_EXISTS, l);
  }

   Parser ::symbol_type
   Parser ::make_FORALL (const location_type& l)
  {
    return symbol_type (token::TOK_FORALL, l);
  }

   Parser ::symbol_type
   Parser ::make_LET (const location_type& l)
  {
    return symbol_type (token::TOK_LET, l);
  }

   Parser ::symbol_type
   Parser ::make_PAR (const location_type& l)
  {
    return symbol_type (token::TOK_PAR, l);
  }

   Parser ::symbol_type
   Parser ::make_AND (const location_type& l)
  {
    return symbol_type (token::TOK_AND, l);
  }

   Parser ::symbol_type
   Parser ::make_NOT (const location_type& l)
  {
    return symbol_type (token::TOK_NOT, l);
  }

   Parser ::symbol_type
   Parser ::make_MINUS (const location_type& l)
  {
    return symbol_type (token::TOK_MINUS, l);
  }

   Parser ::symbol_type
   Parser ::make_PLUS (const location_type& l)
  {
    return symbol_type (token::TOK_PLUS, l);
  }

   Parser ::symbol_type
   Parser ::make_EQ (const location_type& l)
  {
    return symbol_type (token::TOK_EQ, l);
  }

   Parser ::symbol_type
   Parser ::make_GT (const location_type& l)
  {
    return symbol_type (token::TOK_GT, l);
  }

   Parser ::symbol_type
   Parser ::make_GE (const location_type& l)
  {
    return symbol_type (token::TOK_GE, l);
  }

   Parser ::symbol_type
   Parser ::make_LT (const location_type& l)
  {
    return symbol_type (token::TOK_LT, l);
  }

   Parser ::symbol_type
   Parser ::make_LE (const location_type& l)
  {
    return symbol_type (token::TOK_LE, l);
  }

   Parser ::symbol_type
   Parser ::make_ITE (const location_type& l)
  {
    return symbol_type (token::TOK_ITE, l);
  }

   Parser ::symbol_type
   Parser ::make_RE_CONCAT (const location_type& l)
  {
    return symbol_type (token::TOK_RE_CONCAT, l);
  }

   Parser ::symbol_type
   Parser ::make_RE_OR (const location_type& l)
  {
    return symbol_type (token::TOK_RE_OR, l);
  }

   Parser ::symbol_type
   Parser ::make_CONCAT (const location_type& l)
  {
    return symbol_type (token::TOK_CONCAT, l);
  }

   Parser ::symbol_type
   Parser ::make_IN (const location_type& l)
  {
    return symbol_type (token::TOK_IN, l);
  }

   Parser ::symbol_type
   Parser ::make_LEN (const location_type& l)
  {
    return symbol_type (token::TOK_LEN, l);
  }

   Parser ::symbol_type
   Parser ::make_TO_REGEX (const location_type& l)
  {
    return symbol_type (token::TOK_TO_REGEX, l);
  }

   Parser ::symbol_type
   Parser ::make_TBOOL (const location_type& l)
  {
    return symbol_type (token::TOK_TBOOL, l);
  }

   Parser ::symbol_type
   Parser ::make_TINT (const location_type& l)
  {
    return symbol_type (token::TOK_TINT, l);
  }

   Parser ::symbol_type
   Parser ::make_TSTRING (const location_type& l)
  {
    return symbol_type (token::TOK_TSTRING, l);
  }

   Parser ::symbol_type
   Parser ::make_ASSERT (const location_type& l)
  {
    return symbol_type (token::TOK_ASSERT, l);
  }

   Parser ::symbol_type
   Parser ::make_CHECK_SAT (const location_type& l)
  {
    return symbol_type (token::TOK_CHECK_SAT, l);
  }

   Parser ::symbol_type
   Parser ::make_DECLARE_FUN (const location_type& l)
  {
    return symbol_type (token::TOK_DECLARE_FUN, l);
  }

   Parser ::symbol_type
   Parser ::make_DECLARE_SORT (const location_type& l)
  {
    return symbol_type (token::TOK_DECLARE_SORT, l);
  }

   Parser ::symbol_type
   Parser ::make_DEFINE_FUN (const location_type& l)
  {
    return symbol_type (token::TOK_DEFINE_FUN, l);
  }

   Parser ::symbol_type
   Parser ::make_DEFINE_SORT (const location_type& l)
  {
    return symbol_type (token::TOK_DEFINE_SORT, l);
  }

   Parser ::symbol_type
   Parser ::make_EXIT (const location_type& l)
  {
    return symbol_type (token::TOK_EXIT, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_ASSERTIONS (const location_type& l)
  {
    return symbol_type (token::TOK_GET_ASSERTIONS, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_ASSIGNMENT (const location_type& l)
  {
    return symbol_type (token::TOK_GET_ASSIGNMENT, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_INFO (const location_type& l)
  {
    return symbol_type (token::TOK_GET_INFO, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_OPTION (const location_type& l)
  {
    return symbol_type (token::TOK_GET_OPTION, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_PROOF (const location_type& l)
  {
    return symbol_type (token::TOK_GET_PROOF, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_UNSAT_CORE (const location_type& l)
  {
    return symbol_type (token::TOK_GET_UNSAT_CORE, l);
  }

   Parser ::symbol_type
   Parser ::make_GET_VALUE (const location_type& l)
  {
    return symbol_type (token::TOK_GET_VALUE, l);
  }

   Parser ::symbol_type
   Parser ::make_POP (const location_type& l)
  {
    return symbol_type (token::TOK_POP, l);
  }

   Parser ::symbol_type
   Parser ::make_PUSH (const location_type& l)
  {
    return symbol_type (token::TOK_PUSH, l);
  }

   Parser ::symbol_type
   Parser ::make_SET_LOGIC (const location_type& l)
  {
    return symbol_type (token::TOK_SET_LOGIC, l);
  }

   Parser ::symbol_type
   Parser ::make_SET_INFO (const location_type& l)
  {
    return symbol_type (token::TOK_SET_INFO, l);
  }

   Parser ::symbol_type
   Parser ::make_SET_OPTION (const location_type& l)
  {
    return symbol_type (token::TOK_SET_OPTION, l);
  }

   Parser ::symbol_type
   Parser ::make_BINARY (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_BINARY, v, l);
  }

   Parser ::symbol_type
   Parser ::make_DECIMAL (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_DECIMAL, v, l);
  }

   Parser ::symbol_type
   Parser ::make_HEXADECIMAL (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_HEXADECIMAL, v, l);
  }

   Parser ::symbol_type
   Parser ::make_KEYWORD (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_KEYWORD, v, l);
  }

   Parser ::symbol_type
   Parser ::make_NUMERAL (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_NUMERAL, v, l);
  }

   Parser ::symbol_type
   Parser ::make_STRING (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_STRING, v, l);
  }

   Parser ::symbol_type
   Parser ::make_SYMBOL (const std::string& v, const location_type& l)
  {
    return symbol_type (token::TOK_SYMBOL, v, l);
  }


#line 9 "parser.ypp" // lalr1.cc:372
} //  Vlab 
#line 1956 "parser.hpp" // lalr1.cc:372




#endif // !YY_YY_PARSER_HPP_INCLUDED
