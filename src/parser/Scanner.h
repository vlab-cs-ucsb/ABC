/*
 * Scanner.h
 *
 *  Created on: Nov 13, 2014
 *      Author: baki
 */

#ifndef PARSER_SCANNER_H_
#define PARSER_SCANNER_H_

#include <iostream>
#include <string>
#include <cstdlib>
#include <iomanip>
#include <fstream>
#include <sstream>

#if ! defined(yyFlexLexerOnce)
#include <FlexLexer.h>
#endif

// change YY_DECL to symbol compatible one
#undef YY_DECL
#define YY_DECL Vlab::SMT::Parser::symbol_type Vlab::SMT::Scanner::yylex_next_symbol()

#include "parser/parser.hpp"
#include "parser/location.hh"

namespace Vlab {
namespace SMT {

class Scanner: public yyFlexLexer {
public:
  Scanner();
  Scanner(std::istream* in);
  ~Scanner();
  virtual Parser::symbol_type yylex_next_symbol();
  static const std::string TAG;

protected:
  std::stringstream quoted_value;
  location loc;
  void LexerOutput(const char* buf, int size);
  void LexerError(const char* msg);

private:
  int yylex() {
    return 0;
  } // hide the default yylex, it is not compatible with bison c++ symbol_type
};

} /* namespace SMT */
} /* namespace Vlab */

#endif /* PARSER_SCANNER_H_ */
