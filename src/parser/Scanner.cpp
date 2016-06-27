/*
 * Scanner.cpp
 *
 *  Created on: Nov 13, 2014
 *      Author: baki
 */

#include "Scanner.h"

namespace Vlab {
namespace SMT {

const std::string Scanner::TAG = "Scanner";

Scanner::Scanner()
        : yyFlexLexer() {
}
Scanner::Scanner(std::istream* in)
        : yyFlexLexer(in) {
}

Scanner::~Scanner() {
}

void Scanner::LexerOutput(const char* buf, int size) {
  yyout << std::setw(9) << Scanner::TAG << ": " << buf << std::endl;
}

void Scanner::LexerError(const char* msg) {
  std::cerr << std::setw(9) << Scanner::TAG << ": '" << yytext << "' at " << loc << " - " << msg << "\n";
  std::exit(2);
}

} /* namespace SMT */
} /* namespace Vlab */
