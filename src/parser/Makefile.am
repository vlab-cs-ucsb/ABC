AM_YFLAGS = -d

AM_CXXFLAGS = -I$(top_srcdir)/src
AM_LDFLAGS = $(LIBGLOG)
noinst_LTLIBRARIES = libabcparser.la
libabcparser_la_SOURCES = \
	../smt/ast.cpp \
	../smt/ast.h \
	../smt/typedefs.h \
	../smt/Visitable.h \
	../smt/Visitor.h \
	parser.ypp \
	Scanner.cpp \
	Scanner.h \
	lexer.lpp

libabcparser_la_LDFLAGS = -version-info 0:1:0

libabcparser_la_LIBADD = $(LIBGLOG)

CLEANFILES = \
	lexer.cpp \
	location.hh \
	parser.hpp \
	parser.cpp \
	position.hh \
	stack.hh
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	
