AM_YFLAGS = -d

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

libabcparser_la_CXXFLAGS = -I$(includedir)
libabcparser_la_LDFLAGS = -version-info 0:1:0 \
  -L$(libdir) 
libabcparser_la_LIBADD = $(LIBGLOG)

CLEANFILES = \
	lexer.cpp \
	location.hh \
	parser.hpp \
	parser.cpp \
	position.hh \
	stack.hh

MAINTAINERCLEANFILES = \
  Makefile \
  Makefile.in \
  .deps \
  .libs	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	
