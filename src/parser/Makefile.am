AM_YFLAGS = -d
AM_CXXFLAGS = -I$(top_srcdir)/external/glog/src -I$(srcdir)/parser 
AM_LDFLAGS = -L$(top_srcdir)/external/glog -lglog
noinst_LTLIBRARIES = libabcparser.la
libabcparser_la_SOURCES = \
	../smt/ast.cpp \
	../smt/typedefs.h \
	../smt/Visitable.h \
	../smt/Visitor.h \
	../smt/ast.h \
	parser.ypp \
	Scanner.cpp \
	Scanner.h \
	lexer.lpp
	
libabcparser_la_LIBADD = \
	$(top_srcdir)/external/glog/libglog.la

CLEANFILES = \
	lexer.cpp \
	location.hh \
	parser.hpp \
	parser.cpp \
	position.hh \
	stack.hh
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	