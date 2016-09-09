SUBDIRS = ../smt
AM_YFLAGS =

# AM_LDFLAGS = $(LIBGLOG)

AM_CXXFLAGS = -g

noinst_LTLIBRARIES = libabcparser.la
libabcparser_la_SOURCES = \
	parser.ypp \
	Scanner.cpp \
	Scanner.h \
	lexer.lpp

libabcparser_la_LDFLAGS = -version-info 0:1:0

libabcparser_la_LIBADD = \
	../smt/libabcsmt.la \
	$(LIBGLOG)

CLEANFILES = \
	lexer.cpp \
	location.hh \
	parser.hpp \
	parser.cpp \
	position.hh \
	stack.hh
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	