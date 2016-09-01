# AM_LDFLAGS = $(LIBGLOG)

AM_CXXFLAGS = -g

noinst_LTLIBRARIES = libabcsmt.la

libabcsmt_la_SOURCES = \
	ast.cpp \
	ast.h \
	typedefs.h \
	Visitable.h \
	Visitor.h

libabcsmt_la_LDFLAGS = -version-info 0:1:0
	
libabcsmt_la_LIBADD = $(LIBGLOG)

test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	