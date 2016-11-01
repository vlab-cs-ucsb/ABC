# AM_LDFLAGS = $(LIBGLOG)

AM_CXXFLAGS =

noinst_LTLIBRARIES = libabcutils.la
libabcutils_la_LDFLAGS = -version-info 0:1:0
libabcutils_la_CXXFLAGS = -I$(top_srcdir)/src 
libabcutils_la_SOURCES = \
	RegularExpression.cpp \
	RegularExpression.h \
	Math.cpp \
	Math.h \
	List.cpp \
	List.h \
	Cmd.cpp \
	Cmd.h \
	Program.cpp \
	Program.h \
	Serialize.cpp \
	Serialize.h
	
libabcutils_la_LIBADD = $(LIBGLOG)

test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	