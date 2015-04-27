SUBDIRS=parser
AM_CXXFLAGS = -I$(top_srcdir)/external/glog/src -I$(srcdir)/parser 
AM_LDFLAGS = -L$(top_srcdir)/external/glog -lglog
bin_PROGRAMS = abc
abc_SOURCES = \
  ./solver/Ast2Dot.cpp \
  ./solver/Ast2Dot.h \
  ./solver/Initializer.cpp \
  ./solver/Initializer.h \
	Driver.cpp \
	Driver.h \
	main.cpp 
	
abc_LDADD = \
	parser/libabcparser.la \
	$(top_srcdir)/external/glog/libglog.la

test-local:
	@echo src, $(srcdir), $(top_srcdir)	