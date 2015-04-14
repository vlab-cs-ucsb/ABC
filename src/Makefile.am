SUBDIRS=parser
AM_CXXFLAGS = -I$(srcdir)/parser
bin_PROGRAMS = abc
abc_SOURCES = \
  ./solver/Ast2Dot.cpp \
  ./solver/Ast2Dot.h \
	Driver.cpp \
	Driver.h \
	main.cpp 
	
abc_LDADD = \
	parser/libabcparser.la
