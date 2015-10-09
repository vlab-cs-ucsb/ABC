SUBDIRS = parser theory
AM_CXXFLAGS = \
	-I$(srcdir)/parser \
	-I$(srcdir)/theory

if JAVA_HOME_VALID
AM_CXXFLAGS += -I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/linux
ABC_JNI_SORUCE_FILES = vlab_cs_ucsb_edu_DriverProxy.cpp vlab_cs_ucsb_edu_DriverProxy.h
ABC_JNI_HEADER_FILES = vlab_cs_ucsb_edu_DriverProxy.h
endif

AM_LDFLAGS = \
  -L$(top_srcdir)/src/.libs \
	$(LIBGLOG) 
	

lib_LTLIBRARIES = libabc.la
libabc_la_SOURCES = \
  ./solver/AstTraverser.cpp \
  ./solver/AstTraverser.h \
  ./solver/Ast2Dot.cpp \
  ./solver/Ast2Dot.h \
  ./solver/Value.cpp \
  ./solver/Value.h \
  ./solver/SymbolTable.cpp \
  ./solver/SymbolTable.h \
  ./solver/Initializer.cpp \
  ./solver/Initializer.h \
  ./solver/SyntacticProcessor.cpp \
  ./solver/SyntaxProcessor.h \
  ./solver/SyntacticOptimizer.cpp \
  ./solver/SyntacticOptimizer.h \
  ./solver/Counter.cpp \
  ./solver/Counter.h \
  ./solver/OptimizationRuleRunner.cpp \
  ./solver/OptimizationRuleRunner.h \
  ./solver/VariableOptimizer.cpp \
  ./solver/VariableOptimizer.h \
  ./solver/FormulaOptimizer.cpp \
  ./solver/FormulaOptimizer.h \
  ./solver/ConstraintSorter.cpp \
  ./solver/ConstraintSorter.h \
  ./solver/PreImageComputer.cpp \
  ./solver/PreImageComputer.h \
  ./solver/PostImageComputer.cpp \
	./solver/PostImageComputer.h \
	Driver.cpp \
	Driver.h $(ABC_JNI_SORUCE_FILES)

libabc_la_LDFLAGS = -version-info 0:1:0

libabc_la_LIBADD = \
	$(LIBGLOG) \
	./parser/libabcparser.la \
	./theory/libabcautomaton.la

libabc_ladir = $(includedir)/abc
libabc_la_HEADERS = Driver.h $(ABC_JNI_HEADER_FILES)

bin_PROGRAMS = abc
abc_SOURCES = \
	main.cpp 
	
abc_LDADD = \
	$(LIBGLOG) \
	-labc

test-local:
	@echo src, $(srcdir), $(top_srcdir)
