SUBDIRS = parser theory
AM_CXXFLAGS = -I$(top_srcdir)/external/glog/src -I$(top_srcdir)/external/LibStranger/src -I$(srcdir)/parser -I$(srcdir)/theory
AM_LDFLAGS = -L$(top_srcdir)/external/glog -lglog
bin_PROGRAMS = abc
abc_SOURCES = \
  ./solver/Ast2Dot.cpp \
  ./solver/Ast2Dot.h \
  ./solver/SymbolTable.cpp \
  ./solver/SymbolTable.h \
  ./solver/Initializer.cpp \
  ./solver/Initializer.h \
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
	Driver.h \
	main.cpp 
	
abc_LDADD = \
	$(top_srcdir)/external/glog/libglog.la \
	./parser/libabcparser.la \
	./theory/libabcautomaton.la


test-local:
	@echo src, $(srcdir), $(top_srcdir)	
