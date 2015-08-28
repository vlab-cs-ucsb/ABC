SUBDIRS = parser theory
AM_CXXFLAGS = \
	-I$(top_srcdir)/external/glog/src \
	-I$(top_srcdir)/external/LibStranger/src \
	-I$(srcdir)/parser \
	-I$(srcdir)/theory \
	-I$(JAVA_HOME)/include \
	-I$(JAVA_HOME)/include/linux
	
AM_LDFLAGS = \
	-L$(top_srcdir)/external/glog \
	-lglog

lib_LTLIBRARIES = libabc.la
libabc_la_SOURCES = \
  ./solver/Ast2Dot.cpp \
  ./solver/Ast2Dot.h \
  ./solver/Value.cpp \
  ./solver/Value.h \
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
	vlab_cs_ucsb_edu_DriverProxy.cpp \
	vlab_cs_ucsb_edu_DriverProxy.h

libabc_la_LDFLAGS = -version-info 0:1:0

libabc_la_LIBADD = \
	$(top_srcdir)/external/glog/libglog.la \
	./parser/libabcparser.la \
	./theory/libabcautomaton.la

libabc_ladir = $(includedir)/abc
libabc_la_HEADERS = \
	Driver.h \
	vlab_cs_ucsb_edu_DriverProxy.h

bin_PROGRAMS = abc
abc_SOURCES = \
	main.cpp 
	
abc_LDADD = \
	$(top_srcdir)/external/glog/libglog.la \
	./libabc.la

test-local:
	@echo src, $(srcdir), $(top_srcdir)	
