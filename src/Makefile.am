SUBDIRS = parser theory model_counter
AM_CXXFLAGS = \
	-I$(top_srcdir)/src \
	-g


if JAVA_HOME_VALID
AM_CXXFLAGS += -I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/linux $(JAVA_HEADERS)
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
  ./solver/SyntacticProcessor.h \
  ./solver/optimization/ConstantTermChecker.cpp \
  ./solver/optimization/ConstantTermChecker.h \
  ./solver/optimization/ConstantTermOptimization.cpp \
  ./solver/optimization/ConstantTermOptimization.h \
  ./solver/optimization/CharAtOptimization.cpp \
  ./solver/optimization/CharAtOptimization.h \
  ./solver/optimization/SubstringOptimization.cpp \
  ./solver/optimization/SubstringOptimization.h \
  ./solver/SyntacticOptimizer.cpp \
  ./solver/SyntacticOptimizer.h \
  ./solver/Counter.cpp \
  ./solver/Counter.h \
  ./solver/ConstraintInformation.cpp \
  ./solver/ConstraintInformation.h \
  ./solver/DependencySlicer.cpp \
  ./solver/DependencySlicer.h \
  ./solver/EquivalenceClass.cpp \
  ./solver/EquivalenceClass.h \
  ./solver/EquivalenceGenerator.h \
  ./solver/EquivalenceGenerator.cpp \
  ./solver/EquivClassRuleRunner.cpp \
  ./solver/EquivClassRuleRunner.h \
  ./solver/FormulaOptimizer.cpp \
  ./solver/FormulaOptimizer.h \
  ./solver/ConstraintSorter.cpp \
  ./solver/ConstraintSorter.h \
  ./solver/VariableValueComputer.cpp \
  ./solver/VariableValueComputer.h \
  ./solver/ArithmeticFormulaGenerator.cpp \
  ./solver/ArithmeticFormulaGenerator.h \
  ./solver/ArithmeticConstraintSolver.cpp \
  ./solver/ArithmeticConstraintSolver.h \
  ./solver/StringRelationGenerator.cpp \
  ./solver/StringRelationGenerator.h \
  ./solver/StringConstraintSolver.cpp \
  ./solver/StringConstraintSolver.h \
  ./solver/ConstraintSolver.cpp \
	./solver/ConstraintSolver.h \
	./options/Solver.cpp \
	./options/Solver.h \
	Driver.cpp \
	Driver.h $(ABC_JNI_SORUCE_FILES)

libabc_la_LDFLAGS = -version-info 0:1:0

libabc_la_LIBADD = \
	$(LIBGLOG) \
	./parser/libabcparser.la \
	./theory/libabcautomaton.la \
	./model_counter/libabcmodelcounter.la 

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
