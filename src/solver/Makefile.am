SUBDIRS = ../parser ../theory

AM_CXXFLAGS =

#AM_LDFLAGS = 
	
noinst_LTLIBRARIES = libabcsolver.la
libabcsolver_la_LDFLAGS = -version-info 0:1:0
libabcsolver_la_CXXFLAGS = -I$(top_srcdir)/src
libabcsolver_la_SOURCES = \
  options/Solver.cpp \
  options/Solver.h \
  AstTraverser.cpp \
  AstTraverser.h \
  Ast2Dot.cpp \
  Ast2Dot.h \
  Value.cpp \
  Value.h \
  SymbolTable.cpp \
  SymbolTable.h \
  Initializer.cpp \
  Initializer.h \
  SyntacticProcessor.cpp \
  SyntacticProcessor.h \
  optimization/ConstantTermChecker.cpp \
  optimization/ConstantTermChecker.h \
  optimization/ConstantTermOptimization.cpp \
  optimization/ConstantTermOptimization.h \
  optimization/CharAtOptimization.cpp \
  optimization/CharAtOptimization.h \
  optimization/SubstringOptimization.cpp \
  optimization/SubstringOptimization.h \
  optimization/ConstraintQuerier.cpp \
  optimization/ConstraintQuerier.h \
  SyntacticOptimizer.cpp \
  SyntacticOptimizer.h \
  Counter.cpp \
  Counter.h \
  ConstraintInformation.cpp \
  ConstraintInformation.h \
  DependencySlicer.cpp \
  DependencySlicer.h \
  EquivalenceClass.cpp \
  EquivalenceClass.h \
  EquivalenceGenerator.h \
  EquivalenceGenerator.cpp \
  EquivClassRuleRunner.cpp \
  EquivClassRuleRunner.h \
  FormulaOptimizer.cpp \
  FormulaOptimizer.h \
  ImplicationRunner.h \
  ImplicationRunner.cpp \
  ConstraintSorter.cpp \
  ConstraintSorter.h \
  VariableValueComputer.cpp \
  VariableValueComputer.h \
  ArithmeticFormulaGenerator.cpp \
  ArithmeticFormulaGenerator.h \
  ArithmeticConstraintSolver.cpp \
  ArithmeticConstraintSolver.h \
  StringFormulaGenerator.cpp \
  StringFormulaGenerator.h \
  StringRelationGenerator.cpp \
  StringRelationGenerator.h \
  StringConstraintSolver.cpp \
  StringConstraintSolver.h \
  ConstraintSolver.cpp \
  ConstraintSolver.h \
  ModelCounter.cpp \
  ModelCounter.h

libabcsolver_la_LIBADD = \
	../parser/libabcparser.la \
	../theory/libabcautomaton.la \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBM) 

test-local:
	@echo src, $(srcdir), $(top_srcdir)
