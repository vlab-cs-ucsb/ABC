#SUBDIRS = parser theory

AM_YFLAGS = -d
AM_CXXFLAGS =	-I$(includedir) 
AM_LDFLAGS =  -L$(libdir) 

if JAVA_HOME_VALID
AM_CXXFLAGS += -I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/linux $(JAVA_HEADERS)
ABC_JNI_SORUCE_FILES = vlab_cs_ucsb_edu_DriverProxy.cpp vlab_cs_ucsb_edu_DriverProxy.h
ABC_JNI_HEADER_FILES = vlab_cs_ucsb_edu_DriverProxy.h
endif

lib_LTLIBRARIES = libabc.la

#smt
libabc_la_SOURCES = \
  smt/ast.cpp \
  smt/ast.h \
  smt/typedefs.h \
  smt/Visitable.h \
  smt/Visitor.h 

#parser 
libabc_la_SOURCES += \
  parser/parser.ypp \
  parser/Scanner.cpp \
  parser/Scanner.h \
  parser/lexer.lpp

#utils
libabc_la_SOURCES += \
  utils/RegularExpression.cpp \
  utils/RegularExpression.h \
  utils/Math.cpp \
  utils/Math.h \
  utils/List.cpp \
  utils/List.h \
  utils/Cmd.cpp \
  utils/Cmd.h 

#options
libabc_la_SOURCES += \
  options/Theory.cpp \
  options/Theory.h \
  options/Solver.cpp \
  options/Solver.h 

#theory
libabc_la_SOURCES += \
  theory/GraphNode.cpp \
  theory/GraphNode.h \
  theory/Graph.cpp \
  theory/Graph.h \
  theory/DAGraphNode.cpp \
  theory/DAGraphNode.h \
  theory/DAGraph.cpp \
  theory/DAGraph.h \
  theory/ArithmeticFormula.cpp \
  theory/ArithmeticFormula.h \
  theory/BinaryState.cpp \
  theory/BinaryState.h \
  theory/SemilinearSet.cpp \
  theory/SemilinearSet.h \
  theory/Automaton.cpp \
  theory/Automaton.h \
  theory/BoolAutomaton.cpp \
  theory/BoolAutomaton.h \
  theory/UnaryAutomaton.cpp \
  theory/UnaryAutomaton.h \
  theory/IntAutomaton.cpp \
  theory/IntAutomaton.h \
  theory/StringAutomaton.cpp \
  theory/StringAutomaton.h \
  theory/BinaryIntAutomaton.cpp \
  theory/BinaryIntAutomaton.h \
  theory/MultiTrackAutomaton.cpp \
  theory/MultiTrackAutomaton.h \
  theory/StringRelation.cpp \
  theory/StringRelation.h

#solver
libabc_la_SOURCES += \
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
  ./solver/ImplicationRunner.h \
  ./solver/ImplicationRunner.cpp \
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
	Driver.cpp \
	Driver.h $(ABC_JNI_SORUCE_FILES)

libabc_la_LDFLAGS = -version-info 0:1:0 
libabc_la_LIBADD = \
  $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBGLOG) $(LIBM)  

libabc_ladir = $(includedir)/abc
libabc_la_HEADERS = Driver.h $(ABC_JNI_HEADER_FILES)

# ABC executable
bin_PROGRAMS = abc
abc_SOURCES = \
  main.cpp

abc_LDADD = \
  .libs/libabc.so \
  $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBGLOG) $(LIBM)

MAINTAINERCLEANFILES = \
  Makefile \
  Makefile.in \
  .deps \
  .libs

test-local:
	@echo src, $(srcdir), $(top_srcdir)
