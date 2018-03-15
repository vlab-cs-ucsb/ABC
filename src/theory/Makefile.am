SUBDIRS = ../utils
AM_CXXFLAGS =

#AM_LDFLAGS = 

noinst_LTLIBRARIES = libabcautomaton.la
libabcautomaton_la_LDFLAGS = -version-info 0:1:0
libabcautomaton_la_CXXFLAGS = -I$(top_srcdir)/src 
libabcautomaton_la_SOURCES = \
	options/Theory.cpp \
	options/Theory.h \
	libs/MONALib.cpp \
	libs/MONALib.h \
	GraphNode.cpp \
	GraphNode.h \
	Graph.cpp \
	Graph.h \
	DAGraphNode.cpp \
	DAGraphNode.h \
	DAGraph.cpp \
	DAGraph.h \
	ArithmeticFormula.cpp \
	ArithmeticFormula.h \
	BinaryState.cpp \
	BinaryState.h \
	SemilinearSet.cpp \
	SemilinearSet.h \
	StringFormula.cpp \
	StringFormula.h \
	Automaton.cpp \
	Automaton.h \
	AutomatonBuilder.cpp \
	AutomatonBuilder.h \
	BoolAutomaton.cpp \
	BoolAutomaton.h \
	BoolAutomatonBuilder.cpp \
	BoolAutomatonBuilder.h \
	UnaryAutomaton.cpp \
	UnaryAutomaton.h \
	UnaryAutomatonBuilder.cpp \
	UnaryAutomatonBuilder.h \
	IntAutomaton.cpp \
	IntAutomaton.h \
	StringAutomaton.cpp \
	StringAutomaton.h \
	StringAutomatonBuilder.cpp \
	StringAutomatonBuilder.h \
	IntegerAutomaton.cpp \
	IntegerAutomaton.h \
	IntegerAutomatonBuilder.cpp \
	IntegerAutomatonBuilder.h \
	NaturalNumberAutomaton.cpp \
	NaturalNumberAutomaton.h \
	NaturalNumberAutomatonBuilder.cpp \
	NaturalNumberAutomatonBuilder.cpp \
	RelationalStringAutomaton.cpp \
	RelationalStringAutomaton.h \
	SymbolicCounter.cpp \
	SymbolicCounter.h
	
libabcautomaton_la_LIBADD = \
	../utils/libabcutils.la \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBM) 
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	