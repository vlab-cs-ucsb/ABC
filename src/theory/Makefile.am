SUBDIRS = ../utils
AM_CXXFLAGS =

#AM_LDFLAGS = 

noinst_LTLIBRARIES = libabcautomaton.la
libabcautomaton_la_LDFLAGS = -version-info 0:1:0
libabcautomaton_la_CXXFLAGS = -I$(top_srcdir)/src 
libabcautomaton_la_SOURCES = \
	options/Theory.cpp \
	options/Theory.h \
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
	BoolAutomaton.cpp \
	BoolAutomaton.h \
	UnaryAutomaton.cpp \
	UnaryAutomaton.h \
	IntAutomaton.cpp \
	IntAutomaton.h \
	StringAutomaton.cpp \
	StringAutomaton.h \
	BinaryIntAutomaton.cpp \
	BinaryIntAutomaton.h \
	RelationalStringAutomaton.cpp \
	RelationalStringAutomaton.h \
	MultiTrackAutomaton.cpp \
	MultiTrackAutomaton.h \
	StringRelation.cpp \
	StringRelation.h \
	SymbolicCounter.cpp \
	SymbolicCounter.h
	
libabcautomaton_la_LIBADD = \
	../utils/libabcutils.la \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBM) 
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	