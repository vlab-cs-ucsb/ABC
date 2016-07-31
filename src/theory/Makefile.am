AM_YFLAGS = -d

AM_CXXFLAGS = \
	-I$(top_srcdir)/src -I$(includedir)

AM_LDFLAGS = \
	$(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBGLOG)

noinst_LTLIBRARIES = libabcautomaton.la
libabcautomaton_la_SOURCES = \
	../utils/RegularExpression.cpp \
	../utils/RegularExpression.h \
	../utils/Math.cpp \
	../utils/Math.h \
	../utils/List.cpp \
	../utils/List.h \
	../utils/Cmd.cpp \
	../utils/Cmd.h \
	../options/Theory.cpp \
	../options/Theory.h \
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
	MultiTrackAutomaton.cpp \
	MultiTrackAutomaton.h \
	StringRelation.cpp \
	StringRelation.h

libabcautomaton_la_LDFLAGS = -version-info 0:1:0
	
libabcautomaton_la_LIBADD = \
  $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBGLOG)
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	
