AM_YFLAGS = -d

AM_CXXFLAGS = \
	-I$(srcdir)/utils \
	-I$(srcdir)/theory 

AM_LDFLAGS = \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBM) $(LIBSTRANGER)

noinst_LTLIBRARIES = libabcautomaton.la
libabcautomaton_la_SOURCES = \
	../utils/RegularExpression.cpp \
	../utils/RegularExpression.h \
	utils.h \
	GraphNode.cpp \
	GraphNode.h \
	Graph.cpp \
	Graph.h \
	DAGraphNode.cpp \
	DAGraphNode.h \
	DAGraph.cpp \
	DAGraph.h \
	Automaton.cpp \
	Automaton.h \
	BoolAutomaton.cpp \
	BoolAutomaotn.h \
	IntAutomaton.cpp \
	IntAutomaton.h \
	IntBoolAutomaton.cpp \
	IntBoolAutomaton.h \
	StringAutomaton.cpp \
	StringAutomaton.h

libabcautomaton_la_LDFLAGS = -version-info 0:1:0
	
libabcautomaton_la_LIBADD = \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBM) $(LIBSTRANGER)
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	