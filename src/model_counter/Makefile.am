AM_YFLAGS = -d

AM_LDFLAGS = \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) 

noinst_LTLIBRARIES = libabcmodelcounter.la

libabcmodelcounter_la_SOURCES = \
	Test.cpp \
	Test.h
	
libabcmodelcounter_la_LDFLAGS = -version-info 0:1:0
	
libabcmodelcounter_la_LIBADD = \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) 
	
test-local: 
	@echo parser, $(srcdir), $(top_srcdir)	