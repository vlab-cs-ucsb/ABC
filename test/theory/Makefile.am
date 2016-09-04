check:

#SUBDIRS = 

AM_CXXFLAGS = \
	-isystem $(top_srcdir)/lib/googletest/googletest/include \
	-isystem $(top_srcdir)/lib/googletest/googlemock/include \
	-I$(top_srcdir)/src \
	$(GMOCK_CXXFLAGS) \
	$(ABC_CXXFLAGS) \
	-g

AM_LDFLAGS = \
	$(GMOCK_LDFLAGS) \
	-L$(top_srcdir)/src/.libs \
	-L$(top_srcdir)/lib/googletest/googletest/lib/.libs \
	-L$(top_srcdir)/lib/googletest/googlemock/lib/.libs 

noinst_LTLIBRARIES = libabctesttheory.la

libabctesttheory_la_SOURCES = \
	ArithmeticFormulaTest.cpp \
	ArithmeticFormulaTest.h 
	
libabctesttheory_la_LDFLAGS = -version-info 0:1:0

libabctesttheory_la_LIBADD = \
	../helper/libabctesthelper.la \
	$(top_srcdir)/src/theory/libabcautomaton.la \
	$(LIBGMOCK) \
	$(LIBGTEST) \
	$(GMOCK_LIBS) 
	

test-local:
	@echo src, $(srcdir), $(top_srcdir)