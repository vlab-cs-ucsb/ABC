# not in use yet, needs fixes
AM_CXXFLAGS = \
	-isystem $(top_srcdir)/lib/googletest/googletest/include \
	-isystem $(top_srcdir)/lib/googletest/googlemock/include \
	-I$(top_srcdir)/src \
	$(GMOCK_CXXFLAGS) \
	$(ABC_CXXFLAGS) \
	-g

AM_LDFLAGS = \
	$(GMOCK_LDFLAGS) $(GMOCK_LIBS) \
	$(top_srcdir)/lib/googletest/googletest/lib/libgtest.la \
	$(top_srcdir)/lib/googletest/googlemock/lib/libgmock_main.la \
	$(top_srcdir)/lib/googletest/googlemock/lib/libgmock.la \
	-L$(top_srcdir)/src/.libs

noinst_LTLIBRARIES = libabctestmocktheory.la
libabctestmocktheory_la_SOURCES = \
	./mock/theory/MockIntegerAutomaton.cpp \
	./mock/theory/MockBinaryIntAutmaton.h

libabctestmocktheory_la_LDFLAGS = -version-info 0:1:0

#libabctestmocktheory_la_LIBADD =

test-local:
	@echo src, $(srcdir), $(top_srcdir)
