AM_CXXFLAGS = \
	-isystem $(top_srcdir)/lib/googletest/googletest/include \
	-isystem $(top_srcdir)/lib/googletest/googlemock/include \
	-I$(top_srcdir)/src \
	$(GMOCK_CXXFLAGS) \
	$(ABC_CXXFLAGS)

AM_LDFLAGS = \
	$(GMOCK_LDFLAGS) $(GMOCK_LIBS) \
		$(top_srcdir)/lib/googletest/googletest/lib/libgtest.la \
	$(top_srcdir)/lib/googletest/googlemock/lib/libgmock_main.la \
	$(top_srcdir)/lib/googletest/googlemock/lib/libgmock.la \
	-L$(top_srcdir)/src/.libs

# TESTS -- Programs run automatically by "make check"
# check_PROGRAMS -- Programs built by "make check" but not necessarily run
TESTS = 
check_PROGRAMS = 

TESTS += \
	abctest
	
check_PROGRAMS += \
	abctest


abctest_SOURCES = \
	./helper/Path.h \
	./helper/FileHelper.cpp \
	./helper/FileHelper.h \
	./mock/theory/MockBinaryIntAutomaton.cpp \
	./mock/theory/MockBinaryIntAutmaton.h \
	./theory/ArithmeticFormulaTest.cpp \
	./theory/ArithmeticFormulaTest.h \
	./theory/BinaryIntAutomatonTest.cpp \
	./theory/BinaryIntAutomatonTest.h

abctest_LDADD = $(top_srcdir)/src/libabc.la