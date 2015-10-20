AM_CXXFLAGS = -isystem $(top_srcdir)/lib/googletest/googletest/include \
	-I$(top_srcdir)/src \
	$(GTEST_CXXFLAGS)
	
AM_LDFLAGS = $(GTEST_LDFLAGS) $(GTEST_LIBS) \
	$(top_srcdir)/lib/googletest/googletest/lib/libgtest_main.la \
	$(top_srcdir)/lib/googletest/googletest/lib/libgtest.la \
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
	./solver/ArithmeticFormulaTest.cpp \
	./solver/ArithmeticFormulaTest.h

abctest_LDADD = $(top_srcdir)/src/libabc.la