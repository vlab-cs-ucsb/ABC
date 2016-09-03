check:

#SUBDIRS = helper mock
SUBDIRS = helper

AM_CXXFLAGS = \
	-isystem $(top_srcdir)/lib/googletest/googletest/include \
	-isystem $(top_srcdir)/lib/googletest/googlemock/include \
	-I$(top_srcdir)/src \
	$(GMOCK_CXXFLAGS) \
	$(ABC_CXXFLAGS)

AM_LDFLAGS = \
	$(GMOCK_LDFLAGS) \
	-L$(top_srcdir)/src/.libs \
	-L$(top_srcdir)/lib/googletest/googletest/lib/.libs \
	-L$(top_srcdir)/lib/googletest/googlemock/lib/.libs 

# TESTS -- Programs run automatically by "make check"
# check_PROGRAMS -- Programs built by "make check" but not necessarily run
TESTS = 
check_PROGRAMS = 

TESTS += \
	abctest
	
check_PROGRAMS += \
	abctest


#abctest_SOURCES = \
#	./mock/theory/MockBinaryIntAutomaton.cpp \
#	./mock/theory/MockBinaryIntAutmaton.h \
#	./theory/ArithmeticFormulaTest.cpp \
#	./theory/ArithmeticFormulaTest.h \
#	./theory/BinaryIntAutomatonTest.cpp \
#	./theory/BinaryIntAutomatonTest.h
	
abctest_SOURCES = \
	./theory/ArithmeticFormulaTest.cpp \
	./theory/ArithmeticFormulaTest.h 

abctest_LDADD = \
	helper/libabctesthelper.la \
	$(top_srcdir)/src/theory/libabcautomaton.la \
	$(LIBGMOCKMAIN) \
	$(LIBGMOCK) \
	$(LIBGTEST) \
	$(GMOCK_LIBS) 
	

test-local:
	@echo src, $(srcdir), $(top_srcdir)