SUBDIRS = solver interface
AM_CXXFLAGS =

#AM_LDFLAGS = 

bin_PROGRAMS = abc
abc_LDFLAGS = -L$(top_srcdir)/src/interface/.libs

abc_SOURCES = \
	main.cpp 
	
abc_LDADD = \
	-labc \
	$(LIBGLOG)

test-local:
	@echo src, $(srcdir), $(top_srcdir), $(libdir), $(top_srcdir), $(builddir)