check: 
AM_CXXFLAGS = -g

#AM_LDFLAGS = 

noinst_LTLIBRARIES = libabctesthelper.la
libabctesthelper_la_SOURCES = \
	FileHelper.cpp \
	FileHelper.h \
	Path.h 

libabctesthelper_la_LDFLAGS = -version-info 0:1:0

#libabctesthelper_la_LIBADD = 

test-local:
	@echo src, $(srcdir), $(top_srcdir)