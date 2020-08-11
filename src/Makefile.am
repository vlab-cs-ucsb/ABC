SUBDIRS = solver 
AM_CXXFLAGS = -std=c++17

AM_LDFLAGS = 
	
lib_LTLIBRARIES = libabc.la
libabc_la_LDFLAGS = -version-info 0:1:0
libabc_la_CXXFLAGS = -I$(top_srcdir)/src 

if JAVA_HOME_VALID
libabc_la_CXXFLAGS += -I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/$(OS) $(JAVA_HEADERS)
ABC_JNI_SORUCE_FILES = vlab_cs_ucsb_edu_DriverProxy.cpp vlab_cs_ucsb_edu_DriverProxy.h
ABC_JNI_HEADER_FILES = vlab_cs_ucsb_edu_DriverProxy.h
endif

libabc_la_SOURCES = \
  Driver.cpp \
  Driver.h \
  $(ABC_JNI_SORUCE_FILES)

libabc_la_LIBADD = \
	solver/libabcsolver.la \
	$(LIBGLOG) $(LIBMONADFA) $(LIBMONABDD) $(LIBMONAMEM) $(LIBM) 

libabc_ladir = $(includedir)/abc
libabc_la_HEADERS = Driver.h $(ABC_JNI_HEADER_FILES)

bin_PROGRAMS = abc
abc_LDFLAGS = -L$(top_srcdir)/src/.libs

abc_SOURCES = \
	main.cpp 
	
abc_LDADD = \
	-labc \
	$(LIBGLOG)

test-local:
	@echo src, $(srcdir), $(top_srcdir)
