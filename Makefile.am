ACLOCAL_AMFLAGS = ${ACLOCAL_FLAGS} -I m4
SUBDIRS = src test
EXTRA_DIST = autogen.sh build/install-build-deps.py

AM_CXXFLAGS = \
  -I$(top_srcdir)/src \
  -g

if JAVA_HOME_VALID
AM_CXXFLAGS += -I$(JAVA_HOME)/include -I$(JAVA_HOME)/include/linux $(JAVA_HEADERS)
ABC_JNI_SORUCE_FILES = vlab_cs_ucsb_edu_DriverProxy.cpp vlab_cs_ucsb_edu_DriverProxy.h
ABC_JNI_HEADER_FILES = vlab_cs_ucsb_edu_DriverProxy.h
endif

AM_LDFLAGS = \
  -L$(top_srcdir)/src/.libs -L/usr/local/lib \
   -labc $(LIBGLOG)

bin_PROGRAMS = abc
abc_SOURCES = \
  src/main.cpp

abc_LDFLAGS = -rpath $(libdir)  

abc_LDADD = \
  -labc $(LIBGLOG)

test-local:
	@echo top, $(srcdir) $(top_srcdir), $(includedir), $(JAVA_HOME), $(libdir)
