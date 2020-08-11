dnl Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT([ABC],[1.0],[vlab@cs.ucsb.edu],[abc],[https://github.com/vlab-cs-ucsb/ABC])

AC_CONFIG_MACRO_DIR([m4])
AC_CONFIG_LIBOBJ_DIR([lib])
AM_MAINTAINER_MODE([enable])

# Check for NDEBUG flag
AC_MSG_CHECKING([whether to build with debug information])
AC_ARG_ENABLE([debug],
    [AS_HELP_STRING([--enable-debug],
    [enable debug data generation (defult=yes)])],
    [debugit="$enableval"],
    [debugit=yes])
AC_MSG_RESULT([$debugit])

AX_CHECK_ENABLE_DEBUG([$debugit],,,)

#if test x"$debugit" = x"yes"; then
#    AX_CHECK_ENABLE_DEBUG(,,,[$debugit])
#else
#    AX_CHECK_ENABLE_DEBUG(,,,[$debugit])
#fi

# lib building
AC_ENABLE_SHARED
AC_DISABLE_STATIC

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

AM_INIT_AUTOMAKE([subdir-objects])

case $host_os in
  darwin* )
        JAVA_HEADERS="-I/System/Library/Frameworks/JavaVM.framework/Headers"
        OS="darwin"
        ;;
  linux*)
        JAVA_HEADERS=
        OS="linux"
        ;;
   *BSD*)
        JAVA_HEADERS=
        OS=""
        ;;
    *)
        #Default Case
        AC_MSG_ERROR([Your platform is not currently supported])
        ;;
esac

AC_SUBST([JAVA_HEADERS])
AC_SUBST([OS])


# Check for programs
AC_LANG([C++])
AC_PROG_CXX
# AX_CXX_COMPILE_STDCXX_14([noext])
AX_CHECK_COMPILE_FLAG([-Wall -Wextra -Wno-uninitialized -Wno-unused-variable -Wno-unused-but-set-variable -Wno-unused-parameter],\
    [CXXFLAGS="$CXXFLAGS -std=c++17 -Wall -Wextra -Wno-uninitialized -Wno-unused-variable -Wno-unused-but-set-variable -Wno-unused-parameter"])

#if test x"$debugit" = x"yes"; then
#    AC_DEFINE([DEBUG],[],[Debug Mode])
#    AX_CHECK_ENABLE_DEBUG(,,,[$debugit])
#else
#    AC_DEFINE([NDEBUG],[],[No-debug Mode])
#fi


AM_PROG_LEX
AC_PROG_YACC

# Check for libraries
#LT_INIT([disable-shared])
LT_INIT


AC_HAVE_LIBRARY([glog], [LIBGLOG=-lglog], AC_MSG_ERROR(Glog logging library not found))
AC_SUBST([LIBGLOG])

AC_CHECK_LIB([monadfa], [dfaFree], [LIBMONADFA=-lmonadfa], AC_MSG_ERROR(MONA DFA library not found))
AC_SUBST([LIBMONADFA])

AC_CHECK_LIB([monabdd], [bdd_size], [LIBMONABDD=-lmonabdd], AC_MSG_ERROR(MONA BDD library not found))
AC_SUBST([LIBMONABDD])

AC_CHECK_LIB([monamem], [mem_alloc], [LIBMONAMEM=-lmonamem], AC_MSG_ERROR(MONA MEM library not found))
AC_SUBST([LIBMONAMEM])



AC_CHECK_LIB([hiredis], [redisConnect])
AS_IF([test "$ac_cv_lib_hiredis_redisConnect" = yes], [HAVE_HIREDIS=1], [HAVE_HIREDIS=0])
AC_CHECK_LIB([ev], [ev_io_stop])
AS_IF([test "$ac_cv_lib_ev_ev_io_stop" = yes], [HAVE_EV=1], [HAVE_EV=0])
AC_CHECK_LIB([redox], [connect])
AS_IF([test "$ac_cv_lib_redox_connect" = yes], [HAVE_REDOX=1], [HAVE_REDOX=0])

AM_CONDITIONAL([HAVE_CACHE], [test "$HAVE_HIREDIS" -eq 1 -a "$HAVE_EV" -eq 1 -a "$HAVE_REDOX" -eq 1])

AM_COND_IF([HAVE_CACHE],
           [AC_DEFINE(USE_CACHE)],
           [AC_MSG_RESULT([Caching disabled: libraries not found])])

AC_CHECK_LIB([stdc++fs], [main])
AS_IF([test "$ac_cv_lib_stdc++fs_main" = yes], [HAVE_STDFS=1], [HAVE_STDFS=0])
AM_CONDITIONAL([STDCFS], [test "$HAVE_STDFS" -eq 1])

AM_COND_IF([STDCFS],
           [AC_DEFINE(HAVE_EXP_FS)],
           [AC_MSG_RESULT([stdc++fs library not found])])

#AC_LINK_IFELSE(
#  [AC_LANG_PROGRAM([#include <boost/multiprecision/cpp_int.hpp>], 
#    [boost::multiprecision::cpp_int dummy])],
#  [], 
#  [AC_MSG_ERROR([Please install boost multiprecision big number headers])])

AC_CHECK_LIB([m], [floor],[LIBM=-lm], AC_MSG_ERROR(c math library m not found))
AC_SUBST([LIBM])


# Define gmock variables 
GMOCK_VERSION="1.7.0"
if test "x$have_pthread" = "xyes"; then
  GMOCK_CPPFLAGS="-DGMOCK_HAS_PTHREAD=1"
  GMOCK_CXXFLAGS="$PTHREAD_CFLAGS"
  GMOCK_LDFLAGS=
  GMOCK_LIBS="$PTHREAD_LIBS"
else
  GMOCK_CPPFLAGS="-DGMOCK_HAS_PTHREAD=0"
  GMOCK_CXXFLAGS=
  GMOCK_LDFLAGS=
  GMOCK_LIBS=
fi
AC_SUBST([GMOCK_VERSION])
AC_SUBST([GMOCK_CPPFLAGS])
AC_SUBST([GMOCK_CXXFLAGS])
AC_SUBST([GMOCK_LDFLAGS])
AC_SUBST([GMOCK_LIBS])
LIBGTEST=-lgtest
LIBGMOCK=-lgmock
LIBGMOCKMAIN=-lgmock_main
AC_SUBST([LIBGTEST])
AC_SUBST([LIBGMOCK])
AC_SUBST([LIBGMOCKMAIN])

# Define Paths
ABC_PATH=`readlink -f $srcdir`
ABC_CXXFLAGS="-D__ABC_PATH__=$ABC_PATH"
AC_SUBST([ABC_CXXFLAGS])

# TODO remove dependencies that is not needed by cpp later on
# TODO improve library check here

# Check for headers

# Check for functions
AC_DEFUN([FUNCTION_MISSING], [AC_MSG_ERROR(required library function not found)])

AC_FUNC_MALLOC
AC_FUNC_MEMCMP
AC_FUNC_MMAP
AC_CHECK_FUNCS(memset localeconv,,FUNCTION_MISSING)

# Check for environment variables
AC_MSG_CHECKING([if JAVA_HOME environment variable is set])
AC_SUBST([JAVA_HOME])
AM_CONDITIONAL([JAVA_HOME_VALID], [test ! -z "$JAVA_HOME"])
AM_COND_IF([JAVA_HOME_VALID], 
          [AC_MSG_RESULT([yes])], 
          [AC_MSG_RESULT([no, JNI interface will not be loaded. Please set JAVA_HOME path to install JNI support and to make ABC available for JAVA programs.])])

# set global compiler options

# Create Makefile files
AC_CONFIG_FILES([ \
    Makefile \
    src/Makefile \
    src/smt/Makefile \
    src/parser/Makefile \
    src/utils/Makefile \
    src/theory/Makefile \
    src/solver/Makefile \
    test/Makefile \
    test/helper/Makefile])
#AC_CONFIG_SUBDIRS([lib/googletest/googletest lib/googletest/googlemock])
#AC_CONFIG_SUBDIRS([external/glog external/LibStranger])
AC_OUTPUT

