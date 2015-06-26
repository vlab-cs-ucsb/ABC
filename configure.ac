dnl Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT([ABC],[1.0],[vlab@cs.ucsb.edu])
AC_CONFIG_MACRO_DIR([m4])
AC_CONFIG_LIBOBJ_DIR([lib])
AM_MAINTAINER_MODE([enable])

# lib building
#AC_ENABLE_SHARED
#AC_DISABLE_STATIC

AC_CANONICAL_BUILD
AC_CANONICAL_HOST
AC_CANONICAL_TARGET

AM_INIT_AUTOMAKE([subdir-objects])

# Check for programs
AC_LANG([C++])
AC_PROG_CXX
AX_CXX_COMPILE_STDCXX_11([noext])
AX_CHECK_COMPILE_FLAG([-Wall -Wextra -Wno-unused-variable -Wno-unused-but-set-variable -Wno-unused-parameter],\
    [CXXFLAGS="$CXXFLAGS -Wall -Wextra -Wno-unused-variable -Wno-unused-but-set-variable -Wno-unused-parameter"])


AM_PROG_LEX
AC_PROG_YACC

# Check for libraries
#LT_INIT([disable-shared])
LT_INIT

AC_CHECK_LIB([monadfa], [dfaFree], [MONADFALIB=-lmonadfa], AC_MSG_ERROR(MONA DFA library not found))
# this will define a variable variable. you can use it in automake.am $(MONADFALIB)
AC_SUBST([MONADFALIB])

AC_CHECK_LIB([monabdd], [bdd_size], [MONABDDLIB=-lmonabdd], AC_MSG_ERROR(MONA BDD library not found))
AC_SUBST([MONABDDLIB])

AC_CHECK_LIB([monamem], [mem_alloc], [MONAMEMLIB=-lmonamem], AC_MSG_ERROR(MONA MEM library not found))
AC_SUBST([MONAMEMLIB])

AC_CHECK_LIB([m], [floor],[MLIB=-lm], AC_MSG_ERROR(c math library m not found))
AC_SUBST([MLIB])

# Check for headers

# Check for functions
AC_DEFUN([FUNCTION_MISSING], [AC_MSG_ERROR(required library function not found)])

AC_FUNC_MALLOC
AC_FUNC_MEMCMP
AC_FUNC_MMAP
AC_CHECK_FUNCS(memset localeconv,,FUNCTION_MISSING)

# set global compiler options

# Create Makefile files
AC_CONFIG_FILES([Makefile src/Makefile src/parser/Makefile src/theory/Makefile])
#AC_CONFIG_SUBDIRS([external/glog external/googletest])
AC_CONFIG_SUBDIRS([external/glog external/LibStranger])
AC_OUTPUT

