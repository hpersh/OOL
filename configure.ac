#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ([2.69])
AC_INIT([ool], [1], [hpersh@yahoo.com])

# automake needed when not using sub-configured libltdl
# subdir-objects only needed when using non-recursive inline build
AM_INIT_AUTOMAKE

# the inline build *requires* the configure header, although the name
# is not really important
AC_CONFIG_HEADERS([config.h])

# the inline build *requires* libtool with dlopen support
LT_INIT([dlopen])

# find the libltdl sources in the libltdl sub-directory
LT_CONFIG_LTDL_DIR([libltdl])

# only for the recursive case
AC_CONFIG_FILES([libltdl/Makefile])

# choose one
#LTDL_INIT([subproject])
LTDL_INIT([recursive])
#LTDL_INIT([nonrecursive])

# Checks for programs.
AC_PROG_CC
AC_PROG_YACC
# Sometimes Flex is installed as Lex, e.g., NetBSD.
AC_CHECK_PROG([FLEX], [flex lex], [flex])
# Force the use of `missing' to wrap Flex invocations.
AM_MISSING_PROG([LEX], [$FLEX])
# Perform all the tests Automake and Autoconf need.
AM_PROG_LEX

# Checks for libraries.
AC_CHECK_LIB(dl, dlopen)

# Checks for header files.
AC_CHECK_HEADERS([netinet/in.h stdlib.h string.h sys/socket.h])

# Checks for typedefs, structures, and compiler characteristics.

# Checks for library functions.
AC_FUNC_MALLOC
AC_CHECK_FUNCS([memmove memset socket])

AC_CONFIG_FILES([Makefile])
AC_OUTPUT
