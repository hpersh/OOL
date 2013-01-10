
bin_PROGRAMS	= ool
ool_SOURCES	= grammar.y scanner.l ool.c
AM_CFLAGS	= -DDEBUG
AM_YFLAGS	= -d -t

pkglibdir_LTLIBRARIES = socket.la

socketla_SOURCES = socket.c
socket_la_LDFLAGS = -avoid-version -module -shared -export-dynamic


