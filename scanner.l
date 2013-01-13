%option noyywrap

%{

#include <stdlib.h>
#include <stdio.h>

#include "grammar.tab.h"

struct yy_stack_entry {
    struct yy_stack_entry *prev;
    FILE                  *fp;
    void                  *cookie;
    unsigned              line;
    YY_BUFFER_STATE       yybs;		/* Previous; current in YY_CURRENT_BUFFER */
} *yysp;

void *cmalloc(unsigned), _cfree(void *, unsigned);

void
yy_push(void)
{
    struct yy_stack_entry *p;

    p = cmalloc(sizeof(*p));
    p->prev = yysp;
    yysp = p;

    yysp->yybs = YY_CURRENT_BUFFER;
}

void
yy_pop(void)
{
    struct yy_stack_entry *p;

    yy_switch_to_buffer(yysp->yybs);

    p = yysp;
    yysp = yysp->prev;

    _cfree(p, sizeof(*p));
}

void
yy_popall(void)
{
    while (yysp)  yy_pop();
}

void
yy_push_file(FILE *fp, void *cookie)
{
    yy_push();
    yy_switch_to_buffer(yy_create_buffer(fp, YY_BUF_SIZE));
    yysp->fp     = fp;
    yysp->cookie = cookie;
    yysp->line   = 1;
}

void
yy_push_str(char *s, unsigned n)
{
    yy_push();
    yy_scan_bytes(s, n);
    yysp->fp     = 0;
    yysp->cookie = 0;
    yysp->line   = 0;
}

void *
yycookie(void)
{
    return (yysp ? yysp->cookie : 0);
}

int
yyline(void)
{
    return (yysp ? yysp->line : -1);
}

%}

ALPHA           [A-Za-z_\-]

DECDIGIT        [0-9]

HEXDIGIT        [0-9A-Fa-f]

DQUOTE          "\""

EDQUOTE         "\\\""

NDQUOTE         [^\"]

%%

"-"?{DECDIGIT}+"."{DECDIGIT}+	{ return (TOK_FLOATNUM); }

"-"?{DECDIGIT}+			{ return (TOK_DECNUM); }

0[Xx]{HEXDIGIT}+		{ return (TOK_HEXNUM); }

"#"{ALPHA}({ALPHA}|{DECDIGIT})*       { return (TOK_CSYM); }

{ALPHA}({ALPHA}|{DECDIGIT})*          { return (TOK_SYM); }

{DQUOTE}({EDQUOTE}|{NDQUOTE})*{DQUOTE}        { return (TOK_QSTR); }

{ALPHA}({ALPHA}|{DECDIGIT})*":"       { return (TOK_SELN); }

"'"     { return (TOK_QUOTE); }

"("     { return (TOK_LPAREN); }

","     { return (TOK_COMMA); }

")"     { return (TOK_RPAREN); }

"["     { return (TOK_LSQBR); }

"="	{ return (TOK_EQUAL); }

":="	{ return (TOK_CEQUAL); }

"]"     { return (TOK_RSQBR); }

"{"     { return (TOK_LBRACE); }

"}"     { return (TOK_RBRACE); }

"//" {
    char c;

    do {
        c = input();
    } while (!(c == '\n' || c == EOF));

    if (yysp)  ++yysp->line;
}

"\n"	{ if (yysp)  ++yysp->line; }

[ \t\n\r]       /* Skip whitespace */

.               { fprintf(stderr, "Bad character (0x%02x) in input\n", yytext[0]); }
