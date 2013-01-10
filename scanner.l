%option noyywrap

%{

#include <stdlib.h>
#include <stdio.h>

#include "grammar.tab.h"

struct yy_stack_entry {
    struct yy_stack_entry *prev;
    YY_BUFFER_STATE       yybs;
} *yysp;

void
yy_push(void)
{
    struct yy_stack_entry *p;

    p = malloc(sizeof(*p));
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

    free(p);
}

void
yy_push_file(FILE *_fp)
{
    yy_push();
    yy_switch_to_buffer(yy_create_buffer(_fp, YY_BUF_SIZE));
}

void
yy_push_str(char *s, unsigned n)
{
    yy_push();
    yy_scan_bytes(s, n);
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
}

[ \t\n\r]       /* Skip whitespace */

.               { fprintf(stderr, "Bad character (0x%02x) in input\n", yytext[0]); }
