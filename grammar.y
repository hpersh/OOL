%{

#include <stdio.h>
#include <string.h>

#include "ool.h"

#define YYSTYPE  obj_t

extern char *yytext;
extern int  yyleng;

%}

%token TOK_QUOTE
%token TOK_LPAREN
%token TOK_COMMA
%token TOK_RPAREN
%token TOK_LSQBR
%token TOK_CEQUAL
%token TOK_EQUAL
%token TOK_RSQBR
%token TOK_LBRACE
%token TOK_RBRACE
%token TOK_FLOATNUM
%token TOK_DECNUM
%token TOK_HEXNUM
%token TOK_CSYM
%token TOK_SYM
%token TOK_DSYM
%token TOK_QSTR
%token TOK_SELN
%start inp

%%

decnum:
        TOK_DECNUM
{
    long long val = 0;

    sscanf(yytext, "%lld", &val);
    integer_new(0, val);

    vm_push(0);                /* Just for keeping a reference while parsing */
    $$ = R0;
}
	;

hexnum:
        TOK_HEXNUM
{
    long long val = 0;

    sscanf(yytext, "%llx", &val);
    integer_new(0, val);

    vm_push(0);
    $$ = R0;
}
	;

floatnum:
	TOK_FLOATNUM
{
    long double val = 0;

    sscanf(yytext, "%Lf", &val);
    float_new(0, val);

    vm_push(0);
    $$ = R0;
}
	;

csym:
        TOK_CSYM
{
    string_new(0, 1, yyleng, yytext);

    vm_push(0);
    $$ = R0;
}
	;

qstr:
        TOK_QSTR
{
    unsigned size = yyleng - 2, n;
    char     *p;

    for (p = yytext + 1, n = size; n; --n, ++p) {
        char c;

        if (*p != '\\' || n < 2)  continue;
        switch (p[1]) {
        case '"':
            c = '"';
            break;
        case 'n':
            c = '\n';
            break;
        case 'r':
            c = '\r';
            break;
        case 't':
            c = '\t';
            break;
        default:
            continue;
        }
        memmove(p, p + 1, n - 1);
        *p = c;
        --n;
        --size;
    }

    vm_pushm(1, 2);

    string_new(1, 1, size, yytext + 1);
    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(1, consts.cl.list, R1, R2);
    method_call_new(0, R1);

    vm_popm(1, 2);

    vm_push(0);
    $$ = R0;
}
	;

sym:
        TOK_SYM
{
    string_new(0, 1, yyleng, yytext);

    vm_push(0);
    $$ = R0;
}
	;

dsym:
	TOK_DSYM
{
    unsigned k, n;
    char     *p, *q;

    vm_pushm(1, 4);

    for (k = 0, p = yytext;; p = q + 1, ++k) {
	q = index(p, '.');
	n = q ? q - p : strlen(p);

	string_new(4, 1, n, p);

	if (k == 0) {
	    vm_assign(1, R4);
	    continue;
	}
	
	cons(3, consts.cl.list, consts.str.quote, NIL);
	cons(3, consts.cl.list, R4, R3);
	method_call_new(2, R3);
	cons(3, consts.cl.list, R2, NIL);
	cons(3, consts.cl.list, consts.str.atc, R3);
	cons(2, consts.cl.list, R1, R3);
	method_call_new(1, R2);

	if (q == 0)  break;
    }
	
    vm_assign(0, R1);
    
    vm_popm(1, 4);

    vm_push(0);
    $$ = R0;
}
	;

seln:
        TOK_SELN
{
    string_new(0, 1, yyleng, yytext);

    vm_push(0);
    $$ = R0;
}
	;

atom:
        decnum
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | hexnum
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | floatnum
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | sym
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | csym
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | seln
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | qstr
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        ;

pair:
	TOK_LPAREN expr TOK_COMMA expr TOK_RPAREN
{
    cons(0, consts.cl.pair, $2, $4);

    vm_push(0);
    $$ = R0;
}
	;

list_exprs_1:
        list_exprs_1 expr
{
    list_concat($1, $2);

    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | expr
{
    cons(0, consts.cl.list, $1, NIL);

    vm_push(0);
    $$ = R0;
}
        ;

list:
        TOK_LPAREN list_exprs_1 TOK_RPAREN
{
    vm_assign(0, $2);
    
    vm_push(0);
    $$ = R0;
}
        | TOK_LPAREN TOK_RPAREN
{
    vm_assign(0, NIL);
    
    $$ = R0;
}
        ;

method_call_sel_and_args:
        method_call_sel_and_args seln expr
{
    obj_t p, q;

    vm_pushm(1, 2);

    cons(2, consts.cl.list, $3, NIL);
    cons(1, consts.cl.list, $2, R2);
    _list_concat($1, R1);
    vm_assign(0, $1);

    vm_popm(1, 2);

    vm_push(0);
    $$ = R0;
}
        | seln expr
{
    vm_push(1);

    cons(1, consts.cl.list, $2, NIL);
    cons(0, consts.cl.list, $1, R1);

    vm_pop(1);

    vm_push(0);
    $$ = R0;
}
        ;

method_call:
	dsym
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
	| TOK_LSQBR sym TOK_CEQUAL expr TOK_RSQBR
{
    vm_pushm(1, 2);

    cons(1, consts.cl.list, $4, NIL);
    string_new(2, 1, 4, "put:");
    cons(1, consts.cl.list, R2, R1);
    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(2, consts.cl.list, $2, R2);
    method_call_new(3, R2);
    cons(1, consts.cl.list, R3, R1);
    string_new(2, 1, 4, "new:");
    cons(1, consts.cl.list, R2, R1);
    cons(1, consts.cl.list, consts.str.Environment, R1);
    method_call_new(0, R1);

    vm_popm(1, 2);
    
    vm_push(0);
    $$ = R0;
}
	| TOK_LSQBR sym TOK_EQUAL expr TOK_RSQBR
{
    vm_pushm(1, 2);

    cons(1, consts.cl.list, $4, NIL);
    string_new(2, 1, 4, "put:");
    cons(1, consts.cl.list, R2, R1);
    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(2, consts.cl.list, $2, R2);
    method_call_new(3, R2);
    cons(1, consts.cl.list, R3, R1);
    string_new(2, 1, 3, "at:");
    cons(1, consts.cl.list, R2, R1);
    cons(1, consts.cl.list, consts.str.Environment, R1);
    method_call_new(0, R1);

    vm_popm(1, 2);
    
    vm_push(0);
    $$ = R0;
}
        | TOK_LSQBR expr sym TOK_RSQBR
{
    vm_pushm(1, 2);
    
    cons(2, consts.cl.list, $3, NIL);
    cons(1, consts.cl.list, $2, R2);
    method_call_new(0, R1);

    vm_popm(1, 2);

    vm_push(0);
    $$ = R0;
}
        | TOK_LSQBR expr csym TOK_RSQBR
{
    vm_pushm(1, 2);
    
    cons(2, consts.cl.list, $3, NIL);
    cons(1, consts.cl.list, $2, R2);
    method_call_new(0, R1);

    vm_popm(1, 2);

    vm_push(0);
    $$ = R0;
}
        | TOK_LSQBR expr method_call_sel_and_args TOK_RSQBR
{
    vm_push(1);

    cons(1, consts.cl.list, $2, $3);
    method_call_new(0, R1);

    vm_pop(1);

    vm_push(0);
    $$ = R0;
}
        ;

block_args_1:
        block_args_1 sym
{
    list_concat($1, $2);

    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | sym
{
    cons(0, consts.cl.list, $1, NIL);

    vm_push(0);
    $$ = R0;
}
        ;

block_args:
        TOK_LPAREN block_args_1 TOK_RPAREN
{
    vm_assign(0, $2);

    vm_push(0);
    $$ = R0;
}
        | TOK_LPAREN TOK_RPAREN
{
    vm_assign(0, NIL);

    $$ = R0;
}
        ;

block_body_1:
        block_body_1 expr
{
    list_concat($1, $2);

    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | expr
{
    cons(0, consts.cl.list, $1, NIL);

    vm_push(0);
    $$ = R0;
}
        ;

block_body:
        block_body_1
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | /* empty */
{
    vm_assign(0, NIL);

    $$ = R0;
}
        ;

block:
        TOK_LBRACE block_args block_body TOK_RBRACE
{
    vm_push(1);

    cons(1, consts.cl.list, $2, $3);
    block_new(0, R1);

    vm_pop(1);

    vm_push(0);
    $$ = R0;
}
        ;

expr:
        atom
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | pair
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | list
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | method_call
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | block
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;
}
        | TOK_QUOTE expr
{
    vm_pushm(1, 2);

    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(1, consts.cl.list, $2, R2);
    method_call_new(0, R1);

    vm_popm(1, 2);
    
    vm_push(0);
    $$ = R0;
}
        ;

inp:
        expr
{
    vm_assign(0, $1);

    vm_push(0);
    $$ = R0;

    YYACCEPT;
}

