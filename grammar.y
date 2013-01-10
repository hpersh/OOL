%{

#include <stdio.h>
#include <string.h>

#include "ool.h"

#define YYSTYPE  obj_t

extern char *yytext;
extern int  yyleng;

void list_concat(obj_t li, obj_t obj);

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

    VM_PUSH(R0);                /* Just for keeping a reference while parsing */
    $$ = R0;
}

hexnum:
        TOK_HEXNUM
{
    long long val = 0;

    sscanf(yytext, "%llx", &val);
    integer_new(0, val);

    VM_PUSH(R0);
    $$ = R0;
}

floatnum:
	TOK_FLOATNUM
{
    long double val = 0;

    sscanf(yytext, "%Lf", &val);
    float_new(0, val);

    VM_PUSH(R0);
    $$ = R0;
}
	;

csym:
        TOK_CSYM
{
    string_new(0, 1, yyleng, yytext);

    VM_PUSH(R0);
    $$ = R0;
}

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

    VM_PUSHM(R1, 2);

    string_new(1, 1, size, yytext + 1);
    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(1, consts.cl.list, R1, R2);
    method_call_new(0, R1);

    VM_POPM(R1, 2);

    VM_PUSH(R0);
    $$ = R0;
}

sym:
        TOK_SYM
{
    string_new(0, 1, yyleng, yytext);

    VM_PUSH(R0);
    $$ = R0;
}

seln:
        TOK_SELN
{
    string_new(0, 1, yyleng, yytext);

    VM_PUSH(R0);
    $$ = R0;
}

atom:
        decnum
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | hexnum
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | floatnum
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | sym
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | csym
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | seln
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | qstr
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

pair:
	TOK_LPAREN expr TOK_COMMA expr TOK_RPAREN
{
    cons(0, consts.cl.pair, $2, $4);

    VM_PUSH(R0);
    $$ = R0;
}
	;

list_exprs_1:
        list_exprs_1 expr
{
    list_concat($1, $2);

    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | expr
{
    cons(0, consts.cl.list, $1, NIL);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

list:
        TOK_LPAREN list_exprs_1 TOK_RPAREN
{
    VM_ASSIGN(R0, $2);
    
    VM_PUSH(R0);
    $$ = R0;
}
        | TOK_LPAREN TOK_RPAREN
{
    VM_ASSIGN(R0, NIL);
    
    $$ = R0;
}
        ;

method_call_sel_and_args:
        method_call_sel_and_args seln expr
{
    obj_t p, q;

    VM_PUSHM(R1, 2);

    cons(2, consts.cl.list, $3, NIL);
    cons(1, consts.cl.list, $2, R2);
    for (p = $1; q = CDR(p); p = q);
    VM_ASSIGN(CDR(p), R1);
    VM_ASSIGN(R0, $1);

    VM_POPM(R1, 2);

    VM_PUSH(R0);
    $$ = R0;
}
        | seln expr
{
    VM_PUSH(R1);

    cons(1, consts.cl.list, $2, NIL);
    cons(0, consts.cl.list, $1, R1);

    VM_POP(R1);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

method_call:
	TOK_LSQBR sym TOK_EQUAL expr TOK_RSQBR
{
    VM_PUSHM(R1, 2);

    cons(1, consts.cl.list, $4, NIL);
    string_new(2, 1, 6, "value:");
    cons(1, consts.cl.list, R2, R1);
    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(2, consts.cl.list, $2, R2);
    method_call_new(3, R2);
    cons(1, consts.cl.list, R3, R1);
    string_new(2, 1, 4, "new:");
    cons(1, consts.cl.list, R2, R1);
    cons(1, consts.cl.list, consts.str.Environment, R1);
    method_call_new(0, R1);

    VM_POPM(R1, 2);
    
    VM_PUSH(R0);
    $$ = R0;
}
	| TOK_LSQBR sym TOK_CEQUAL expr TOK_RSQBR
{
    VM_PUSHM(R1, 2);

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

    VM_POPM(R1, 2);
    
    VM_PUSH(R0);
    $$ = R0;
}
        | TOK_LSQBR expr sym TOK_RSQBR
{
    VM_PUSHM(R1, 2);
    
    cons(2, consts.cl.list, $3, NIL);
    cons(1, consts.cl.list, $2, R2);
    method_call_new(0, R1);

    VM_POPM(R1, 2);

    VM_PUSH(R0);
    $$ = R0;
}
        | TOK_LSQBR expr method_call_sel_and_args TOK_RSQBR
{
    VM_PUSH(R1);

    cons(1, consts.cl.list, $2, $3);
    method_call_new(0, R1);

    VM_POP(R1);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

block_args_1:
        block_args_1 sym
{
    list_concat($1, $2);

    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | sym
{
    cons(0, consts.cl.list, $1, NIL);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

block_args:
        TOK_LPAREN block_args_1 TOK_RPAREN
{
    VM_ASSIGN(R0, $2);

    VM_PUSH(R0);
    $$ = R0;
}
        | TOK_LPAREN TOK_RPAREN
{
    VM_ASSIGN(R0, NIL);

    $$ = R0;
}
        ;

block_body_1:
        block_body_1 expr
{
    list_concat($1, $2);

    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | expr
{
    cons(0, consts.cl.list, $1, NIL);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

block_body:
        block_body_1
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | /* empty */
{
    VM_ASSIGN(R0, NIL);

    $$ = R0;
}
        ;

block:
        TOK_LBRACE block_args block_body TOK_RBRACE
{
    VM_PUSH(R1);

    cons(1, consts.cl.list, $2, $3);
    block_new(0, R1);

    VM_POP(R1);

    VM_PUSH(R0);
    $$ = R0;
}
        ;

expr:
        atom
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | pair
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | list
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | method_call
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | block
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;
}
        | TOK_QUOTE expr
{
    VM_PUSHM(R1, 2);

    cons(2, consts.cl.list, consts.str.quote, NIL);
    cons(1, consts.cl.list, $2, R2);
    method_call_new(0, R1);

    VM_POPM(R1, 2);
    
    VM_PUSH(R0);
    $$ = R0;
}
        ;

inp:
        expr
{
    VM_ASSIGN(R0, $1);

    VM_PUSH(R0);
    $$ = R0;

    YYACCEPT;
}

