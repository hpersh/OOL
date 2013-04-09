#include <setjmp.h>
#include <stdio.h>

struct list {
    struct list *prev, *next;
};

struct obj;
typedef struct obj *obj_t;
#define NIL  ((obj_t) 0)

struct obj {
    struct list list_node;
    obj_t       inst_of;
    unsigned    ref_cnt;
#ifndef NDEBUG
    unsigned    old_ref_cnt;
#endif
};

typedef void (*inst_init_t)(obj_t cl, obj_t inst, va_list ap);
typedef void (*inst_walk_t)(obj_t cl, obj_t inst, void (*func)(obj_t));
typedef void (*inst_free_t)(obj_t cl, obj_t inst);

struct inst_metaclass {
    struct obj  base;
    obj_t       name;
    obj_t       parent;
    obj_t       module;
    obj_t       cl_methods;
    obj_t       cl_vars;
    obj_t       inst_methods;
    obj_t       inst_vars;
    unsigned    inst_size;         /* Size of instance, in bytes */
    inst_init_t inst_init;
    inst_walk_t inst_walk;
    inst_free_t inst_free;
};
#define CLASS(obj)  ((struct inst_metaclass *)(obj))

struct inst_code_method {
  struct obj base;
  void       (*func)(unsigned argc, obj_t args);
};
#define CODE_METHOD(obj)  ((struct inst_code_method *)(obj))

struct inst_boolean {
  struct obj    base;
  unsigned char val;
};
#define BOOLEAN(obj)  ((struct inst_boolean *)(obj))

typedef long long          integer_val_t;
typedef unsigned long long uinteger_val_t;
#define INTEGER_FMT_DEC  "%lld"
#define INTEGER_FMT_OCT  "%llo"
#define INTEGER_FMT_HEX  "%llx"
struct inst_integer {
  struct obj    base;
  integer_val_t val;
};
#define INTEGER(obj)  ((struct inst_integer *)(obj))

typedef long double float_val_t;
#define FLOAT_FMT_SCAN   "%Lf"
#define FLOAT_FMT_PRINT  "%Lg"
struct inst_float {
  struct obj  base;
  float_val_t val;
};
#define FLOAT(obj)  ((struct inst_float *)(obj))

struct inst_string {
    struct obj base;
    unsigned   size;
    char       *data;
};
#define STRING(obj)  ((struct inst_string *)(obj))

struct inst_dptr {
  struct obj base;
  obj_t      car, cdr;
};
#define DPTR(obj)  ((struct inst_dptr *)(obj))
#define CAR(obj)  (DPTR(obj)->car)
#define CDR(obj)  (DPTR(obj)->cdr)

struct inst_method_call {
    struct obj base;
    obj_t      list;
};
#define METHOD_CALL(obj)  ((struct inst_method_call *)(obj))

struct inst_block {
    struct obj base;
    obj_t      list;
};
#define BLOCK(obj)  ((struct inst_block *)(obj))

struct inst_array {
    struct obj base;
    unsigned   size;
    obj_t      *data;
};
#define ARRAY(obj)  ((struct inst_array *)(obj))

struct inst_dict {
    struct inst_array base;
    unsigned (*hash_func)(obj_t key);
    unsigned (*equal_func)(obj_t k1, obj_t k2);
};
#define DICT(obj)  ((struct inst_dict *)(obj))

struct inst_file {
  struct obj base;
  obj_t      filename;
  obj_t      mode;
  FILE       *fp;
};
#define _FILE(obj)  ((struct inst_file *)(obj))

struct inst_module {
    struct inst_dict base;
    obj_t            name;
    obj_t            parent;
    obj_t            filename;	/* NIL <=> Main (top-level module) */
    void             *ptr;      /* NIL <=> Not loaded from dynamic lib */
};
#define MODULE(obj)  ((struct inst_module *)(obj))

enum fatal_errcode {
    FATAL_ERR_NO_MEM,
    FATAL_ERR_STACK_OVERFLOW,
    FATAL_ERR_STACK_UNDERFLOW,
    FATAL_ERR_DOUBLE_ERR,
    FATAL_ERR_BAD_ERR_STREAM
};

void fatal(enum fatal_errcode errcode);

enum errcode {
    ERR_ASSERT,
    ERR_SYM_NOT_BOUND,
    ERR_NO_METHOD,
    ERR_INVALID_METHOD,
    ERR_INVALID_ARG,
    ERR_INVALID_VALUE_1,
    ERR_INVALID_VALUE_2,
    ERR_NUM_ARGS,
    ERR_IDX_RANGE,
    ERR_IDX_RANGE_2,
    ERR_BREAK,
    ERR_CONT,
    ERR_RETURN,
    ERR_FILE_OPEN,
    ERR_CONST,
    ERR_MODULE_LOAD,
    ERR_MODULE_MEMBER,
    ERR_BAD_FORM,
    ERR_OVF
};

void error(enum errcode errcode, ...);

obj_t *sp;
obj_t *env;
obj_t module_main;		/* Top-level module */
obj_t module_cur;		/* Module currently executing */

obj_t regs[8];
#define R0   (regs[0])
#define R1   (regs[1])
#define R2   (regs[2])
#define R3   (regs[3])
#define R4   (regs[4])
#define R5   (regs[5])
#define R6   (regs[6])
#define R7   (regs[7])

void obj_assign(obj_t *dst, obj_t obj);
#define OBJ_ASSIGN(dst, src)  (obj_assign(&(dst), (src)))
obj_t obj_retain(obj_t);
void  obj_release(obj_t);

void vm_assign(unsigned dst, obj_t val);
void vm_pushl(obj_t obj);
void vm_push(unsigned src);
void vm_pushm(unsigned src, unsigned n);
void vm_pop(unsigned dst);
void vm_popm(unsigned dst, unsigned n);
void vm_drop(void);
void vm_dropn(unsigned n);

void inst_init_parent(obj_t cl, obj_t inst, va_list ap);
void inst_walk_parent(obj_t cl, obj_t inst, void (*func)(obj_t));
void inst_free_parent(obj_t cl, obj_t inst);

void cl_inst_init(obj_t cl, obj_t inst, va_list ap);
void cl_inst_walk(obj_t cl, obj_t inst, void (*func)(obj_t));
void cl_inst_free(obj_t cl, obj_t inst);

void m_inst_alloc(obj_t cl);
void inst_init(obj_t recvr, ...);

void m_code_method_new(void (*func)(unsigned, obj_t));
void m_boolean_new(unsigned val);
void m_integer_new(long long val);
void m_float_new(long double val);
void m_string_new(unsigned n, ...);
unsigned string_hash(obj_t s);
unsigned string_equal(obj_t s1, obj_t s2);
void m_string_tocstr(obj_t s);
void m_pair_new(obj_t car, obj_t cdr);
void m_cons(obj_t car, obj_t cdr);
void _list_concat(obj_t li, obj_t obj);
void m_list_concat(obj_t li, obj_t obj);
void m_method_call_new(obj_t list);
void m_block_new(obj_t list);
void m_array_new(unsigned size);
void m_string_dict_new(unsigned size);
void m_dict_new(unsigned size);
void m_class_new(obj_t name, obj_t parent, unsigned inst_size,
		 inst_init_t _inst_init, inst_walk_t _inst_walk, inst_free_t _inst_free
		 );

void m_method_call_1(obj_t sel, obj_t recvr);
void m_method_call_2(obj_t sel, obj_t recvr, obj_t arg1);
void m_method_call_3(obj_t sel, obj_t recvr, obj_t arg1, obj_t arg2);

obj_t env_at(obj_t s);
void  env_new_put(obj_t s, obj_t val);
void  env_at_put(obj_t s, obj_t val);
void  env_del(obj_t s);

struct root_hdr {
    struct root_hdr *next;
    unsigned        size;
};

struct consts {
  struct root_hdr hdr;
  struct {
    obj_t _false, _true;
  } bool;
  struct  {
    obj_t metaclass;
    obj_t object;
    obj_t code_method;
    obj_t boolean;
    obj_t integer;
    obj_t _float;
    obj_t string;
    obj_t dptr;
    obj_t pair;
    obj_t list;
    obj_t method_call;
    obj_t block;
    obj_t array;
    obj_t dict;
    obj_t file;
    obj_t module;
    obj_t env;
    obj_t system;
  } cl;
  struct {
    obj_t Array;
    obj_t Block;
    obj_t Boolean;
    obj_t Code_Method;
    obj_t Dictionary;
    obj_t Dptr;
    obj_t Environment;
    obj_t File;
    obj_t Float;
    obj_t Integer;
    obj_t List;
    obj_t Metaclass;
    obj_t Method_Call;
    obj_t Module;
    obj_t Object;
    obj_t Pair;
    obj_t String;
    obj_t System;
    obj_t addc;
    obj_t andc;
    obj_t appendc;
    obj_t asc;
    obj_t atc;
    obj_t atc_lengthc;
    obj_t atc_putc;
    obj_t _break;
    obj_t car;
    obj_t cdr;
    obj_t chr;
    obj_t class_methods;
    obj_t class_variables;
    obj_t _continue;
    obj_t deletec;
    obj_t divc;
    obj_t equalsc;
    obj_t eval;
    obj_t evalc;
    obj_t exit;
    obj_t exitc;
    obj_t _false;
    obj_t filterc;
    obj_t foreachc;
    obj_t gec;
    obj_t gtc;
    obj_t hash;
    obj_t hex;
    obj_t ifc;
    obj_t ifc_elsec;
    obj_t indexc;
    obj_t instance_methods;
    obj_t instance_variables;
    obj_t instanceof;
    obj_t keys;
    obj_t lec;
    obj_t length;
    obj_t load;
    obj_t ltc;
    obj_t main;
    obj_t mapc;
    obj_t minus;
    obj_t modc;
    obj_t mode;
    obj_t multc;
    obj_t name;
    obj_t new;
    obj_t newc;
    obj_t newc_modec;
    obj_t newc_parentc_instance_variablesc;
    obj_t newc_putc;
    obj_t nil;
    obj_t not;
    obj_t orc;
    obj_t parent;
    obj_t path;
    obj_t pquote;
    obj_t print;
    obj_t printc;
    obj_t quote;
    obj_t range;
    obj_t rangec;
    obj_t rangec_stepc;
    obj_t readc;
    obj_t readln;
    obj_t reducec_initc;
    obj_t _return;
    obj_t rindexc;
    obj_t splicec;
    obj_t splitc;
    obj_t _stderr;
    obj_t _stdin;
    obj_t _stdout;
    obj_t subc;
    obj_t subclassc_instance_variablesc;
    obj_t tostring;
    obj_t tostringc;
    obj_t _true;
    obj_t whilec;
    obj_t xorc;
    
#ifndef NDEBUG
    obj_t assert;
    obj_t collect;
    obj_t debugc;
#endif
    } str;
} consts;

struct root_hdr *root;

struct init_cl {
    obj_t    *pcl;
    obj_t    *pparent, *pname;    
    unsigned inst_size;
    void     (*inst_init)(obj_t cl, obj_t inst, va_list ap);
    void     (*inst_walk)(obj_t cl, obj_t inst, void (*func)(obj_t));
    void     (*inst_free)(obj_t cl, obj_t inst);
};

struct init_str {
    obj_t      *pobj;
    const char *str;
};

struct init_method {
  obj_t *pcl;
  obj_t *psel;
  void  (*func)(unsigned, obj_t);
};

struct init_inst_var {
    obj_t    *pcl;
    obj_t    *psel;
    unsigned ofs;
};

void init_cls(const struct init_cl *tbl, unsigned n);
void init_strs(const struct init_str *tbl, unsigned n);
void init_cl_methods(const struct init_method *tbl, unsigned n);
void init_inst_methods(const struct init_method *tbl, unsigned n);
void init_inst_vars(const struct init_inst_var *tbl, unsigned n);
void root_add(struct root_hdr *hdr, unsigned size);


struct frame {
    struct frame *prev;
    enum frame_type {
	FRAME_TYPE_RESTART,	/* For restarting, after error */
	FRAME_TYPE_INPUT,	/* Input stream */
	FRAME_TYPE_METHOD_CALL,	/* Calling a method */
	FRAME_TYPE_WHILE,	/* Running a "while" */
	FRAME_TYPE_BLOCK,	/* Running a block */
	FRAME_TYPE_MODULE	/* Adding/running a module */
    } type;
};

struct frame_jmp {
    struct frame base;
    obj_t        *sp;		/* Recorded top of stack */
    jmp_buf      jmp_buf;	/* For longjmp() */
};
#define FRAME_JMP(x)  ((struct frame_jmp *)(x))

struct frame_input {
  struct frame       base;
  obj_t              file;
  unsigned           line;
  struct frame_input *prev;
  void               *yybs_prev;
};
#define FRAME_INPUT(x)  ((struct frame_input *)(x))

struct frame_method_call {
    struct frame base;
    obj_t        cl;
    obj_t        sel;
    obj_t        args;
};
#define FRAME_METHOD_CALL(x)  ((struct frame_method_call *)(x))

struct frame_block {
    struct frame_jmp base;
    obj_t            dict;
};
#define FRAME_BLOCK(x)  ((struct frame_block *)(x))

struct frame_module {
  struct frame base;
  obj_t        module;
  obj_t        module_prev;
};
#define FRAME_MODULE(x)  ((struct frame_module *)(x))

obj_t module_cur;

void     *yy_inp_push_file(obj_t file);
void     *yy_inp_push_str(obj_t str);
void     yy_inp_pop(void * cookie);
obj_t    yy_inp_file(void * cookie);
unsigned yy_inp_line(void * cookie);

int  yyparse();

