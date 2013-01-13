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
};

struct inst_metaclass {
    struct obj base;
    obj_t      name;
    obj_t      parent;
    obj_t      cl_methods;
    obj_t      cl_vars;
    obj_t      inst_methods;
    obj_t      inst_vars;
    unsigned   inst_size;         /* Size of instance, in bytes */
    void       (*inst_init)(obj_t cl, obj_t inst, va_list ap);
    void       (*inst_walk)(obj_t cl, obj_t inst, void (*func)(obj_t));
    void       (*inst_free)(obj_t cl, obj_t inst);
};
#define CLASS(obj)      ((struct inst_metaclass *)(obj))

struct inst_code_method {
    struct obj base;
    void       (*func)(unsigned argc);
};
#define CODE_METHOD(obj) ((struct inst_code_method *)(obj))

struct inst_boolean {
  struct obj    base;
  unsigned char val;
};
#define BOOLEAN(obj)  ((struct inst_boolean *)(obj))

struct inst_integer {
  struct obj base;
  long long  val;
};
#define INTEGER(obj)  ((struct inst_integer *)(obj))

struct inst_float {
    struct obj  base;
    long double val;
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
    struct obj base;
    void       *ptr;
};
#define MODULE(obj)  ((struct inst_module *)(obj))

obj_t *sp;
obj_t env;

obj_t regs[8];
#define R0   (regs[0])
#define R1   (regs[1])
#define R2   (regs[2])
#define R3   (regs[3])
#define R4   (regs[4])
#define R5   (regs[5])
#define R6   (regs[6])
#define R7   (regs[7])

obj_t obj_retain(obj_t);
void  obj_release(obj_t);

void vm_assign(unsigned dst, obj_t val);
void vm_inst_alloc(unsigned dst, obj_t cl);
void vm_pushl(obj_t obj);
void vm_push(unsigned src);
void vm_pushm(unsigned src, unsigned n);
void vm_pop(unsigned dst);
void vm_popm(unsigned dst, unsigned n);
void vm_drop(void);
void vm_dropn(unsigned n);

void inst_init_passthru(obj_t cl, obj_t inst, va_list ap);
void inst_walk_passthru(obj_t cl, obj_t inst, void (*func)(obj_t));
void inst_free_passthru(obj_t cl, obj_t inst);

void cl_inst_init(obj_t cl, obj_t inst, va_list ap);
void cl_inst_walk(obj_t cl, obj_t inst, void (*func)(obj_t));
void cl_inst_free(obj_t cl, obj_t inst);
void inst_init(obj_t recvr, ...);

struct mc_frame {
    struct mc_frame *prev;
    obj_t           sel, args;
} *mcfp;

#define MC_FRAME_SEL       (mcfp->sel)
#define MC_FRAME_ARGS      (mcfp->args)
#define MC_FRAME_RECVR     (CAR(MC_FRAME_ARGS))
#define MC_FRAME_ARG_0     (CAR(CDR(MC_FRAME_ARGS)))
#define MC_FRAME_ARG_1     (CAR(CDR(CDR(MC_FRAME_ARGS))))
#define MC_FRAME_ARG_2     (CAR(CDR(CDR(CDR(MC_FRAME_ARGS)))))

void code_method_new(unsigned dst, void (*func)(unsigned));
void boolean_new(unsigned dst, unsigned val);
void integer_new(unsigned dst, long long val);
void float_new(unsigned dst, long double val);
void string_new(unsigned dst, unsigned n, ...);
unsigned string_hash(obj_t s);
unsigned string_equal(obj_t s1, obj_t s2);
void string_tocstr(unsigned dst, obj_t s);
void cons(unsigned dst, obj_t cl, obj_t car, obj_t cdr);
void _list_concat(obj_t li, obj_t obj);
void list_concat(obj_t li, obj_t obj);
void method_call_new(unsigned dst, obj_t list);
void block_new(unsigned dst, obj_t list);
void array_new(unsigned dst, unsigned size);
void _dict_new(unsigned dst, unsigned size, unsigned (*hash_func)(obj_t), unsigned (*equal_func)(obj_t, obj_t));
void dict_new(unsigned dst, unsigned size);

struct root_hdr {
    struct root_hdr *next;
    unsigned        size;
};

struct consts {
    struct root_hdr hdr;
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
        obj_t mapc;
	obj_t minus;
	obj_t modc;
        obj_t multc;
        obj_t name;
        obj_t new;
        obj_t newc;
	obj_t newc_modec;
	obj_t newc_parentc_instance_variablesc;
        obj_t newc_valuec;
        obj_t nil;
        obj_t not;
	obj_t orc;
        obj_t parent;
        obj_t pop;
	obj_t pquote;
        obj_t print;
        obj_t printc;
        obj_t push;
        obj_t quote;
        obj_t range;
        obj_t rangec;
	obj_t rangec_stepc;
        obj_t readc;
        obj_t readlnc;
	obj_t reducec_initc;
	obj_t _return;
	obj_t rindexc;
        obj_t shellc;
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
        
#ifdef DEBUG
        obj_t assertc;
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
    void (*func)(unsigned);
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

