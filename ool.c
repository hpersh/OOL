#include <errno.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <unistd.h>
#include <setjmp.h>
#include <dlfcn.h>
#include <assert.h>

#include "ool.h"

#define ASSERT  assert

#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

#define FIELD_OFS(s, f)                   ((long long) &((s *) 0)->f)
#define FIELD_PTR_TO_STRUCT_PTR(p, s, f)  ((s *)((char *)(p) - FIELD_OFS(s, f)))

#ifdef DEBUG
struct {
    unsigned vm    : 1;
    unsigned mem   : 1;
    unsigned parse : 1;
} debug;
#endif

void yy_push_file(FILE *fp, void *cookie), yy_push_str(char *, unsigned), yy_pop(void), yy_popall(void);
char *yycookie(void);
int  yyline(void);
int  yyparse();

/***************************************************************************/

enum fatal_errcode {
    FATAL_ERR_NO_MEM,
    FATAL_ERR_STACK_OVERFLOW,
    FATAL_ERR_STACK_UNDERFLOW,
    FATAL_ERR_DOUBLE_ERR,
    FATAL_ERR_BAD_ERR_STREAM
};

void
fatal(enum fatal_errcode errcode)
{
    char *msg;

    switch (errcode) {
    case FATAL_ERR_NO_MEM:
	msg = "Out of memory";
	break;
    case FATAL_ERR_STACK_OVERFLOW:
	msg = "Stack overflow";
	break;
    case FATAL_ERR_STACK_UNDERFLOW:
	msg = "Stack underflow";
	break;
    case FATAL_ERR_DOUBLE_ERR:
	msg = "Double error";
	break;
    case FATAL_ERR_BAD_ERR_STREAM:
	msg = "Bad strem for error output";
	break;
    default:
	ASSERT(0);
    }

    fprintf(stderr, "%s\n", msg);

    abort();
}

/***************************************************************************/

#define LIST_FIRST(list)  ((list)->next)
#define LIST_LAST(list)   ((list)->prev)
#define LIST_END(list)    (list)

unsigned
list_empty(struct list *list)
{
    ASSERT((LIST_FIRST(list) == list) == (LIST_LAST(list) == list));

    return (LIST_FIRST(list) == list);
}

void
list_init(struct list *list)
{
    list->prev = list->next = list;
}

void
list_insert(struct list *node, struct list *before)
{
    struct list *p = before->prev;

    node->prev = p;
    node->next = before;
    p->next = before->prev = node;
}

void
list_erase(struct list *node)
{
    struct list *p = node->prev, *q = node->next;

    p->next = q;
    q->prev = p;
}

/***************************************************************************/

obj_t *stack, *stack_end;

/***************************************************************************/

obj_t
inst_of(obj_t obj)
{
    return (obj ? obj->inst_of : consts.cl.object);
}

void
cl_inst_init(obj_t cl, obj_t inst, va_list ap)
{
    (*CLASS(cl)->inst_init)(cl, inst, ap);
}

void
inst_init_parent(obj_t cl, obj_t inst, va_list ap)
{
    cl_inst_init(CLASS(cl)->parent, inst, ap);
}

void meta_metaclass_walk(obj_t inst, void (*func)(obj_t));

void
cl_inst_walk(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    if (inst == consts.cl.metaclass) {
        meta_metaclass_walk(inst, func);
        return;
    }

    (*CLASS(cl)->inst_walk)(cl, inst, func);
}

void
inst_walk_parent(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    cl_inst_walk(CLASS(cl)->parent, inst, func);
}

void
cl_inst_free(obj_t cl, obj_t inst)
{
    (*CLASS(cl)->inst_free)(cl, inst);
}

void
inst_free_parent(obj_t cl, obj_t inst)
{
    cl_inst_free(CLASS(cl)->parent, inst);
}

void
inst_init(obj_t recvr, ...)
{
    va_list ap;

    va_start(ap, recvr);

    cl_inst_init(inst_of(recvr), recvr, ap);

    va_end(ap);
}

struct list obj_list[2];
unsigned obj_list_idx_active, obj_list_idx_marked;
#define OBJ_LIST_ACTIVE  (&obj_list[obj_list_idx_active])
#define OBJ_LIST_MARKED  (&obj_list[obj_list_idx_marked])
unsigned collectingf;

void
mem_init(void)
{
    unsigned i;

    for (i = 0; i < ARRAY_SIZE(obj_list); ++i)  list_init(&obj_list[i]);

    obj_list_idx_active = 0;
    obj_list_idx_marked = 1;
}

void collect();
unsigned initf;

#ifdef DEBUG

struct {
    struct {
        unsigned alloc_cnt;
        unsigned bytes_alloced;
        unsigned free_cnt;
        unsigned bytes_freed;
        unsigned bytes_in_use;
        unsigned bytes_in_use_max;
    } mem;
    struct {
        unsigned stack_depth;
        unsigned stack_depth_max;
    } vm;
} stats;

#define PRINT_INT(x)  printf(#x "\t= %d\n", x)

void
mem_stats_print(void)
{
    printf("\nMemory stats:\n");
    PRINT_INT(stats.mem.alloc_cnt);
    PRINT_INT(stats.mem.bytes_alloced);
    PRINT_INT(stats.mem.free_cnt);
    PRINT_INT(stats.mem.bytes_freed);
    PRINT_INT(stats.mem.bytes_in_use);
    PRINT_INT(stats.mem.bytes_in_use_max);
}

void
vm_stats_print(void)
{
    printf("\nVM stats:\n");
    PRINT_INT(stats.vm.stack_depth_max);    
}

obj_t mem_debug_addr;

void
mem_debug(obj_t obj)
{
    unsigned f = 0;

    if (obj != mem_debug_addr)  return;

    f = f;
}

#define MEM_DEBUG(obj)  mem_debug(obj)

void method_call_0(obj_t, obj_t);

void
stack_dump(void)
{
    obj_t *p, *sp_save = sp;

    printf("Stack dump:\n");
    for (p = sp; p < stack_end; ++p) {
	printf("%p: ", *p);
	method_call_0(*p, consts.str.print);
	printf("\n");
    }

    ASSERT(sp == sp_save);
}

#else

#define MEM_DEBUG(obj)

#endif

void *
cmalloc(unsigned size)
{
    static unsigned alloc_cnt, alloc_limit = (unsigned) -1;

    void *result = 0;
    
    if (!initf
        && (alloc_cnt >= alloc_limit || ((result = (void *) malloc(size)) == 0))
        ) {
        collect();
        if (alloc_cnt < alloc_limit)  alloc_limit = alloc_cnt / 2;
        alloc_cnt = 0;
    }

    if (result == 0 && ((result = malloc(size)) == 0)) {
	fatal(FATAL_ERR_NO_MEM);
    }

    if (!initf)  ++alloc_cnt;

#ifdef DEBUG
    ++stats.mem.alloc_cnt;
    stats.mem.bytes_alloced += size;
    stats.mem.bytes_in_use += size;
    if (stats.mem.bytes_in_use > stats.mem.bytes_in_use_max) {
        stats.mem.bytes_in_use_max = stats.mem.bytes_in_use;
    }
#endif

    return (result);
}

void
_cfree(void *p, unsigned size)
{
    if (p == 0)  return;

#ifdef DEBUG
    ++stats.mem.free_cnt;
    stats.mem.bytes_freed += size;
    stats.mem.bytes_in_use -= size;
#endif

    free(p);
}

void *
zcmalloc(unsigned size)
{
    void *result = cmalloc(size);

    memset(result, 0, size);

    return (result);
}

void
obj_free(obj_t obj)
{
    if (obj == NIL)  return;

    if (!collectingf)  cl_inst_walk(inst_of(obj), obj, obj_release);

    list_erase(&obj->list_node);

    cl_inst_free(inst_of(obj), obj);
}

void
obj_release(obj_t obj)
{
    MEM_DEBUG(obj);

    /* Reference loops do exist, so release of an obj with ref_cnt == 0 can
       happen, as freeing progresses.
    */

    if (obj == NIL || obj->ref_cnt == 0)  return;

    if (--obj->ref_cnt == 0)  obj_free(obj);
}

obj_t
obj_retain(obj_t obj)
{
    MEM_DEBUG(obj);

    if (obj) {
        ++obj->ref_cnt;

        ASSERT(obj->ref_cnt != 0);
    }

    return (obj);
}

void
_obj_assign(obj_t *dst, obj_t obj)
{
    obj_t old = *dst;

    *dst = obj;
    obj_release(old);
}

void
obj_assign(obj_t *dst, obj_t obj)
{
    _obj_assign(dst, obj_retain(obj));
}
#define OBJ_ASSIGN(dst, src)  (obj_assign(&(dst), (src)))

obj_t
obj_alloc(obj_t cl)
{
    obj_t result;

    result = (obj_t) zcmalloc(CLASS(cl)->inst_size);

    list_insert(&result->list_node, LIST_END(OBJ_LIST_ACTIVE));

    OBJ_ASSIGN(result->inst_of, cl);

    return (result);
}

void
obj_mark(obj_t obj)
{
    if (obj == NIL)  return;

    obj_retain(obj);
    
    if (obj->ref_cnt > 1)  return;

    list_erase(&obj->list_node);
    list_insert(&obj->list_node, LIST_END(OBJ_LIST_MARKED));

    cl_inst_walk(inst_of(obj), obj, obj_mark);
}

void
root_walk(void (*func)(obj_t))
{
    unsigned        i, n;
    obj_t           *p;
    struct root_hdr *r;
    
    for (i = 0; i < ARRAY_SIZE(regs); ++i)  (*func)(regs[i]);
    
    for (p = sp; p < stack_end; ++p)  (*func)(*p);
    
    (*func)(env);

    for (r = root; r; r = r->next) {
	for (p = (obj_t *)(r + 1), n = r->size; n; --n, ++p) {
	    (*func)(*p);
	}
    }
}

void
root_mark(void)
{
    /* Zero out all ref cnts */
    {
        struct list *p;
        
        for (p = LIST_FIRST(OBJ_LIST_ACTIVE); p != LIST_END(OBJ_LIST_ACTIVE); p = p->next) {
            obj_t q = FIELD_PTR_TO_STRUCT_PTR(p, struct obj, list_node);
            
            q->ref_cnt = 0;
        }
    }
        
    /* Mark everything referenced by root set.
       Root set = regs + stack + env + consts
    */

    root_walk(obj_mark);

#ifdef DEBUG
    /* Consistency checking */
    {
        struct list *p;

        for (p = LIST_FIRST(OBJ_LIST_ACTIVE); p != LIST_END(OBJ_LIST_ACTIVE); p = p->next) {
            obj_t q = FIELD_PTR_TO_STRUCT_PTR(p, struct obj, list_node);

            ASSERT(q->ref_cnt == 0);
        }
        for (p = LIST_FIRST(OBJ_LIST_MARKED); p != LIST_END(OBJ_LIST_MARKED); p = p->next) {
            obj_t q = FIELD_PTR_TO_STRUCT_PTR(p, struct obj, list_node);

            ASSERT(q->ref_cnt != 0);

	    /* Can reference loops cause ref_cnt different after marking?
	       Marking always starts wit root set, but reference counting
	       during normal alloc/retain/release/free operations may
	       be something different?
	    */
        }
    }
#endif
}

void
collect(void)
{
#ifdef DEBUG
    if (debug.mem) {
        printf("collect(): Starting...\n");
        mem_stats_print();
    }
#endif

    collectingf = 1;

    root_mark();

    /* Free everything left on active list */
    {
        struct list *p;

        while ((p = LIST_FIRST(OBJ_LIST_ACTIVE)) != LIST_END(OBJ_LIST_ACTIVE)) {
            obj_t q = FIELD_PTR_TO_STRUCT_PTR(p, struct obj, list_node);

            obj_free(q);
        }
    }

    /* Swap marked and active lists */
    {
        unsigned temp;
        
        temp                = obj_list_idx_active;
        obj_list_idx_active = obj_list_idx_marked;
        obj_list_idx_marked = temp;
    }

    collectingf = 0;

#ifdef DEBUG
    if (debug.mem) {
        printf("collect(): done\n");
        mem_stats_print();
    }
#endif
}

/***************************************************************************/

void
vm_assign(unsigned dst, obj_t val)
{
    OBJ_ASSIGN(regs[dst], val);
}

void
vm_inst_alloc(unsigned dst, obj_t cl)
{
    vm_assign(dst, obj_alloc(cl));
}

#ifdef DEBUG

#define VM_STATS_UPDATE_PUSH(n) \
    do {								\
	if ((stats.vm.stack_depth += (n)) > stats.vm.stack_depth_max) {	\
	    stats.vm.stack_depth_max = stats.vm.stack_depth;		\
	}								\
    } while (0)

#define VM_STATS_UPDATE_POP(n)   (stats.vm.stack_depth -= (n))

#else

#define VM_STATS_UPDATE_PUSH(n)
#define VM_STATS_UPDATE_POP(n)

#endif

void
vm_pushl(obj_t obj)
{
    if (sp <= stack)  fatal(FATAL_ERR_STACK_OVERFLOW);

    VM_STATS_UPDATE_PUSH(1);

    *--sp = obj_retain(obj);
}

void
vm_push(unsigned src)
{
    vm_pushl(regs[src]);
}

void
vm_pushm(unsigned src, unsigned n)
{
    obj_t *p;

    if ((sp - n) < stack)  fatal(FATAL_ERR_STACK_OVERFLOW);

    VM_STATS_UPDATE_PUSH(n);

    for (p = &regs[src]; n; --n, ++p)  *--sp = obj_retain(*p);
}

void
vm_pop(unsigned dst)
{
    if (sp >= stack_end)  fatal(FATAL_ERR_STACK_UNDERFLOW);

    VM_STATS_UPDATE_POP(1);

    _obj_assign(&regs[dst], *sp++);
}

void
vm_popm(unsigned dst, unsigned n)
{
    obj_t *p;

    if ((sp + n) > stack_end)  fatal(FATAL_ERR_STACK_UNDERFLOW);

    VM_STATS_UPDATE_POP(n);

    for (p = &regs[dst + n - 1]; n; --n, --p)  _obj_assign(p, *sp++);
}

void
vm_drop(void)
{
    if (sp >= stack_end)  fatal(FATAL_ERR_STACK_UNDERFLOW);

    VM_STATS_UPDATE_POP(1);

    obj_release(*sp++);
}

void
vm_dropn(unsigned n)
{
    if ((sp + n) > stack_end)  fatal(FATAL_ERR_STACK_UNDERFLOW);

    VM_STATS_UPDATE_POP(n);

    for (; n; --n)  obj_release(*sp++);
}

/***************************************************************************/

enum errcode {
    ERR_SYM_NOT_BOUND,
    ERR_NO_METHOD,
    ERR_INVALID_METHOD,
    ERR_INVALID_ARG,
    ERR_INVALID_VALUE,
    ERR_NUM_ARGS,
    ERR_BREAK,
    ERR_CONT,
    ERR_RETURN
};

void error(enum errcode errcode, ...);

/***************************************************************************/

#define MC_FRAME_BEGIN(s, a)			\
    {                                           \
	struct mc_frame __mcf[1];		\
						\
	__mcf->prev = mcfp;			\
	mcfp = __mcf;				\
	mcfp->sel  = (s);			\
	mcfp->args = (a);			

#define MC_FRAME_END				\
        mcfp = mcfp->prev;			\
    }

void method_call_0(obj_t recvr, obj_t sel);
void method_call_1(obj_t recvr, obj_t sel, obj_t arg1);
void method_call_2(obj_t recvr, obj_t sel, obj_t arg1, obj_t arg2);

unsigned string_hash(obj_t s), string_equal(obj_t s1, obj_t s2);
obj_t dict_at(obj_t dict, obj_t key);
void  dict_at_put(obj_t dict, obj_t key, obj_t val);

void
bt_print(obj_t outf)
{
    FILE            *fp = _FILE(outf)->fp;
    struct mc_frame *p;

    fprintf(fp, "Backtrace:\n");
    for (p = mcfp; p; p = p->prev) {
	method_call_1(p->sel, consts.str.printc, outf);
	fprintf(fp, " ");
	method_call_1(p->args, consts.str.printc, outf);
	fprintf(fp, "\n");
    }
}

void
method_run(obj_t func, unsigned argc)
{
    if (inst_of(func) == consts.cl.code_method) {
        (* CODE_METHOD(func)->func)(argc);
        
        return;
    }

    if (inst_of(func) == consts.cl.block) {
        method_call_1(func, consts.str.evalc, MC_FRAME_ARGS);

        return;
    }

    error(ERR_INVALID_METHOD, func);
}

void
method_call(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, sel = MC_FRAME_SEL, cl;
    unsigned sel_with_colon = 0;

    vm_push(1);

    if (STRING(sel)->data[STRING(sel)->size - 1] == ':') {
        string_new(1, 1, STRING(sel)->size - 1, STRING(sel)->data);
        sel_with_colon = 1;
    } else {
        vm_assign(1, sel);
    }

    cl = inst_of(recvr);
#if 0
    if (cl == NIL || cl == consts.cl.metaclass) {
#endif
    if (recvr == consts.cl.metaclass || cl == consts.cl.metaclass) {
        for (cl = recvr; cl; cl = CLASS(cl)->parent) {
            obj_t obj;

            if (argc <= 1 && (obj = dict_at(CLASS(cl)->cl_vars, R1))) {
		if (sel_with_colon) {
		    OBJ_ASSIGN(CDR(obj), MC_FRAME_ARG_0);
		}
		vm_assign(0, CDR(obj));
		goto done;
	    }

            if (obj = dict_at(CLASS(cl)->cl_methods, sel)) {
                method_run(CDR(obj), argc);
                goto done;
            }
        }
    }

    for (cl = inst_of(recvr); cl; cl = CLASS(cl)->parent) {
        obj_t obj;

        if (argc <= 1 && (obj = dict_at(CLASS(cl)->inst_vars, R1))) {
            obj_t *p = (obj_t *)((char *) recvr + INTEGER(CDR(obj))->val);

            if (sel_with_colon) {
                obj_assign(p, MC_FRAME_ARG_0);
            }
            vm_assign(0, *p);
            goto done;
        }

        if (obj = dict_at(CLASS(cl)->inst_methods, sel)) {
            method_run(CDR(obj), argc);
            goto done;
        }
    }

    error(ERR_NO_METHOD, sel);

 done:
    vm_pop(1);
}

void
method_call_0(obj_t recvr, obj_t sel)
{
    vm_pushl(sel);
    cons(0, consts.cl.list, recvr, NIL);
    vm_push(0);
    MC_FRAME_BEGIN(sp[1], sp[0]) {
        method_call(0);
    } MC_FRAME_END;
    vm_dropn(2);
}

void
method_call_1(obj_t recvr, obj_t sel, obj_t arg)
{
    vm_pushl(sel);
    cons(0, consts.cl.list, arg, NIL);
    cons(0, consts.cl.list, recvr, R0);
    vm_push(0);
    MC_FRAME_BEGIN(sp[1], sp[0]) {
        method_call(1);
    } MC_FRAME_END;
    vm_dropn(2);
}

void
method_call_2(obj_t recvr, obj_t sel, obj_t arg1, obj_t arg2)
{
    vm_pushl(sel);
    cons(0, consts.cl.list, arg2, NIL);
    cons(0, consts.cl.list, arg1, R0);
    cons(0, consts.cl.list, recvr, R0);
    vm_push(0);
    MC_FRAME_BEGIN(sp[1], sp[0]) {
        method_call(2);
    } MC_FRAME_END;
    vm_dropn(2);
}

/***************************************************************************/

jmp_buf jmp_buf_top;

unsigned err_depth;

void
error(enum errcode errcode, ...)
{
    obj_t   outf;
    FILE    *fp;
    va_list ap;
    obj_t   obj;
    void    *cookie;

    if (err_depth > 0) {
	fatal(FATAL_ERR_DOUBLE_ERR);
    }
    ++err_depth;

    method_call_0(consts.cl.file, consts.str._stderr);
    if (inst_of(R0) != consts.cl.file) {
	fatal(FATAL_ERR_BAD_ERR_STREAM);
    }
    fp = _FILE(outf = R0)->fp;

    if (cookie = yycookie()) {
	fprintf(fp, "File ");
	method_call_1(_FILE(cookie)->filename, consts.str.printc, outf);
	fprintf(fp, ", line %d\n", yyline());
    }

    va_start(ap, errcode);
    
    fprintf(fp, "\n");
    switch (errcode) {
    case ERR_SYM_NOT_BOUND:
	fprintf(fp, "Symbol not bound: ");
	obj = va_arg(ap, obj_t);
	method_call_1(obj, consts.str.printc, outf);
	break;
    case ERR_NO_METHOD:
	fprintf(fp, "No such method: ");
	obj = va_arg(ap, obj_t);
	method_call_1(obj, consts.str.printc, outf);
	break;
    case ERR_INVALID_METHOD:
	fprintf(fp, "Invalid method: ");
	obj = va_arg(ap, obj_t);
	method_call_1(obj, consts.str.printc, outf);
	break;
    case ERR_INVALID_ARG:
	fprintf(fp, "Invalid argument: ");
	obj = va_arg(ap, obj_t);
	method_call_1(obj, consts.str.printc, outf);
	break;
    case ERR_INVALID_VALUE:
	{
	    obj_t obj2;

	    obj  = va_arg(ap, obj_t);
	    obj2 = va_arg(ap, obj_t);
	    fprintf(fp, "Invalid value for ");
	    method_call_1(obj, consts.str.printc, outf);
	    fprintf(fp, ": ");
	    method_call_1(obj2, consts.str.printc, outf);
	}
	break;
    case ERR_NUM_ARGS:
	fprintf(fp, "Incorrect number of arguments");
	break;
    case ERR_BREAK:
	fprintf(fp, "break not within while:");
	break;
    case ERR_CONT:
	fprintf(fp, "continue not within while:");
	break;
    case ERR_RETURN:
	fprintf(fp, "return not within block");
	break;
    default:
	ASSERT(0);
    }

    fprintf(fp, "\n");
    bt_print(outf);

    va_end(ap);

    --err_depth;

    longjmp(jmp_buf_top, 1);
}

/***************************************************************************

Object hiearchies

Instance-of

  Object
    Metaclass
      Object
      Boolean
      Integer
      ...

Parent

  Object
    Metaclass
    Boolean
    Integer
    ...


Known reference loops include:
  inst_of(parent(#Metaclass) == #Metaclass
  inst_of(inst_of(#Metaclass)) == #Metaclass
  inst_of(name(#String)) == #String

***************************************************************************/

/* Metaclass itself */

/* Used when walking an object whose inst_of is NIL;
   see cl_inst_walk()
*/
void
meta_metaclass_walk(obj_t inst, void (*func)(obj_t))
{
    (*func)(CLASS(inst)->name);
    (*func)(CLASS(inst)->parent);
    (*func)(CLASS(inst)->cl_methods);
    (*func)(CLASS(inst)->cl_vars);
    (*func)(CLASS(inst)->inst_methods);
    (*func)(CLASS(inst)->inst_vars);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_name(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;
    
    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                     error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->name);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_tostring(unsigned argc)
{
    cm_meta_metaclass_name(argc);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_parent(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;
    
    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                     error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->parent);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_cl_methods(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;
    
    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                     error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->cl_methods);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_cl_vars(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;
    
    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                     error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->cl_vars);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_inst_methods(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;
    
    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                     error(ERR_NUM_ARGS);

    vm_assign(0, NIL);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_inst_vars(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;
    
    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                     error(ERR_NUM_ARGS);

    /* Must be hard-coded, because
       inst_vars(#Metaclass) only has mutable ones
    */

    cons(0, consts.cl.list, consts.str.instance_variables, NIL);
    cons(0, consts.cl.list, consts.str.instance_methods, R0);
    cons(0, consts.cl.list, consts.str.class_variables, R0);
    cons(0, consts.cl.list, consts.str.class_methods, R0);
    cons(0, consts.cl.list, consts.str.parent, R0);
    cons(0, consts.cl.list, consts.str.name, R0);
}

/***************************************************************************/

/* Class: Object */

void
inst_init_object(obj_t cl, obj_t inst, va_list ap)
{
    /* Do nothing */
}

void
inst_walk_object(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    (*func)(inst_of(inst));
}

void
inst_free_object(obj_t cl, obj_t inst)
{
    _cfree(inst, CLASS(inst_of(inst))->inst_size);
}

void
cm_object_new(unsigned argc)
{
    if (argc != 0)  error(ERR_NUM_ARGS);

    vm_inst_alloc(0, MC_FRAME_RECVR);
}

void
cm_object_quote(unsigned argc)
{
    if (argc != 0)  error(ERR_NUM_ARGS);

    vm_assign(0, MC_FRAME_RECVR);
}

void
cm_object_pquote(unsigned argc)
{
    cm_object_quote(argc);
}

void
cm_object_eval(unsigned argc)
{
    cm_object_quote(argc);
}

void
cm_object_instof(unsigned argc)
{
    if (argc != 0)  error(ERR_NUM_ARGS);

    vm_assign(0, inst_of(MC_FRAME_RECVR));
}

void
cm_object_eq(unsigned argc)
{
    if (argc != 1)  error(ERR_NUM_ARGS);

    boolean_new(0, MC_FRAME_RECVR == MC_FRAME_ARG_0);
}

void
cm_object_tostring(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, cl_name;
    char  buf[64];

    if (argc != 0)  error(ERR_NUM_ARGS);

    if (recvr == NIL) {
        vm_assign(0, consts.str.nil);
        return;
    }

    cl_name = CLASS(inst_of(recvr))->name;
    string_new(0, 3, snprintf(buf, sizeof(buf), "<inst @ %p, of class ", recvr), buf,
                     STRING(cl_name)->size, STRING(cl_name)->data,
                     1, ">"
               );
}

void
cm_object_print(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (argc != 0)  error(ERR_NUM_ARGS);

    method_call_0(recvr, consts.str.tostring);
    vm_assign(1, R0);
    method_call_0(R1, consts.str.print);

    vm_assign(0, recvr);
}

void
cm_object_printc(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (argc != 1)  error(ERR_NUM_ARGS);

    method_call_0(recvr, consts.str.tostring);
    vm_assign(1, R0);
    method_call_1(R1, consts.str.printc, MC_FRAME_ARG_0);

    vm_assign(0, recvr);
}

void
cm_object_append(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg;

    if (recvr != NIL)                    error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                       error(ERR_NUM_ARGS);
    arg = MC_FRAME_ARG_0;
    if (inst_of(arg) != consts.cl.list)  error(ERR_INVALID_ARG, arg);

    vm_assign(0, arg);
}

enum {
    WB_BREAK = 1,
    WB_CONT,
    WB_RETURN
};

struct wb_frame {
    struct wb_frame *prev;

    enum {
	WBF_TYPE_WHILE,
	WBF_TYPE_BLOCK
    } type;

    jmp_buf jmp_buf;
} *wbfp;

void
cm_object_while(unsigned argc)
{
    obj_t           recvr = MC_FRAME_RECVR, arg;
    struct wb_frame wbf[1];
    obj_t           *sp_save;
    struct mc_frame *mcfp_save;
    int             rc;

    if (argc != 1)  error(ERR_NUM_ARGS);
    arg = MC_FRAME_ARG_0;

    wbf->prev = wbfp;
    wbfp = wbf;
    wbfp->type = WBF_TYPE_WHILE;

    mcfp_save = mcfp;
    sp_save   = sp;
    
    if ((rc = setjmp(wbfp->jmp_buf)) != 0) {
	mcfp = mcfp_save;
	while (sp < sp_save)  vm_drop();

	switch (rc) {
	case WB_CONT:
	    break;
	case WB_BREAK:
	    goto done;
	default:
	    ASSERT(0);
	}
    }

    for (;;) {
	method_call_0(recvr, consts.str.eval);
	if (inst_of(R0) != consts.cl.boolean)  error(ERR_INVALID_VALUE, recvr, R0);
	if (!BOOLEAN(R0)->val)  break;
	method_call_0(arg, consts.str.eval);
    }

 done:
    wbfp = wbfp->prev;
}

void
cm_object_break(unsigned argc)
{
    struct wb_frame *p;

    if (argc != 0)  error(ERR_NUM_ARGS);
    for (p = wbfp; p; p = p->prev) {
	if (p->type == WBF_TYPE_WHILE)  break;
    }
    if (p == 0)  error(ERR_BREAK);

    vm_assign(0, MC_FRAME_RECVR);

    longjmp(p->jmp_buf, WB_BREAK);
}

void
cm_object_cont(unsigned argc)
{
    struct wb_frame *p;

    if (argc != 0)  error(ERR_NUM_ARGS);
    for (p = wbfp; p; p = p->prev) {
	if (p->type == WBF_TYPE_WHILE)  break;
    }
    if (p == 0)  error(ERR_CONT);

    longjmp(p->jmp_buf, WB_CONT);
}

void
cm_object_return(unsigned argc)
{
    struct wb_frame *p;

    if (argc != 0)  error(ERR_NUM_ARGS);
    for (p = wbfp; p; p = p->prev) {
	if (p->type == WBF_TYPE_BLOCK)  break;
    }
    if (p == 0)  error(ERR_RETURN);

    vm_assign(0, MC_FRAME_RECVR);

    longjmp(p->jmp_buf, WB_RETURN);
}

/***************************************************************************/

/* Class: Metaclass */

void
inst_walk_metaclass(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    (*func)(CLASS(inst)->name);
    (*func)(CLASS(inst)->parent);
    (*func)(CLASS(inst)->cl_methods);
    (*func)(CLASS(inst)->cl_vars);
    (*func)(CLASS(inst)->inst_methods);
    (*func)(CLASS(inst)->inst_vars);

    inst_walk_parent(cl, inst, func);
}

void
cm_metaclass_name(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                              error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->name);
}

void
cm_metaclass_tostring(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                              error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->name);
}

void
cm_metaclass_parent(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                              error(ERR_NUM_ARGS);

    vm_assign(0, CLASS(recvr)->parent);
}

void dict_keys(obj_t dict);

void
cm_metaclass_inst_vars(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                              error(ERR_NUM_ARGS);

    dict_keys(CLASS(recvr)->inst_vars);
}

void
inst_walk_user(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    unsigned ofs;
    obj_t    *p;
    
    for (ofs = CLASS(CLASS(cl)->parent)->inst_size, p = (obj_t *)((char *) inst + ofs);
         ofs < CLASS(cl)->inst_size;
         ofs += sizeof(obj_t), ++p
         ) {
        (*func)(*p);
    }

    inst_walk_parent(cl, inst, func);
}

void string_dict_new(unsigned dst, unsigned size);
obj_t env_new(obj_t, obj_t);

void
cm_metaclass_new(unsigned argc)
{
    obj_t    recvr = MC_FRAME_RECVR, p;
    unsigned inst_size;

    if (recvr != consts.cl.metaclass)  error(ERR_INVALID_ARG, recvr);
    if (argc != 3)                     error(ERR_NUM_ARGS);

    vm_push(1);

    vm_inst_alloc(0, consts.cl.metaclass);
    OBJ_ASSIGN(CLASS(R0)->name,   MC_FRAME_ARG_0);
    OBJ_ASSIGN(CLASS(R0)->parent, MC_FRAME_ARG_1);
    env_new(CLASS(R0)->name, R0);
    string_dict_new(1, 16);
    OBJ_ASSIGN(CLASS(R0)->cl_methods, R1);
    string_dict_new(1, 16);
    OBJ_ASSIGN(CLASS(R0)->cl_vars, R1);
    string_dict_new(1, 16);
    OBJ_ASSIGN(CLASS(R0)->inst_methods, R1);
    string_dict_new(1, 16);
    OBJ_ASSIGN(CLASS(R0)->inst_vars, R1);
    for (inst_size = CLASS(CLASS(R0)->parent)->inst_size, p = MC_FRAME_ARG_2;
         p;
         p = CDR(p), inst_size += sizeof(obj_t)
         ) {
        integer_new(1, inst_size);
        dict_at_put(CLASS(R0)->inst_vars, CAR(p), R1);
    }
    CLASS(R0)->inst_size = inst_size;
    CLASS(R0)->inst_init = inst_init_parent;
    CLASS(R0)->inst_walk = inst_walk_user;
    CLASS(R0)->inst_free = inst_free_parent;

    vm_pop(1);
}

/***************************************************************************/

/* Class: Code_Method */

void
inst_init_code_method(obj_t cl, obj_t inst, va_list ap)
{
    CODE_METHOD(inst)->func = va_arg(ap, void (*)(unsigned));

    inst_init_parent(cl, inst, ap);
}

void
code_method_new(unsigned dst, void (*func)(unsigned))
{
    vm_inst_alloc(dst, consts.cl.code_method);
    inst_init(regs[dst], func);
}

unsigned list_len(obj_t);

void
cm_code_method_eval(unsigned argc)
{
    obj_t    recvr = MC_FRAME_RECVR, args;
    unsigned nargs;

    if (inst_of(recvr) != consts.cl.code_method)  error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                                error(ERR_NUM_ARGS);
    args = MC_FRAME_ARG_0;
    if (inst_of(args) != consts.cl.list)  error(ERR_INVALID_ARG, args);
    nargs = list_len(args);
    if (nargs < 1)  error(ERR_NUM_ARGS);

    vm_pushl(recvr);
    vm_pushl(args);
    MC_FRAME_BEGIN(sp[1], sp[0]) {
        (*CODE_METHOD(recvr)->func)(nargs - 1);
    } MC_FRAME_END;
    vm_dropn(2);
}

/**********************************************************************/

/* Class: Boolean */

void
inst_init_boolean(obj_t cl, obj_t inst, va_list ap)
{
    BOOLEAN(inst)->val = va_arg(ap, unsigned);

    inst_init_parent(cl, inst, ap);
}

void
boolean_new(unsigned dst, unsigned val)
{
    vm_inst_alloc(dst, consts.cl.boolean);
    inst_init(regs[dst], val != 0);
}

void
cm_boolean_and(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                            error(ERR_NUM_ARGS);
    arg = MC_FRAME_ARG_0;
    if (inst_of(arg) != consts.cl.boolean)    error(ERR_INVALID_ARG, arg);

    boolean_new(0, BOOLEAN(recvr)->val && BOOLEAN(arg)->val);
}

void
cm_boolean_or(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                            error(ERR_NUM_ARGS);
    arg = MC_FRAME_ARG_0;
    if (inst_of(arg) != consts.cl.boolean)    error(ERR_INVALID_ARG, arg);

    boolean_new(0, BOOLEAN(recvr)->val || BOOLEAN(arg)->val);
}

void
cm_boolean_xor(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                            error(ERR_NUM_ARGS);
    arg = MC_FRAME_ARG_0;
    if (inst_of(arg) != consts.cl.boolean)    error(ERR_INVALID_ARG, arg);

    boolean_new(0, BOOLEAN(recvr)->val ^ BOOLEAN(arg)->val);
}

void
cm_boolean_not(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                            error(ERR_NUM_ARGS);

    boolean_new(0, !BOOLEAN(recvr)->val);
}

void
cm_boolean_tostring(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 0)                            error(ERR_NUM_ARGS);

    vm_assign(0, BOOLEAN(recvr)->val ? consts.str._true : consts.str._false);
}

void
cm_boolean_equals(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                            error(ERR_NUM_ARGS);
    arg = MC_FRAME_ARG_0;
    if (inst_of(arg) != consts.cl.boolean)    error(ERR_INVALID_ARG, arg);

    boolean_new(0, BOOLEAN(recvr)->val == BOOLEAN(arg)->val);
}

void
cm_boolean_if(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 1)                            error(ERR_NUM_ARGS);

    if (BOOLEAN(recvr)->val) {
	method_call_0(MC_FRAME_ARG_0, consts.str.eval);
    } else {
	vm_assign(0, recvr);
    }
}

void
cm_boolean_if_else(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    if (inst_of(recvr) != consts.cl.boolean)  error(ERR_INVALID_ARG, recvr);
    if (argc != 2)                            error(ERR_NUM_ARGS);

    method_call_0(BOOLEAN(recvr)->val ? MC_FRAME_ARG_0 : MC_FRAME_ARG_1, consts.str.eval);
}

/***************************************************************************/

/* Class: Integer */

void
inst_init_integer(obj_t cl, obj_t inst, va_list ap)
{
    INTEGER(inst)->val = va_arg(ap, long long);

    inst_init_parent(cl, inst, ap);
}

void
integer_new(unsigned dst, long long val)
{
    vm_inst_alloc(dst, consts.cl.integer);
    inst_init(regs[dst], val);
}

void
cm_integer_new(unsigned argc)
{
    obj_t arg;

    if (argc == 0) {
        integer_new(0, 0);
        return;
    }

    arg = MC_FRAME_ARG_0;
    
    if (inst_of(arg) == consts.cl.integer) {
        integer_new(0, INTEGER(arg)->val);
        return;
    }

    if (inst_of(arg) == consts.cl._float) {
        integer_new(0, (long long) FLOAT(arg)->val);
        return;
    }

    if (inst_of(arg) == consts.cl.string) {
        long long val = 0;
        char      *fmt;

        if (STRING(arg)->size >= 3
            && STRING(arg)->data[0] == '0'
            && (STRING(arg)->data[1] | 0x20) == 'x'
            ) {
            fmt = "%llx";
        } else {
            fmt = "%lld";
        }

        string_tocstr(0, arg);
        sscanf(STRING(R0)->data, fmt, &val);
        integer_new(0, val);
        
        return;
    }

    error(ERR_INVALID_ARG, arg);
}

void
cm_integer_tostring(unsigned argc)
{
    char buf[32];

    string_new(0, 1, snprintf(buf, sizeof(buf), "%lld", INTEGER(MC_FRAME_RECVR)->val), buf);
}

void
cm_integer_tostring_base(unsigned argc)
{
    obj_t     recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;
    long long val = INTEGER(recvr)->val, base;
    char      buf[32], *p;
    unsigned  n;

    if (inst_of(arg) != consts.cl.integer)  error(ERR_INVALID_ARG, arg);
    base = INTEGER(arg)->val;
    if (base <= 0 || base > 36)  error(ERR_INVALID_ARG, arg);

    for (p = &buf[ARRAY_SIZE(buf)], n = 0; n == 0 || val != 0; val /= base) {
	long long d = val % base;
	char      c;

	if (d <= 9) {
	    c = '0' + d;
	} else {
	    c = 'A' + d - 10;
	}

	ASSERT(n < sizeof(buf));

	*--p = c;
	++n;

	if (val == 0)  break;
    }

    string_new(0, 1, n, p);
}

void
cm_integer_hash(unsigned argc)
{
    vm_assign(0, MC_FRAME_RECVR);
}

void
cm_integer_equals(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    boolean_new(0,
		inst_of(arg) == consts.cl.integer
		&& INTEGER(MC_FRAME_RECVR)->val == INTEGER(arg)->val
		);
}

void
cm_integer_minus(unsigned argc)
{
    integer_new(0, -INTEGER(MC_FRAME_RECVR)->val);
}

void
cm_integer_add(unsigned argc)
{
    integer_new(0, INTEGER(MC_FRAME_RECVR)->val + INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_sub(unsigned argc)
{
    integer_new(0, INTEGER(MC_FRAME_RECVR)->val - INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_mult(unsigned argc)
{
    integer_new(0, INTEGER(MC_FRAME_RECVR)->val * INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_div(unsigned argc)
{
    integer_new(0, INTEGER(MC_FRAME_RECVR)->val / INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_mod(unsigned argc)
{
    integer_new(0, INTEGER(MC_FRAME_RECVR)->val % INTEGER(MC_FRAME_ARG_0)->val);
}

void
integer_range(long long init, long long lim, long long step)
{
    long long val;
    obj_t     *p;

    vm_pushm(1, 2);

    vm_assign(0, NIL);
    for (p = &R0, val = init; val < lim; val += step) {
        integer_new(1, val);
        cons(2, consts.cl.list, R1, NIL);
        obj_assign(p, R2);
        p = &CDR(R2);
    }

    vm_popm(1, 2);
}

void
cm_integer_range(unsigned argc)
{
    integer_range(0, INTEGER(MC_FRAME_RECVR)->val, 1);
}

void
cm_integer_range_init(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    if (inst_of(arg) != consts.cl.integer)  error(ERR_INVALID_ARG, arg);

    integer_range(INTEGER(arg)->val, INTEGER(MC_FRAME_RECVR)->val, 1);
}

void
cm_integer_range_init_step(unsigned argc)
{
    obj_t arg0 = MC_FRAME_ARG_0, arg1 = MC_FRAME_ARG_1;

    if (inst_of(arg0) != consts.cl.integer)  error(ERR_INVALID_ARG, arg0);
    if (inst_of(arg1) != consts.cl.integer)  error(ERR_INVALID_ARG, arg1);

    integer_range(INTEGER(arg0)->val, INTEGER(MC_FRAME_RECVR)->val, INTEGER(arg1)->val);
}

void
cm_integer_chr(unsigned argc)
{
    obj_t     recvr = MC_FRAME_RECVR;
    long long val = INTEGER(recvr)->val;
    char c;

    if (val < 0 || val > 127)  error(ERR_INVALID_ARG, recvr);

    c = val;
    string_new(0, 1, 1, &c);
}

void
cm_integer_lt(unsigned argc)
{
    boolean_new(0, INTEGER(MC_FRAME_RECVR)->val < INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_gt(unsigned argc)
{
    boolean_new(0, INTEGER(MC_FRAME_RECVR)->val > INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_le(unsigned argc)
{
    boolean_new(0, INTEGER(MC_FRAME_RECVR)->val <= INTEGER(MC_FRAME_ARG_0)->val);
}

void
cm_integer_ge(unsigned argc)
{
    boolean_new(0, INTEGER(MC_FRAME_RECVR)->val >= INTEGER(MC_FRAME_ARG_0)->val);
}

/***************************************************************************/

/* Class: Float */

void
inst_init_float(obj_t cl, obj_t inst, va_list ap)
{
    FLOAT(inst)->val = va_arg(ap, long double);

    inst_init_parent(cl, inst, ap);
}

void
float_new(unsigned dst, long double val)
{
    vm_inst_alloc(dst, consts.cl._float);
    inst_init(regs[dst], val);
}

void
cm_float_new(unsigned argc)
{
    obj_t arg;

    if (argc == 0) {
        float_new(0, 0.0);
        return;
    }

    arg = MC_FRAME_ARG_0;
    
    if (inst_of(arg) == consts.cl._float) {
        float_new(0, FLOAT(arg)->val);
        return;
    }

    if (inst_of(arg) == consts.cl.integer) {
        float_new(0, (long double) INTEGER(arg)->val);
        return;
    }

    if (inst_of(arg) == consts.cl.string) {
        long double val = 0.0;

        string_tocstr(0, arg);
        sscanf(STRING(R0)->data, "%Lf", &val);
        float_new(0, val);
        
        return;
    }

    ASSERT(0);                  /* Wrong arg type */
}

void
cm_float_add(unsigned argc)
{
    float_new(0, FLOAT(MC_FRAME_RECVR)->val + FLOAT(MC_FRAME_ARG_0)->val);
}

void
cm_float_sub(unsigned argc)
{
    float_new(0, FLOAT(MC_FRAME_RECVR)->val - FLOAT(MC_FRAME_ARG_0)->val);
}

void
cm_float_mult(unsigned argc)
{
    float_new(0, FLOAT(MC_FRAME_RECVR)->val * FLOAT(MC_FRAME_ARG_0)->val);
}

void
cm_float_div(unsigned argc)
{
    float_new(0, FLOAT(MC_FRAME_RECVR)->val / FLOAT(MC_FRAME_ARG_0)->val);
}

void
cm_float_minus(unsigned argc)
{
    float_new(0, -FLOAT(MC_FRAME_RECVR)->val);
}

void
cm_float_hash(unsigned argc)
{
    integer_new(0, (long long) FLOAT(MC_FRAME_RECVR)->val);
}

void
cm_float_equals(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    boolean_new(0,
		inst_of(arg) == consts.cl._float
		&& FLOAT(MC_FRAME_RECVR)->val == FLOAT(arg)->val
		);
}

void
cm_float_tostring(unsigned argc)
{
    char buf[64];

    string_new(0, 1, snprintf(buf, sizeof(buf), "%Lg", FLOAT(MC_FRAME_RECVR)->val), buf);
}

/***************************************************************************/

/* Class: String */

void
inst_init_string(obj_t cl, obj_t inst, va_list ap)
{
    unsigned size = va_arg(ap, unsigned);

    if ((STRING(inst)->size = size) > 0) {
        STRING(inst)->data = cmalloc(STRING(inst)->size);
    }

    inst_init_parent(cl, inst, ap);
}

void
inst_free_string(obj_t cl, obj_t inst)
{
    if (STRING(inst)->data)  _cfree(STRING(inst)->data, STRING(inst)->size);

    inst_free_parent(cl, inst);
}

void
string_new(unsigned dst, unsigned n, ...)
{
    va_list  ap;
    unsigned nn, size;

    va_start(ap, n);
    for (size = 0, nn = n; nn; --nn) {
        unsigned s  = va_arg(ap, unsigned);
        char     *d = va_arg(ap, char *);

        size += s;
	d = d;			/* Suppress warning about unused var */
    }
    va_end(ap);

    vm_inst_alloc(dst, consts.cl.string);
    inst_init(regs[dst], size);

    va_start(ap, n);
    for (size = 0, nn = n; nn; --nn) {
        unsigned s  = va_arg(ap, unsigned);
        char     *d = va_arg(ap, char *);

        memcpy(STRING(regs[dst])->data + size, d, s);
        size += s;
    }
    va_end(ap);
}

void
string_tocstr(unsigned dst, obj_t s)
{
    char c = 0;

    string_new(dst, 2, STRING(s)->size, STRING(s)->data,
                       1,               &c
               );
}

unsigned
string_hash(obj_t s)
{
    unsigned result, n;
    char     *p;
    
    ASSERT(inst_of(s) == consts.cl.string);

    for (result = 0, p = STRING(s)->data, n = STRING(s)->size; n; --n, ++p) {
        result += *p;
    }

    return (result);
}

void
cm_string_hash(unsigned argc)
{
    integer_new(0, string_hash(MC_FRAME_RECVR));
}

unsigned
string_equal(obj_t s1, obj_t s2)
{
    ASSERT(inst_of(s1) == consts.cl.string && inst_of(s2) == consts.cl.string);

    return (STRING(s1)->size == STRING(s2)->size
            && memcmp(STRING(s1)->data, STRING(s2)->data, STRING(s1)->size) == 0
            );
}

void
cm_string_equal(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    boolean_new(0,
		inst_of(arg) == consts.cl.string
		&& string_equal(MC_FRAME_RECVR, arg)
		);
}

void
cm_string_tostring(unsigned argc)
{
    vm_assign(0, MC_FRAME_RECVR);
}

void
cm_string_pquote(unsigned argc)
{
    obj_t    recvr = MC_FRAME_RECVR;
    char     *p;
    unsigned n;

    for (p = STRING(recvr)->data, n = STRING(recvr)->size; n; --n, ++p) {
	if (isspace(*p)) {
	    string_new(0, 3, 1, "\"",
		             STRING(recvr)->size, STRING(recvr)->data, 
		             1, "\""
		       );
	    return;
	}
    }

    vm_assign(0, recvr);
}

void
cm_string_append(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;

    string_new(0, 2, STRING(recvr)->size, STRING(recvr)->data,
                     STRING(arg)->size, STRING(arg)->data
               );
}

obj_t env_at(obj_t s);

void
cm_string_eval(unsigned argc)
{
    vm_assign(0, env_at(MC_FRAME_RECVR));
}

void
string_print(obj_t s, FILE *fp)
{
    char     *p, c;
    unsigned n;

    for (p = STRING(s)->data, n = STRING(s)->size; n; --n, ++p) {
        c = *p;

        if (isprint(c) || isspace(c)) {
            putc(c, fp);
        } else {
            fprintf(fp, "\\x%02x", c);
        }
    }
}

void
cm_string_print(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    method_call_0(consts.cl.file, consts.str._stdout);
    if (inst_of(R0) != consts.cl.file)  error(ERR_INVALID_VALUE, consts.str._stdout, R0);

    string_print(recvr, _FILE(R0)->fp);

    vm_assign(0, recvr);
}

void
cm_string_printc(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;

    if (inst_of(arg) != consts.cl.file)  error(ERR_INVALID_ARG, arg);

    string_print(recvr, _FILE(arg)->fp);

    vm_assign(0, recvr);
}

void
cm_string_len(unsigned argc)
{
    integer_new(0, STRING(MC_FRAME_RECVR)->size);
}

void
string_substr(obj_t s, int ofs, int len)
{
    if (ofs < 0)  ofs = (int) STRING(s)->size + ofs;
    
    ASSERT(ofs >= 0 && (ofs + len) <= (int) STRING(s)->size);

    string_new(0, 1, len, STRING(s)->data + ofs);
}

void
cm_string_at(unsigned argc)
{
    string_substr(MC_FRAME_RECVR, INTEGER(MC_FRAME_ARG_0)->val, 1);
}

void
cm_string_at_len(unsigned argc)
{
    string_substr(MC_FRAME_RECVR, INTEGER(MC_FRAME_ARG_0)->val, INTEGER(MC_FRAME_ARG_1)->val);
}

void
cm_string_asc(unsigned arg)
{
    integer_new(0, STRING(MC_FRAME_RECVR)->data[0]);
}

void
cm_string_foreach(unsigned argc)
{
    obj_t    arg = MC_FRAME_ARG_0, *p;
    char     *s;
    unsigned n;

    vm_pushm(1, 3);

    vm_assign(1, NIL);
    for (p = &R1, s = STRING(MC_FRAME_RECVR)->data, n = STRING(MC_FRAME_RECVR)->size; n; --n, ++s) {
	string_new(3, 1, 1, s);
	cons(3, consts.cl.list, R3, NIL);
        method_call_1(arg, consts.str.evalc, R3);
        cons(2, consts.cl.list, R0, NIL);
        obj_assign(p, R2);
        p = &CDR(R2);
    }
    vm_assign(0, R1);

    vm_popm(1, 3);
}

int
string_index(obj_t s1, obj_t s2, unsigned ofs, int dir)
{
    char     *p, c = STRING(s2)->data[0];
    unsigned n = STRING(s1)->size, i;

    i = (dir < 0) ? n - 1 - ofs : ofs;
    for (p = STRING(s1)->data + i; n; --n, p += dir, i += dir) {
	if (*p == c)  return ((int) i);
    }
    return (-1);
}

void
cm_string_index(unsigned argc)
{
    integer_new(0, string_index(MC_FRAME_RECVR, MC_FRAME_ARG_0, 0, 1));
}

void
cm_string_rindex(unsigned argc)
{
    integer_new(0, string_index(MC_FRAME_RECVR, MC_FRAME_ARG_0, 0, -1));
}

void
cm_string_split(unsigned argc)
{
    obj_t    recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0, *p;
    unsigned ofs;

    vm_pushm(1, 3);

    vm_assign(1, NIL);
    for (p = &R1, ofs = 0; ofs < STRING(recvr)->size; ) {
	int      i = string_index(recvr, arg, ofs, 1);
	unsigned n = (i < 0) ? STRING(recvr)->size - ofs : (unsigned) i - ofs;

	string_new(2, 1, n, STRING(recvr)->data + ofs);
	cons(3, consts.cl.list, R2, NIL);
	obj_assign(p, R3);
	p = &CDR(R3);
	ofs += n + 1;
    }
    vm_assign(0, R1);

    vm_popm(1, 3);
}

void
read_eval(void)
{
    obj_t *sp_save;
    
    vm_push(1);

    vm_assign(1, NIL);
    for(sp_save = sp;;) {
        int rc = yyparse();

        while (sp < sp_save)  vm_drop(); /* Discard all objs created during parsing */

        if (rc != 0) break;

	vm_assign(1, R0);
        method_call_0(R1, consts.str.eval);
	vm_assign(1, R0);
    }
    vm_assign(0, R1);

    vm_pop(1);
}

void
cm_string_load(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    yy_push_str(STRING(recvr)->data, STRING(recvr)->size);

    read_eval();

    yy_pop();
}

/***************************************************************************/

/* Class: Dptr */

void
inst_init_dptr(obj_t cl, obj_t inst, va_list ap)
{
    obj_t car = va_arg(ap, obj_t);
    obj_t cdr = va_arg(ap, obj_t);

    OBJ_ASSIGN(DPTR(inst)->car, car);
    OBJ_ASSIGN(DPTR(inst)->cdr, cdr);

    inst_init_parent(cl, inst, ap);
}

void
cons(unsigned dst, obj_t cl, obj_t car, obj_t cdr)
{
    vm_push(dst);

    vm_inst_alloc(dst, cl);
    inst_init(regs[dst], car, cdr);

    vm_drop();
}

void
inst_walk_dptr(obj_t cl, obj_t inst, void (*func)(obj_t))
{
  (*func)(DPTR(inst)->car);
  (*func)(DPTR(inst)->cdr);

  inst_walk_parent(cl, inst, func);
}

void
cm_dptr_car(unsigned argc)
{
    vm_assign(0, CAR(MC_FRAME_RECVR));
}

void
cm_dptr_cdr(unsigned argc)
{
    vm_assign(0, CDR(MC_FRAME_RECVR));
}

void
cm_dptr_hash(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    vm_pushm(1, 2);

    method_call_0(CAR(recvr), consts.str.hash);
    vm_assign(1, R0);
    method_call_0(CDR(recvr), consts.str.hash);
    vm_assign(2, R0);
    method_call_1(R1, consts.str.addc, R2);

    vm_popm(1, 2);
}

void
cm_dptr_equals(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;

    vm_pushm(1, 2);

    method_call_1(CAR(recvr), consts.str.equalsc, CAR(arg));
    vm_assign(1, R0);
    method_call_1(CDR(recvr), consts.str.equalsc, CDR(arg));
    vm_assign(2, R0);
    method_call_1(R1, consts.str.andc, R2);

    vm_popm(1, 2);
}

/***************************************************************************/

/* Class: Pair */

void
cm_pair_eval(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    vm_push(1);

    method_call_0(CAR(recvr), consts.str.eval);
    vm_assign(1, R0);
    method_call_0(CDR(recvr), consts.str.eval);
    cons(0, consts.cl.pair, R1, R0);

    vm_pop(1);
}

void
cm_pair_tostring(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    vm_pushm(1, 2);

    method_call_0(CAR(recvr), consts.str.tostring);
    vm_assign(1, R0);
    method_call_0(CDR(recvr), consts.str.tostring);
    vm_assign(2, R0);
    string_new(0, 5, 1, "(",
	             STRING(R1)->size, STRING(R1)->data,
	             2, ", ",
	             STRING(R2)->size, STRING(R2)->data,
	             1, ")"
	       );

    vm_popm(1, 2);
}

void
cm_pair_at(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR,  arg = MC_FRAME_ARG_0, result;

    switch (INTEGER(arg)->val) {
    case 0:
	result = DPTR(recvr)->car;
	break;
    case 1:
	result = DPTR(recvr)->cdr;
	break;
    default:
	ASSERT(0);
    }

    vm_assign(0, result);
}

/***************************************************************************/

/* Class: List */

unsigned
list_len(obj_t list)
{
    unsigned result;

    for (result = 0; list; list = CDR(list), ++result);

    return (result);
}

void
cm_list_len(unsigned argc)
{
    integer_new(0, list_len(MC_FRAME_RECVR));
}

void
_list_concat(obj_t list, obj_t obj)
{
    obj_t p, q;

    for (p = list; q = CDR(p); p = q);
    OBJ_ASSIGN(CDR(p), obj);
}

void
list_concat(obj_t list, obj_t obj)
{
    vm_push(1);

    cons(1, consts.cl.list, obj, NIL);
    _list_concat(list, R1);

    vm_pop(1);
}

void
list_tostr(obj_t list, char *delim)
{
    char  c;
    obj_t p;

    vm_pushm(1, 2);

    string_new(1, 1, 0, 0);
    c = delim[0];
    for (p = list; p; p = CDR(p), c = ' ') {
        method_call_0(CAR(p), consts.str.tostring);
        string_new(2, 3, STRING(R1)->size, STRING(R1)->data,
                                        1,               &c,
                         STRING(R0)->size, STRING(R0)->data
                   );
        vm_assign(1, R2);
    }
    string_new(0, 2, STRING(R1)->size, STRING(R1)->data, 1, &delim[1]);

    vm_popm(1, 2);
}

void
cm_list_tostring(unsigned argc)
{
    list_tostr(MC_FRAME_RECVR, "()");
}

void
list_eval(obj_t list)
{
    obj_t *q;

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (q = &R1; list; list = CDR(list), q = &CDR(R2)) {
        method_call_0(CAR(list), consts.str.eval);
        cons(2, consts.cl.list, R0, NIL);
        obj_assign(q, R2);
    }
    vm_assign(0, R1);

    vm_popm(1, 2);
}

void
cm_list_eval(unsigned argc)
{
    list_eval(MC_FRAME_RECVR);
}

void
cm_list_map(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0, *p, q;

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (p = &R1, q = MC_FRAME_RECVR; q; q = CDR(q)) {
        method_call_1(arg, consts.str.evalc, CAR(q));
        cons(2, consts.cl.list, R0, NIL);
        obj_assign(p, R2);
        p = &CDR(R2);
    }
    vm_assign(0, R1);

    vm_popm(1, 2);
}

void
cm_list_foreach(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0, *p, q;

    vm_pushm(1, 3);

    vm_assign(1, NIL);
    for (p = &R1, q = MC_FRAME_RECVR; q; q = CDR(q)) {
        cons(3, consts.cl.list, CAR(q), NIL);
        method_call_1(arg, consts.str.evalc, R3);
        cons(2, consts.cl.list, R0, NIL);
        obj_assign(p, R2);
        p = &CDR(R2);
    }
    vm_assign(0, R1);

    vm_popm(1, 3);
}

void
cm_list_splice(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;

    vm_pushm(1, 2);

    string_new(1, 1, 0, 0);
    for ( ; recvr; recvr = CDR(recvr)) {
	method_call_0(CAR(recvr), consts.str.tostring);
	if (STRING(R1)->size == 0) {
	    string_new(2, 1, STRING(R0)->size, STRING(R0)->data);
	} else {
	    string_new(2, 3, STRING(R1)->size, STRING(R1)->data,
		             STRING(arg)->size, STRING(arg)->data,
		             STRING(R0)->size, STRING(R0)->data
		       );
	}
	vm_assign(1, R2);
    }
    vm_assign(0, R1);
    
    vm_popm(1, 2);
}

void
cm_list_append(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;
    obj_t *p, q;

    ASSERT(inst_of(arg) == consts.cl.list);

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (p = &R1, q = MC_FRAME_RECVR; q; q = CDR(q)) {
        cons(2, consts.cl.list, CAR(q), NIL);
	obj_assign(p, R2);
        p = &CDR(R2);
    }
    obj_assign(p, arg);
    vm_assign(0, R1);

    vm_popm(1, 2);
}

void
cm_list_hash(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    vm_pushm(1, 2);

    integer_new(1, 0);
    for ( ; recvr; recvr = CDR(recvr)) {
	method_call_0(CAR(recvr), consts.str.hash);
	vm_assign(2, R0);
	method_call_1(R1, consts.str.addc, R2);
	vm_assign(1, R0);
    }
    vm_assign(0, R1);

    vm_popm(1, 2);
}

void
cm_list_equals(unsigned argc)
{
    obj_t    recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;

    vm_pushm(1, 2);

    boolean_new(1, 1);
    for ( ;
	  BOOLEAN(R1)->val && recvr && arg;
	  recvr = CDR(recvr), arg = CDR(arg)
	  ) {
	method_call_1(CAR(recvr), consts.str.equalsc, CAR(arg));
	vm_assign(2, R0);
	method_call_1(R1, consts.str.andc, R2);
	vm_assign(1, R0);
    }
    if (recvr || arg)  BOOLEAN(R1)->val = 0;
    vm_assign(0, R1);

    vm_popm(1, 2);
}

void
cm_list_at(unsigned argc)
{
    unsigned i = INTEGER(MC_FRAME_ARG_0)->val;
    obj_t    p;

    for (p = MC_FRAME_RECVR; p; p = CDR(p), --i) {
	if (i == 0) {
	    vm_assign(0, CAR(p));
	    return;
	}
    }

    ASSERT(0);
}

void
cm_list_at_len(unsigned argc)
{
    unsigned i = INTEGER(MC_FRAME_ARG_0)->val;
    unsigned n = INTEGER(MC_FRAME_ARG_1)->val;
    obj_t    p, *q;

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (q = &R1, p = MC_FRAME_RECVR; p && n; p = CDR(p)) {
	if (i > 0) {
	    --i;
	    continue;
	}

	cons(2, consts.cl.list, CAR(p), NIL);
	obj_assign(q, R2);
	q = &CDR(R2);
	--n;
    }
    vm_assign(0, R1);

    vm_popm(1, 2);
}

/***************************************************************************/

/* Class: Method_Call */

void
inst_init_method_call(obj_t cl, obj_t inst, va_list ap)
{
    obj_t list = va_arg(ap, obj_t);

    OBJ_ASSIGN(METHOD_CALL(inst)->list, list);

    inst_init_parent(cl, inst, ap);
}

void
inst_walk_method_call(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    (*func)(METHOD_CALL(inst)->list);

    inst_walk_parent(cl, inst, func);
}

void
method_call_new(unsigned dst, obj_t list)
{
    vm_inst_alloc(dst, consts.cl.method_call);
    inst_init(regs[dst], list);
}

void
cm_method_call_new(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    ASSERT(inst_of(arg) == consts.cl.list);

    method_call_new(0, arg);
}

void
cm_method_call_eval(unsigned argc)
{
    obj_t    arg = METHOD_CALL(MC_FRAME_RECVR)->list;
    unsigned n, nargs, s, quotef = 0;
    obj_t    p, *q;
    char     *r;

    vm_pushm(1, 3);
    
    /* Scan to calculate length of selector */
    
    for (s = 0, n = 0, p = arg; p; p = CDR(p), ++n) {
	if (n & 1)  s += STRING(CAR(p))->size;
    }
    
    if (n == 2) {
	nargs = 0;
        
	quotef = string_equal(CAR(CDR(arg)), consts.str.quote);
    } else if (n >= 3) {
	ASSERT((n & 1) == 1);
	
	nargs = n >> 1;
    } else  ASSERT(0);
    
    vm_assign(1, NIL);
    vm_inst_alloc(2, consts.cl.string);
    inst_init(regs[2], s);
    for (q = &R1, r = STRING(R2)->data, n = 0, p = arg; p; p = CDR(p), ++n) {
	if (n & 1) {
	    s = STRING(CAR(p))->size;
	    memcpy(r, STRING(CAR(p))->data, s);
	    r += s;
	    continue;
	}
	
	cons(3, consts.cl.list, CAR(p), NIL);
	obj_assign(q, R3);
	q = &CDR(R3);
    }
    
    vm_push(2);
    if (quotef) {
	vm_push(1);
    } else {
	list_eval(R1);
	vm_push(0);
    }
    MC_FRAME_BEGIN(sp[1], sp[0]) {
	method_call(nargs);
    } MC_FRAME_END;
    vm_dropn(2);

    vm_popm(1, 3);
}

void
cm_method_call_tostring(unsigned argc)
{
    list_tostr(METHOD_CALL(MC_FRAME_RECVR)->list, "[]");
}

void
cm_list_filter(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0, *p;

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (p = &R1; recvr && arg; recvr = CDR(recvr), arg = CDR(arg)) {
	if (!BOOLEAN(CAR(arg))->val)  continue;

	cons(2, consts.cl.list, CAR(recvr), NIL);
	obj_assign(p, R2);
	p = &CDR(R2);
    }
    vm_assign(0, R1);

    vm_popm(1, 2);
}

void
cm_list_reduce(unsigned argc)
{
    obj_t body = MC_FRAME_ARG_0, p;

    vm_pushm(1, 2);
    
    vm_assign(1, MC_FRAME_ARG_1);
    for (p = MC_FRAME_RECVR; p; p = CDR(p)) {
	cons(2, consts.cl.list, CAR(p), NIL);
	cons(2, consts.cl.list, R1, R2);
	method_call_1(body, consts.str.evalc, R2);
	vm_assign(1, R0);
    }
    vm_assign(0, R1);

    vm_popm(1, 2);
}

/***************************************************************************/

/* Class: Block */

void
inst_init_block(obj_t cl, obj_t inst, va_list ap)
{
    obj_t list = va_arg(ap, obj_t);

    OBJ_ASSIGN(BLOCK(inst)->list, list);

    inst_init_parent(cl, inst, ap);
}

void
inst_walk_block(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    (*func)(BLOCK(inst)->list);

    inst_walk_parent(cl, inst, func);
}

void
block_new(unsigned dst, obj_t list)
{
    vm_inst_alloc(dst, consts.cl.block);
    inst_init(regs[dst], list);
}

void env_push(void), env_pop(void);

void
cm_block_eval(unsigned argc)
{
    obj_t           p, q;
    struct wb_frame wbf[1];
    obj_t           *sp_save;
    struct mc_frame *mcfp_save;
    int             rc;
    
    env_push();
    
    for (p = CAR(BLOCK(MC_FRAME_RECVR)->list), q = MC_FRAME_ARG_0; p; p = CDR(p), q = CDR(q)) {
        env_new(CAR(p), CAR(q));
    }

    wbf->prev = wbfp;
    wbfp = wbf;
    wbfp->type = WBF_TYPE_BLOCK;

    mcfp_save = mcfp;
    sp_save   = sp;
    
    if ((rc = setjmp(wbfp->jmp_buf)) != 0) {
	mcfp = mcfp_save;
	while (sp < sp_save)  vm_drop();

	switch (rc) {
	case WB_RETURN:
	    goto done;
	default:
	    ASSERT(0);
	}
    }

    vm_assign(0, NIL);
    for (p = CDR(BLOCK(MC_FRAME_RECVR)->list); p; p = CDR(p)) {
        method_call_0(CAR(p), consts.str.eval);
    }

 done:
    env_pop();
}

void
cm_block_tostring(unsigned argc)
{
    list_tostr(BLOCK(MC_FRAME_RECVR)->list, "{}");
}

/***************************************************************************/

/* Class: Array */

void
inst_init_array(obj_t cl, obj_t inst, va_list ap)
{
    unsigned size = va_arg(ap, unsigned);

    ARRAY(inst)->data = zcmalloc((ARRAY(inst)->size = size) * sizeof(obj_t));

    inst_init_parent(cl, inst, ap);
}

void
inst_walk_array(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    unsigned n;
    obj_t    *p;

    if (p = ARRAY(inst)->data) {
        for (n = ARRAY(inst)->size; n; --n, ++p)  (*func)(*p);
    }

    inst_walk_parent(cl, inst, func);
}

void
inst_free_array(obj_t cl, obj_t inst)
{
    _cfree(ARRAY(inst)->data, ARRAY(inst)->size * sizeof(obj_t));

    inst_free_parent(cl, inst);
}

void
array_new(unsigned dst, unsigned size)
{
    vm_inst_alloc(dst, consts.cl.array);
    inst_init(regs[dst], size);
}

void
cm_array_new(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    if (inst_of(arg) == consts.cl.integer) {
	array_new(0, INTEGER(MC_FRAME_ARG_0)->val);
	return;
    }
    if (inst_of(arg) == consts.cl.list) {
	obj_t    *p;
	unsigned n;

	array_new(0, list_len(arg));
	for (p = ARRAY(R0)->data, n = ARRAY(R0)->size; n; --n, ++p, arg = CDR(arg)) {
	    obj_assign(p, CAR(arg));
	}
	return;
    }

    ASSERT(0);
}

void
cm_array_at(unsigned argc)
{
    vm_assign(0, ARRAY(MC_FRAME_RECVR)->data[INTEGER(MC_FRAME_ARG_0)->val]);
}

void
cm_array_at_put(unsigned argc)
{
    obj_t val = MC_FRAME_ARG_1;

    obj_assign(&ARRAY(MC_FRAME_RECVR)->data[INTEGER(MC_FRAME_ARG_0)->val], val);
    
    vm_assign(0, val);
}

void
cm_array_tostring(unsigned argc)
{
    obj_t    *p, *q;
    unsigned n;

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (q = &R1, p = ARRAY(MC_FRAME_RECVR)->data, n = ARRAY(MC_FRAME_RECVR)->size; n; --n, ++p) {
	cons(2, consts.cl.list, *p, NIL);
	obj_assign(q, R2);
	q = &CDR(R2);
    }
    method_call_0(R1, consts.str.tostring);

    vm_popm(1, 2);
}

/***************************************************************************/

/* Class: Dictionary */

void
inst_init_dict(obj_t cl, obj_t inst, va_list ap)
{
    DICT(inst)->hash_func  = va_arg(ap, unsigned (*)(obj_t));
    DICT(inst)->equal_func = va_arg(ap, unsigned (*)(obj_t, obj_t));

    inst_init_parent(cl, inst, ap);
}

void
_dict_new(unsigned dst, unsigned size, unsigned (*hash_func)(obj_t), unsigned (*equal_func)(obj_t, obj_t))
{
    vm_inst_alloc(dst, consts.cl.dict);
    inst_init(regs[dst], hash_func, equal_func, size);
}

void
string_dict_new(unsigned dst, unsigned size)
{
    _dict_new(dst, size, string_hash, string_equal);
}


unsigned
dict_key_hash_default(obj_t k)
{
    method_call_0(k, consts.str.hash);
    return (INTEGER(R0)->val);
}

unsigned
dict_key_eq_default(obj_t k1, obj_t k2)
{
    method_call_1(k1, consts.str.equalsc, k2);
    return (BOOLEAN(R0)->val);
}

void
dict_new(unsigned dst, unsigned size)
{
    _dict_new(dst, size, dict_key_hash_default, dict_key_eq_default);
}

void
cm_dict_new(unsigned argc)
{
    dict_new(0, 32);
}

obj_t
dict_find(obj_t dict, obj_t key, obj_t **bucket)
{
    obj_t result = NIL, p;
    obj_t *b = &DICT(dict)->base.data[(*DICT(dict)->hash_func)(key) % DICT(dict)->base.size];

    for (p = *b; p; p = CDR(p)) {
        obj_t q = CAR(p);

        if ((*DICT(dict)->equal_func)(CAR(q), key)) {
            result = q;
            break;
        }
    }

    if (bucket)  *bucket = b;

    return (result);
}

obj_t
dict_at(obj_t dict, obj_t key)
{
    return (dict_find(dict, key, 0));
}

void
cm_dict_at(unsigned argc)
{
    vm_assign(0, dict_at(MC_FRAME_RECVR, MC_FRAME_ARG_0));
}

void
dict_at_put(obj_t dict, obj_t key, obj_t val)
{
    obj_t p, *bucket;

    if (p = dict_find(dict, key, &bucket)) {
        OBJ_ASSIGN(CDR(p), val);
    } else {
        vm_pushm(1, 2);

        cons(1, consts.cl.pair, key, val);
        cons(2, consts.cl.list, R1, *bucket);
        obj_assign(bucket, R2);

        vm_popm(1, 2);
    }
}

void
cm_dict_at_put(unsigned argc)
{
    obj_t val = MC_FRAME_ARG_1;

    dict_at_put(MC_FRAME_RECVR, MC_FRAME_ARG_0, val);

    vm_assign(0, val);
}

void
dict_del(obj_t dict, obj_t key)
{
    obj_t p, *q;

    if (dict_find(dict, key, &q)) {
        for (; p = *q; q = &CDR(p)) {
            obj_t r = CAR(p);

            if ((*DICT(dict)->equal_func)(CAR(r), key)) {
                vm_push(1);
                
                vm_assign(1, CDR(p));
                OBJ_ASSIGN(CDR(p), NIL);
                obj_assign(q, R1);

                vm_pop(1);

                break;
            }
        }
    }
}

void
cm_dict_del(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    dict_del(MC_FRAME_RECVR, arg);

    vm_assign(0, arg);
}

void
dict_keys(obj_t dict)
{
    obj_t    *p, *q, r;
    unsigned n;

    vm_push(1);

    vm_assign(0, NIL);
    for (p = &R0, q = DICT(dict)->base.data, n = DICT(dict)->base.size; n; --n, ++q) {
        for (r = *q; r; r = CDR(r)) {
            cons(1, consts.cl.list, CAR(CAR(r)), NIL);
            obj_assign(p, R1);
            p = &CDR(R1);
        }
    }

    vm_pop(1);
}

void
cm_dict_keys(unsigned argc)
{
    dict_keys(MC_FRAME_RECVR);
}

void
cm_dict_tostring(unsigned argc)
{
    obj_t    recvr = MC_FRAME_RECVR, *p, *q, r;
    unsigned n;

    vm_pushm(1, 2);

    vm_assign(1, NIL);
    for (p = &R1, q = DICT(recvr)->base.data, n = DICT(recvr)->base.size; n; --n, ++q) {
        for (r = *q; r; r = CDR(r)) {
            cons(2, consts.cl.list, CAR(r), NIL);
            obj_assign(p, R2);
            p = &CDR(R2);
        }
    }
    
    method_call_0(R1, consts.str.tostring);

    vm_popm(1, 2);
}

/***************************************************************************/

/* Class: Environment */

void
env_push(void)
{
    vm_pushm(1, 2);

    string_dict_new(1, 64);
    cons(2, consts.cl.list, R1, env);
    OBJ_ASSIGN(env, R2);

    vm_popm(1, 2);
}

void
env_pop(void)
{
    OBJ_ASSIGN(env, CDR(env));
}

void
cm_env_push(unsigned argc)
{
    env_push();
    
    vm_assign(0, NIL);
}

void
cm_env_pop(unsigned argc)
{
    env_pop();

    vm_assign(0, NIL);
}

obj_t
env_new(obj_t s, obj_t val)
{
    dict_at_put(CAR(env), s, val);

    return (val);
}

void
cm_env_new(unsigned argc)
{
    vm_assign(0, env_new(MC_FRAME_ARG_0, NIL));
}

void
cm_env_new_val(unsigned argc)
{
    vm_assign(0, env_new(MC_FRAME_ARG_0, MC_FRAME_ARG_1));
}

obj_t 
env_find(obj_t s)
{
    obj_t p, q;

    for (p = env; p; p = CDR(p)) {
        if (q = dict_at(CAR(p), s)) {
            return (q);
        }
    }

    return (NIL);
}

obj_t
env_at(obj_t s)
{
    obj_t p;

    if (p = env_find(s))  return (CDR(p));

    error(ERR_SYM_NOT_BOUND, s);

    ASSERT(0);                  /* Symbol not bound */
}

void
env_at_put(obj_t s, obj_t val)
{
    obj_t p;

    if (p = env_find(s)) {
        OBJ_ASSIGN(CDR(p), val);
    } else {
        dict_at_put(CAR(env), s, val);
    }
}

void
env_del(obj_t s)
{
    dict_del(CAR(env), s);
}

void
cm_env_at(unsigned argc)
{
    vm_assign(0, env_at(MC_FRAME_ARG_0));
}

void
cm_env_at_put(unsigned argc)
{
    obj_t val = MC_FRAME_ARG_1;

    env_at_put(MC_FRAME_ARG_0, val);

    vm_assign(0, val);
}

void
cm_env_del(unsigned argc)
{
    env_del(MC_FRAME_ARG_0);

    vm_assign(0, NIL);
}

/***************************************************************************/

/* Class: System */

void
cm_system_shell(unsigned argc)
{
    string_tocstr(0, MC_FRAME_ARG_0);

    integer_new(0, (long long) system(STRING(R0)->data));
}

extern int yydebug, yy_flex_debug;

#ifdef DEBUG

void
cm_system_debug(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;
    unsigned val = INTEGER(arg)->val;

    debug.vm = val;   val >>= 1;
    debug.mem = val;  val >>= 1;
    debug.parse = val;
    yy_flex_debug = yydebug = debug.parse;

    vm_assign(0, arg);
}

void
cm_system_assert(unsigned argc)
{
    obj_t arg = MC_FRAME_ARG_0;

    assert(inst_of(arg) == consts.cl.boolean && BOOLEAN(arg)->val != 0);

    vm_assign(0, arg);
}

void
cm_system_collect(unsigned argc)
{
    collect();

    vm_assign(0, NIL);
}

#endif

void
cm_system_exit(unsigned argc)
{
    exit(0);
}

void
cm_system_exitc(unsigned argc)
{
    exit(INTEGER(MC_FRAME_ARG_0)->val);
}

/***************************************************************************/

/* Class: File */

void
inst_init_file(obj_t cl, obj_t inst, va_list ap)
{
    obj_t filename = va_arg(ap, obj_t);
    obj_t mode     = va_arg(ap, obj_t);
    FILE *fp       = va_arg(ap, FILE *);

    _FILE(inst)->filename = filename;
    _FILE(inst)->mode     = mode;
    _FILE(inst)->fp       = fp;

    inst_init_parent(cl, inst, ap);
}

void
inst_walk_file(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    (*func)(_FILE(inst)->filename);
    (*func)(_FILE(inst)->mode);

    inst_walk_parent(cl, inst, func);
}

void
inst_free_file(obj_t cl, obj_t inst)
{
    fclose(_FILE(inst)->fp);

    inst_free_parent(cl, inst);
}

void
file_new(unsigned dst, obj_t filename, obj_t mode, FILE *fp)
{
    vm_inst_alloc(0, consts.cl.file);
    inst_init(R0, filename, mode, fp);
}

void
cm_file_new(unsigned argc)
{
    obj_t filename = MC_FRAME_ARG_0, mode = MC_FRAME_ARG_1;
    FILE *fp;

    vm_pushm(1, 2);

    string_tocstr(1, filename);
    string_tocstr(2, mode);

    fp = fopen(STRING(R1)->data, STRING(R2)->data);

    vm_popm(1, 2);

    file_new(0, filename, mode, fp);
}

void
cm_file_load(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR;

    yy_push_file(_FILE(recvr)->fp, recvr);

    read_eval();

    yy_pop();
}

void
file_read(FILE *fp, unsigned len, unsigned linef)
{
    char     *p;
    unsigned i;

    vm_pushm(1, 2);

    vm_inst_alloc(1, consts.cl.string);
    inst_init(R1, len);
    memset(STRING(R1)->data, 0, len);

    for (i = 0, p = STRING(R1)->data; len; --len, ++p, ++i) {
	int c = fgetc(fp);

	if (c == EOF || linef && c == '\n')  break;

	*p = c;
    }
    integer_new(2, i);
    cons(0, consts.cl.pair, R2, R1);

    vm_popm(1, 2);
}

void
cm_file_read(unsigned argc)
{
    file_read(_FILE(MC_FRAME_RECVR)->fp, INTEGER(MC_FRAME_ARG_0)->val, 0);
}

void
cm_file_readln(unsigned argc)
{
    file_read(_FILE(MC_FRAME_RECVR)->fp, INTEGER(MC_FRAME_ARG_0)->val, 1);
}

/***************************************************************************/

/* Class: Module */

void
inst_init_module(obj_t cl, obj_t inst, va_list ap)
{
    void *ptr = va_arg(ap, void *);

    MODULE(inst)->ptr = ptr;

    inst_init_parent(cl, inst, ap);
}

void
inst_free_module(obj_t cl, obj_t inst)
{
    dlclose(MODULE(inst)->ptr);

    inst_free_parent(cl, inst);
}

void
cm_module_new(unsigned argc)
{
    void *ptr;

    vm_push(1);

    vm_inst_alloc(0, consts.cl.module);
    string_tocstr(1, MC_FRAME_ARG_0);
    ptr = dlopen(STRING(R1)->data, RTLD_NOW);
    ASSERT(ptr != 0);
    inst_init(R0, ptr);

    vm_pop(1);
}

/***************************************************************************/

const unsigned STACK_SIZE = 8192;

void
vm_init(void)
{
    memset(regs, 0, sizeof(regs));

    stack = (obj_t *) malloc(STACK_SIZE * sizeof(obj_t));
    stack_end = stack + STACK_SIZE;

    sp = stack_end;
}

const struct init_cl init_cl_tbl[] = {
    { &consts.cl.object,
      0,
      &consts.str.Object,
      sizeof(struct obj),
      inst_init_object,
      inst_walk_object,
      inst_free_object
    },
    { &consts.cl.code_method,
      &consts.cl.object,
      &consts.str.Code_Method,
      sizeof(struct inst_code_method),
      inst_init_code_method,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl.boolean,
      &consts.cl.object,
      &consts.str.Boolean,
      sizeof(struct inst_boolean),
      inst_init_boolean,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl.integer,
      &consts.cl.object,
      &consts.str.Integer,
      sizeof(struct inst_integer),
      inst_init_integer,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl._float,
      &consts.cl.object,
      &consts.str.Float,
      sizeof(struct inst_float),
      inst_init_float,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl.string,
      &consts.cl.object,
      &consts.str.String,
      sizeof(struct inst_string),
      inst_init_string,
      inst_walk_parent,
      inst_free_string
    },
    { &consts.cl.dptr,
      &consts.cl.object,
      &consts.str.Dptr,
      sizeof(struct inst_dptr),
      inst_init_dptr,
      inst_walk_dptr,
      inst_free_parent
    },
    { &consts.cl.pair,
      &consts.cl.dptr,
      &consts.str.Pair,
      sizeof(struct inst_dptr),
      inst_init_parent,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl.list,
      &consts.cl.dptr,
      &consts.str.List,
      sizeof(struct inst_dptr),
      inst_init_parent,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl.method_call,
      &consts.cl.object,
      &consts.str.Method_Call,
      sizeof(struct inst_method_call),
      inst_init_method_call,
      inst_walk_method_call,
      inst_free_parent
    },
    { &consts.cl.block,
      &consts.cl.object,
      &consts.str.Block,
      sizeof(struct inst_block),
      inst_init_block,
      inst_walk_block,
      inst_free_parent
    },
    { &consts.cl.array,
      &consts.cl.object,
      &consts.str.Array,
      sizeof(struct inst_array),
      inst_init_array,
      inst_walk_array,
      inst_free_array
    },
    { &consts.cl.dict,
      &consts.cl.array,
      &consts.str.Dictionary,
      sizeof(struct inst_dict),
      inst_init_dict,
      inst_walk_parent,
      inst_free_parent
    },
    { &consts.cl.file,
      &consts.cl.object,
      &consts.str.File,
      sizeof(struct inst_file),
      inst_init_file,
      inst_walk_file,
      inst_free_file
    },
    { &consts.cl.module,
      &consts.cl.object,
      &consts.str.Module,
      sizeof(struct inst_module),
      inst_init_module,
      inst_walk_parent,
      inst_free_module
    },
    /* Not really instantiable... */
    { &consts.cl.env,
      &consts.cl.object,
      &consts.str.Environment
    },
    { &consts.cl.system,
      &consts.cl.object,
      &consts.str.System
    }
};

const struct init_str init_str_tbl[] = {
    { &consts.str.Array,       "#Array" },
    { &consts.str.Block,       "#Block" },
    { &consts.str.Boolean,     "#Boolean" },
    { &consts.str.Code_Method, "#Code_Method" },    
    { &consts.str.Dictionary,  "#Dictionary" },
    { &consts.str.Dptr,        "#Dptr" },
    { &consts.str.Environment, "#Environment" },
    { &consts.str.File,        "#File" },
    { &consts.str.Float,       "#Float" },
    { &consts.str.Integer,     "#Integer" },
    { &consts.str.List,        "#List" },    
    { &consts.str.Metaclass,   "#Metaclass" },    
    { &consts.str.Method_Call, "#Method-Call" },
    { &consts.str.Module,      "#Module" },
    { &consts.str.Object,      "#Object" },    
    { &consts.str.Pair,        "#Pair" },
    { &consts.str.String,      "#String" },
    { &consts.str.System,      "#System" },
    { &consts.str.addc,        "add:" },
    { &consts.str.andc,        "and:" },
    { &consts.str.appendc,     "append:" },
    { &consts.str.asc,         "asc" },
    { &consts.str.atc,         "at:" },
    { &consts.str.atc_lengthc, "at:length:" },
    { &consts.str.atc_putc,    "at:put:" },
    { &consts.str._break,      "break" },
    { &consts.str.car,         "car" },
    { &consts.str.cdr,         "cdr" },
    { &consts.str.chr,         "chr" },
    { &consts.str.class_methods, "class-methods" },
    { &consts.str.class_variables, "class-variables" },
    { &consts.str._continue,   "continue" },
    { &consts.str.deletec,     "delete:" },
    { &consts.str.divc,        "div:" },
    { &consts.str.equalsc,     "equals:" },
    { &consts.str.eval,        "eval" },
    { &consts.str.evalc,       "eval:" },
    { &consts.str.exit,        "exit" },
    { &consts.str.exitc,       "exit:" },
    { &consts.str._false,       "#false" },
    { &consts.str.filterc,     "filter:" },
    { &consts.str.foreachc,    "foreach:" },
    { &consts.str.gec,         "ge:" },
    { &consts.str.gtc,         "gt:" },
    { &consts.str.hash,        "hash" },
    { &consts.str.ifc,         "if:" },
    { &consts.str.ifc_elsec,   "if:else:" },
    { &consts.str.indexc,      "index:" },
    { &consts.str.instance_methods, "instance-methods" },
    { &consts.str.instance_variables, "instance-variables" },
    { &consts.str.instanceof,  "instance-of" },
    { &consts.str.keys,        "keys" },
    { &consts.str.lec,         "le:" },
    { &consts.str.length,      "length" },
    { &consts.str.load,        "load" },
    { &consts.str.ltc,         "lt:" },
    { &consts.str.mapc,        "map:" },
    { &consts.str.minus,       "minus" },
    { &consts.str.modc,        "mod:" },
    { &consts.str.multc,       "mult:" },
    { &consts.str.name,        "name" },
    { &consts.str.new,         "new" },
    { &consts.str.newc,        "new:" },
    { &consts.str.newc_modec,  "new:mode:" },
    { &consts.str.newc_parentc_instance_variablesc, "new:parent:instance-variables:" },
    { &consts.str.newc_valuec, "new:value:" },
    { &consts.str.nil,         "#nil" },
    { &consts.str.not,         "not" },
    { &consts.str.orc,         "or:" },
    { &consts.str.parent,      "parent" },
    { &consts.str.pop,         "pop" },
    { &consts.str.pquote,      "pquote" },
    { &consts.str.print,       "print" },
    { &consts.str.printc,      "print:" },
    { &consts.str.push,        "push" },
    { &consts.str.quote,       "quote" },
    { &consts.str.range,       "range" },
    { &consts.str.rangec,      "range:" },
    { &consts.str.rangec_stepc, "range:step:" },
    { &consts.str.readc,       "read:" },
    { &consts.str.readlnc,     "readln:" },
    { &consts.str.reducec_initc, "reduce:init:" },
    { &consts.str._return,     "return" },
    { &consts.str.rindexc,     "rindex:" },
    { &consts.str.shellc,      "shell:" },
    { &consts.str._stderr,     "stderr" },
    { &consts.str._stdin,      "stdin" },
    { &consts.str._stdout,     "stdout" },
    { &consts.str.splicec,     "splice:" },
    { &consts.str.splitc,      "split:" },
    { &consts.str.subc,        "sub:" },
    { &consts.str.tostring,    "tostring" },
    { &consts.str.tostringc,   "tostring:" },
    { &consts.str._true,       "#true" },
    { &consts.str.whilec,      "while:" },
    { &consts.str.xorc,        "xor:" }
#ifdef DEBUG
    ,
    { &consts.str.assertc,     "assert:" },
    { &consts.str.collect,     "collect" },
    { &consts.str.debugc,      "debug:" }
#endif
};

const struct init_method init_cl_method_tbl[] = {
    { &consts.cl.metaclass,   &consts.str.name,               cm_meta_metaclass_name },
    { &consts.cl.metaclass,   &consts.str.tostring,           cm_meta_metaclass_tostring },
    { &consts.cl.metaclass,   &consts.str.parent,             cm_meta_metaclass_parent },
    { &consts.cl.metaclass,   &consts.str.class_methods,      cm_meta_metaclass_cl_methods },
    { &consts.cl.metaclass,   &consts.str.class_variables,    cm_meta_metaclass_cl_vars },
    { &consts.cl.metaclass,   &consts.str.instance_methods,   cm_meta_metaclass_inst_methods },
    { &consts.cl.metaclass,   &consts.str.instance_variables, cm_meta_metaclass_inst_vars },
    { &consts.cl.metaclass,   &consts.str.newc_parentc_instance_variablesc, cm_metaclass_new },
    { &consts.cl.object,      &consts.str.new,      cm_object_new },
    { &consts.cl.object,      &consts.str._continue, cm_object_cont },
    { &consts.cl.integer,     &consts.str.new,      cm_integer_new },
    { &consts.cl.integer,     &consts.str.newc,     cm_integer_new },
    { &consts.cl._float,      &consts.str.new,      cm_float_new },
    { &consts.cl._float,      &consts.str.newc,     cm_float_new },
    { &consts.cl.method_call, &consts.str.newc,     cm_method_call_new },
    { &consts.cl.array,       &consts.str.newc,     cm_array_new },
    { &consts.cl.dict,        &consts.str.new,      cm_dict_new },
    { &consts.cl.file,        &consts.str.newc_modec, cm_file_new },
    { &consts.cl.module,      &consts.str.newc,     cm_module_new },
    { &consts.cl.system,      &consts.str.shellc,   cm_system_shell },
    { &consts.cl.system,      &consts.str.exit,     cm_system_exit },
    { &consts.cl.system,      &consts.str.exitc,    cm_system_exitc },
    { &consts.cl.env,         &consts.str.push,     cm_env_push },
    { &consts.cl.env,         &consts.str.pop,      cm_env_pop },
    { &consts.cl.env,         &consts.str.newc,     cm_env_new },
    { &consts.cl.env,         &consts.str.newc_valuec, cm_env_new_val },
    { &consts.cl.env,         &consts.str.atc,      cm_env_at },
    { &consts.cl.env,         &consts.str.atc_putc, cm_env_at_put },
    { &consts.cl.env,         &consts.str.deletec,  cm_env_del }
#ifdef DEBUG
    ,
    { &consts.cl.system,      &consts.str.assertc,  cm_system_assert },
    { &consts.cl.system,      &consts.str.collect,  cm_system_collect },
    { &consts.cl.system,      &consts.str.debugc,   cm_system_debug }
#endif
};

const struct init_method init_inst_method_tbl[] = {
    { &consts.cl.object,      &consts.str.quote,      cm_object_quote },
    { &consts.cl.object,      &consts.str.pquote,     cm_object_pquote },
    { &consts.cl.object,      &consts.str.instanceof, cm_object_instof },
    { &consts.cl.object,      &consts.str.eval,       cm_object_eval },
    { &consts.cl.object,      &consts.str.equalsc,    cm_object_eq },
    { &consts.cl.object,      &consts.str.tostring,   cm_object_tostring },
    { &consts.cl.object,      &consts.str.print,      cm_object_print },
    { &consts.cl.object,      &consts.str.printc,     cm_object_printc },
    { &consts.cl.object,      &consts.str.appendc,    cm_object_append },
    { &consts.cl.object,      &consts.str.whilec,     cm_object_while },
    { &consts.cl.object,      &consts.str._break,     cm_object_break },
    { &consts.cl.object,      &consts.str._return,    cm_object_return },
    { &consts.cl.metaclass,   &consts.str.name,       cm_metaclass_name },
    { &consts.cl.metaclass,   &consts.str.tostring,   cm_metaclass_tostring },
    { &consts.cl.metaclass,   &consts.str.parent,     cm_metaclass_parent },
    { &consts.cl.metaclass,   &consts.str.instance_variables, cm_metaclass_inst_vars },
    { &consts.cl.code_method, &consts.str.evalc,      cm_code_method_eval },
    { &consts.cl.boolean,     &consts.str.andc,       cm_boolean_and },
    { &consts.cl.boolean,     &consts.str.orc,        cm_boolean_or },
    { &consts.cl.boolean,     &consts.str.xorc,       cm_boolean_xor },
    { &consts.cl.boolean,     &consts.str.not,        cm_boolean_not },
    { &consts.cl.boolean,     &consts.str.ifc,        cm_boolean_if },
    { &consts.cl.boolean,     &consts.str.ifc_elsec,  cm_boolean_if_else },
    { &consts.cl.boolean,     &consts.str.tostring,   cm_boolean_tostring },
    { &consts.cl.boolean,     &consts.str.equalsc,    cm_boolean_equals },
    { &consts.cl.integer,     &consts.str.equalsc,    cm_integer_equals },
    { &consts.cl.integer,     &consts.str.addc,       cm_integer_add },
    { &consts.cl.integer,     &consts.str.subc,       cm_integer_sub },
    { &consts.cl.integer,     &consts.str.minus,      cm_integer_minus },
    { &consts.cl.integer,     &consts.str.multc,      cm_integer_mult },
    { &consts.cl.integer,     &consts.str.divc,       cm_integer_div },
    { &consts.cl.integer,     &consts.str.modc,       cm_integer_mod },
    { &consts.cl.integer,     &consts.str.range,      cm_integer_range },
    { &consts.cl.integer,     &consts.str.rangec,     cm_integer_range_init },
    { &consts.cl.integer,     &consts.str.rangec_stepc, cm_integer_range_init_step },
    { &consts.cl.integer,     &consts.str.hash,       cm_integer_hash },
    { &consts.cl.integer,     &consts.str.tostring,   cm_integer_tostring },
    { &consts.cl.integer,     &consts.str.tostringc,  cm_integer_tostring_base },
    { &consts.cl.integer,     &consts.str.chr,        cm_integer_chr },
    { &consts.cl.integer,     &consts.str.lec,        cm_integer_le },
    { &consts.cl.integer,     &consts.str.ltc,        cm_integer_lt },
    { &consts.cl.integer,     &consts.str.gec,        cm_integer_ge },
    { &consts.cl.integer,     &consts.str.gtc,        cm_integer_gt },
    { &consts.cl._float,      &consts.str.addc,       cm_float_add },
    { &consts.cl._float,      &consts.str.subc,       cm_float_sub },
    { &consts.cl._float,      &consts.str.multc,      cm_float_mult },
    { &consts.cl._float,      &consts.str.divc,       cm_float_div },
    { &consts.cl._float,      &consts.str.minus,      cm_float_minus },
    { &consts.cl._float,      &consts.str.hash,       cm_float_hash },
    { &consts.cl._float,      &consts.str.equalsc,    cm_float_equals },
    { &consts.cl._float,      &consts.str.tostring,   cm_float_tostring },
    { &consts.cl.string,      &consts.str.hash,       cm_string_hash },
    { &consts.cl.string,      &consts.str.equalsc,    cm_string_equal },
    { &consts.cl.string,      &consts.str.appendc,    cm_string_append },
    { &consts.cl.string,      &consts.str.tostring,   cm_string_tostring },
    { &consts.cl.string,      &consts.str.eval,       cm_string_eval },
    { &consts.cl.string,      &consts.str.print,      cm_string_print },
    { &consts.cl.string,      &consts.str.printc,     cm_string_printc },
    { &consts.cl.string,      &consts.str.length,     cm_string_len },
    { &consts.cl.string,      &consts.str.atc,        cm_string_at },
    { &consts.cl.string,      &consts.str.atc_lengthc, cm_string_at_len },
    { &consts.cl.string,      &consts.str.asc,        cm_string_asc },
    { &consts.cl.string,      &consts.str.foreachc,   cm_string_foreach },
    { &consts.cl.string,      &consts.str.indexc,     cm_string_index },
    { &consts.cl.string,      &consts.str.rindexc,    cm_string_rindex },
    { &consts.cl.string,      &consts.str.splitc,     cm_string_split },
    { &consts.cl.string,      &consts.str.load,       cm_string_load },
    { &consts.cl.string,      &consts.str.pquote,     cm_string_pquote },
    { &consts.cl.dptr,        &consts.str.car,        cm_dptr_car },
    { &consts.cl.dptr,        &consts.str.cdr,        cm_dptr_cdr },
    { &consts.cl.dptr,        &consts.str.hash,       cm_dptr_hash },
    { &consts.cl.dptr,        &consts.str.equalsc,    cm_dptr_equals },
    { &consts.cl.pair,        &consts.str.eval,       cm_pair_eval },
    { &consts.cl.pair,        &consts.str.tostring,   cm_pair_tostring },
    { &consts.cl.pair,        &consts.str.atc,        cm_pair_at },
    { &consts.cl.list,        &consts.str.length,     cm_list_len },
    { &consts.cl.list,        &consts.str.tostring,   cm_list_tostring },
    { &consts.cl.list,        &consts.str.eval,       cm_list_eval },
    { &consts.cl.list,        &consts.str.mapc,       cm_list_map },
    { &consts.cl.list,        &consts.str.foreachc,   cm_list_foreach },
    { &consts.cl.list,        &consts.str.splicec,    cm_list_splice },
    { &consts.cl.list,        &consts.str.appendc,    cm_list_append },
    { &consts.cl.list,        &consts.str.hash,       cm_list_hash },
    { &consts.cl.list,        &consts.str.equalsc,    cm_list_equals },
    { &consts.cl.list,        &consts.str.atc,        cm_list_at },
    { &consts.cl.list,        &consts.str.atc_lengthc, cm_list_at_len },
    { &consts.cl.list,        &consts.str.filterc,    cm_list_filter },
    { &consts.cl.list,        &consts.str.reducec_initc, cm_list_reduce },
    { &consts.cl.method_call, &consts.str.tostring,   cm_method_call_tostring },
    { &consts.cl.method_call, &consts.str.eval,       cm_method_call_eval },
    { &consts.cl.block,       &consts.str.evalc,      cm_block_eval },
    { &consts.cl.block,       &consts.str.tostring,   cm_block_tostring },
    { &consts.cl.array,       &consts.str.atc,        cm_array_at },
    { &consts.cl.array,       &consts.str.atc_putc,   cm_array_at_put },
    { &consts.cl.array,       &consts.str.tostring,   cm_array_tostring },
    { &consts.cl.dict,        &consts.str.atc,        cm_dict_at },
    { &consts.cl.dict,        &consts.str.atc_putc,   cm_dict_at_put },
    { &consts.cl.dict,        &consts.str.deletec,    cm_dict_del },
    { &consts.cl.dict,        &consts.str.keys,       cm_dict_keys },
    { &consts.cl.dict,        &consts.str.tostring,   cm_dict_tostring },
    { &consts.cl.file,        &consts.str.readc,      cm_file_read },
    { &consts.cl.file,        &consts.str.readlnc,    cm_file_readln },
    { &consts.cl.file,        &consts.str.load,       cm_file_load }
};

const struct init_inst_var init_inst_var_tbl[] = {
    { &consts.cl.metaclass, &consts.str.class_methods,    sizeof(struct obj) + 2 * sizeof(obj_t) },
    { &consts.cl.metaclass, &consts.str.class_variables,  sizeof(struct obj) + 3 * sizeof(obj_t) },
    { &consts.cl.metaclass, &consts.str.instance_methods, sizeof(struct obj) + 4 * sizeof(obj_t) },
};


void
init_cls(const struct init_cl *tbl, unsigned n)
{
    vm_push(1);

    for ( ; n; --n, ++tbl) {
        vm_inst_alloc(1, consts.cl.metaclass);
        obj_assign(tbl->pcl, R1);
        CLASS(*tbl->pcl)->inst_size = tbl->inst_size;
        CLASS(*tbl->pcl)->inst_init = tbl->inst_init;
        CLASS(*tbl->pcl)->inst_walk = tbl->inst_walk;
        CLASS(*tbl->pcl)->inst_free = tbl->inst_free;
        OBJ_ASSIGN(CLASS(*tbl->pcl)->parent, *tbl->pparent);
        string_dict_new(1, 16);
        OBJ_ASSIGN(CLASS(*tbl->pcl)->cl_methods, R1);
        string_dict_new(1, 16);
        OBJ_ASSIGN(CLASS(*tbl->pcl)->inst_methods, R1);
        string_dict_new(1, 16);
        OBJ_ASSIGN(CLASS(*tbl->pcl)->cl_vars, R1);
        string_dict_new(1, 16);
        OBJ_ASSIGN(CLASS(*tbl->pcl)->inst_vars, R1);
        OBJ_ASSIGN(CLASS(*tbl->pcl)->name, *tbl->pname);
        env_at_put(*tbl->pname, *tbl->pcl);
    }

    vm_pop(1);
}

void
init_strs(const struct init_str *tbl, unsigned n)
{
    vm_push(1);

    for ( ; n; --n, ++tbl) {
        string_new(1, 1, strlen(tbl->str), (char *) tbl->str);
        obj_assign(tbl->pobj, R1);
    }

    vm_pop(1);
}

void
init_cl_methods(const struct init_method *tbl, unsigned n)
{
    vm_push(1);

    for ( ; n; --n, ++tbl) {
        code_method_new(1, tbl->func);
        dict_at_put(CLASS(*tbl->pcl)->cl_methods, *tbl->psel, R1);
    }

    vm_pop(1);
}

void
init_inst_methods(const struct init_method *tbl, unsigned n)
{
    vm_push(1);

    for ( ; n; --n, ++tbl) {
        code_method_new(1, tbl->func);
        dict_at_put(CLASS(*tbl->pcl)->inst_methods, *tbl->psel, R1);
    }

    vm_pop(1);
}

void
init_inst_vars(const struct init_inst_var *tbl, unsigned n)
{
    vm_push(1);

    for ( ; n; --n, ++tbl) {
        integer_new(1, tbl->ofs);
        dict_at_put(CLASS(*tbl->pcl)->inst_vars, *tbl->psel, R1);
    }

    vm_pop(1);
}

void
root_add(struct root_hdr *hdr, unsigned size)
{
    hdr->size = size;
    hdr->next = root;
    
    root = hdr;
}


void
env_init(void)
{
    unsigned i;

    root_add(&consts.hdr, (sizeof(consts) - sizeof(consts.hdr)) / sizeof(obj_t));

    OBJ_ASSIGN(consts.cl.metaclass, (obj_t) zcmalloc(sizeof(struct inst_metaclass)));
    list_insert(&consts.cl.metaclass->list_node, LIST_END(OBJ_LIST_ACTIVE));
    CLASS(consts.cl.metaclass)->inst_size = sizeof(struct inst_metaclass);
    CLASS(consts.cl.metaclass)->inst_init = inst_init_parent;
    CLASS(consts.cl.metaclass)->inst_walk = inst_walk_metaclass;
    CLASS(consts.cl.metaclass)->inst_free = inst_free_parent;
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        vm_inst_alloc(0, consts.cl.metaclass);
        obj_assign(init_cl_tbl[i].pcl, R0);
        CLASS(*init_cl_tbl[i].pcl)->inst_size = init_cl_tbl[i].inst_size;
        CLASS(*init_cl_tbl[i].pcl)->inst_init = init_cl_tbl[i].inst_init;
        CLASS(*init_cl_tbl[i].pcl)->inst_walk = init_cl_tbl[i].inst_walk;
        CLASS(*init_cl_tbl[i].pcl)->inst_free = init_cl_tbl[i].inst_free;
    }

    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->parent, consts.cl.object);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        if (init_cl_tbl[i].pparent)  OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->parent, *init_cl_tbl[i].pparent);
    }

    OBJ_ASSIGN(consts.cl.metaclass->inst_of, consts.cl.object);

    string_dict_new(0, 16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->cl_methods, R0);
    string_dict_new(0, 16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->inst_methods, R0);
    string_dict_new(0, 16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->cl_vars, R0);
    string_dict_new(0, 16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->inst_vars, R0);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        string_dict_new(0, 16);
        OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->cl_methods, R0);
        string_dict_new(0, 16);
        OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->inst_methods, R0);
        string_dict_new(0, 16);
        OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->cl_vars, R0);
        string_dict_new(0, 16);
        OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->inst_vars, R0);
    }

    init_strs(init_str_tbl, ARRAY_SIZE(init_str_tbl));

    init_cl_methods(init_cl_method_tbl, ARRAY_SIZE(init_cl_method_tbl));
    init_inst_methods(init_inst_method_tbl, ARRAY_SIZE(init_inst_method_tbl));
    init_inst_vars(init_inst_var_tbl, ARRAY_SIZE(init_inst_var_tbl));

    OBJ_ASSIGN(env, 0);
    env_push();

    env_at_put(consts.str.nil, NIL);
    boolean_new(1, 1);
    env_at_put(consts.str._true, R1);
    boolean_new(1, 0);
    env_at_put(consts.str._false, R1);

    file_new(0, NIL, NIL, stdin);
    dict_at_put(CLASS(consts.cl.file)->cl_vars, consts.str._stdin, R0);
    file_new(0, NIL, NIL, stdout);
    dict_at_put(CLASS(consts.cl.file)->cl_vars, consts.str._stdout, R0);
    file_new(0, NIL, NIL, stderr);
    dict_at_put(CLASS(consts.cl.file)->cl_vars, consts.str._stderr, R0);

    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->name, consts.str.Metaclass);
    env_at_put(consts.str.Metaclass, consts.cl.metaclass);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->name, *init_cl_tbl[i].pname);
        env_at_put(*init_cl_tbl[i].pname, *init_cl_tbl[i].pcl);
    }
}

void
init(void)
{
    initf = 1;

    mem_init();
    vm_init();
    env_init();

    initf = 0;
}


int
yyerror(void)
{
    return (0);
}

#ifdef DEBUG

void
mem_check(void)
{
    struct list *p;
    
    for (p = LIST_FIRST(OBJ_LIST_ACTIVE); p != LIST_END(OBJ_LIST_ACTIVE); p = p->next) {
	obj_t q = FIELD_PTR_TO_STRUCT_PTR(p, struct obj, list_node);
	
	ASSERT(q->ref_cnt != 0);
    }

    root_mark();

    ASSERT(list_empty(OBJ_LIST_ACTIVE)); /* Everytning marked, nothing active */
}

#endif

void
fini(void)
{
#ifdef DEBUG
    {
        if (sp != stack_end)  printf("!!! Stack not empty!\n");
    }

    mem_check();

    mem_stats_print();
    vm_stats_print();
#endif
}


int
main(void)
{
#ifdef YYDEBUG
    yydebug = 1;
#endif
#ifndef YY_FLEX_DEBUG
    yy_flex_debug = 0;
#endif
    
    init();

    setjmp(jmp_buf_top);

    yy_popall();
    while (sp < stack_end)  vm_drop();
    mcfp = 0;
    wbfp  = 0;

    for (;;) {
        printf("\nok ");
        fflush(stdout);

        if (yyparse() != 0)  break;

        while (sp < stack_end)  vm_drop(); /* Discard all objs created during parsing */

	vm_assign(1, R0);
        method_call_0(R1, consts.str.eval);
	vm_assign(1, R0);
        method_call_0(R1, consts.str.print);
    }

    fini();

    return (0);
}

