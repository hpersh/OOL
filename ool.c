#include <errno.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <unistd.h>
#include <dlfcn.h>
#include <assert.h>

#include "ool.h"

#define ASSERT       assert
#define HARD_ASSERT  assert

#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

#define PTR_AS_INT                        int
#define FIELD_OFS(s, f)                   ((PTR_AS_INT) &((s *) 0)->f)
#define FIELD_PTR_TO_STRUCT_PTR(p, s, f)  ((s *)((char *)(p) - FIELD_OFS(s, f)))

#ifdef DEBUG
struct {
    unsigned vm    : 1;
    unsigned mem   : 1;
    unsigned parse : 1;
} debug;
#endif

/***************************************************************************

Design Notes

Passing objects around as parameters to C functions or as return values is OK
**as long as the object is anchored somewhere**, i.e. on the stack, in a VM register,
or as a child of the main module (i.e. accesible from the root set).

Any function that creates a new object must return it in a VM register.  The convention
shall be that all return values go in R0, the same as for code methods.

Any function that uses registers internally must save them to the stack and restore them.
This includes saving R0, even though R0 will be used to pass back the result.  An incoming
value may be in R0, thus it must be saved at the start of a function, and then dropped
at the end.  Unless a function is a leaf function AND it does not modify ANY registers, a
function should save and drop RO, in addition to saving and restoring any registers that
it uses as scratch storage.  Thus, the rules for function F are:
(1) if F uses R1 - R7, they must be saved and restored;
(2) if F uses R0, either if F will return a value in R0 or F calls any function that
    returns a value in R0, R0 must be saved and dropped or restored, depending whether
    F returns a value in R0 or not.

Function nomenclature to make the above easier:

xxx  - Utility function
     - Purely read-only w.r.t. VM registers
     - C return value, or void, and C args
     - Example: inst_of()

vm_xxx - VM function
       - Operates on registers and stack
       - void C type, regular C arguments
       - Do not use scratch registers
       - Examples: vm_push(reg)

m_xxx  - Helper functions for methods
       - void C type, regular C arguments
       - Return value in R0, if any
       - May use scratch registers, which are saved and restored
         - Arguments may reside in registers, so any reagisters used must be saved
           - Goes without saying for R1-R7, but if R0 is used as scratch e.g. by calling
             another m_xxx function, or if a value will be returned in R0, R0 must be saved on entry
       - GENERAL RULE: An m_xxx function must save R0, and either drop it (if returning in R0), or restore it (if not returning in R0)

cm_xxx - Code_Method
       - Same as m_xxx, except that args are standard, and guaranteed to be on the stack
       => Do not need to save any registers, except those used for scratch, as framework
          has placed arguments on the stack
			
***************************************************************************/

/* Globals */

obj_t *stack, *stack_end;	/* Stack start and end */

/* Forward decls */

obj_t dict_at(obj_t dict, obj_t key);
void  dict_new_put(obj_t dict, obj_t key, obj_t val);
void  dict_at_put(obj_t dict, obj_t key, obj_t val);
void  dict_del(obj_t dict, obj_t key);

/***************************************************************************/

/* Fatal error handling */

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

    fprintf(stderr, "Fatal error: %s\n", msg);

    abort();
}

/***************************************************************************/

/* Linked-list handling */

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

obj_t
inst_of(obj_t obj)
{
    return (obj ? obj->inst_of : consts.cl.object);
}

unsigned
is_subclass_of(obj_t cl1, obj_t cl2)
{
    for ( ; cl1; cl1 = CLASS(cl1)->parent) {
	if (cl1 == cl2)  return (1);
    }

    return (0);
}

unsigned
is_kind_of(obj_t obj, obj_t cl)
{
    return (is_subclass_of(inst_of(obj), cl));
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
obj_list_swap(void)
{
  unsigned temp;

  temp                = obj_list_idx_active;
  obj_list_idx_active = obj_list_idx_marked;
  obj_list_idx_marked = temp;
}

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


#define PRINT_VAR(x, f)  printf(#x "\t= " f "\n", x)

void
mem_stats_print(void)
{
    printf("\nMemory stats:\n");
    PRINT_VAR(stats.mem.alloc_cnt,        "%d");
    PRINT_VAR(stats.mem.bytes_alloced,    "%d");
    PRINT_VAR(stats.mem.free_cnt,         "%d");
    PRINT_VAR(stats.mem.bytes_freed,      "%d");
    PRINT_VAR(stats.mem.bytes_in_use,     "%d");
    PRINT_VAR(stats.mem.bytes_in_use_max, "%d");
}

void
vm_stats_print(void)
{
    printf("\nVM stats:\n");
    PRINT_VAR(stats.vm.stack_depth,     "%d");
    PRINT_VAR(stats.vm.stack_depth_max, "%d");
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

void
stack_dump(void)
{
    obj_t *p, *sp_save = sp;

    printf("Stack dump:\n");
    for (p = sp; p < stack_end; ++p) {
	printf("%p: ", *p);
	vm_method_call_1(consts.str.print, *p);
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
    
    (*func)(module_main);

    for (p = sp; p < stack_end; ++p)  (*func)(*p);
    
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
            
#ifdef DEBUG
	    q->old_ref_cnt = q->ref_cnt;
#endif
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
	    ASSERT(q->ref_cnt == q->old_ref_cnt);
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

    obj_list_swap();		/* Swap marked and active lists */

    collectingf = 0;

#ifdef DEBUG
    if (debug.mem) {
        printf("collect(): done\n");
        mem_stats_print();
    }
#endif
}

/***************************************************************************/

/* Design Notes

We need a frame mechanism, for tracking history of:
- method calls, for printing backtraces, and resolving symbol lookups (via modules);
- input files, also for backtraces;
- blocks, for resolving symbol lookups;

Symbol resolution:
- locals i.e. blocks first, then globals i.e. modules
- env_at
  . Search through frames, newest to oldest, search dict in each BLOCK frame, i.e.
    local variables, by invocation
  . Search modules, current to parent, search dict in each module, i.e. module namespaces,
    by inclusion (parentage)
- env_new_put
  . Search through frames, for first BLOCK or MODULE frame, add to dict
- env_at_put
  . Find as in env_at; if found, change value, else do env_new_put
*/

#define FRAME_INIT(f, t)	       \
  (f)->type = (t);		       \
  (f)->prev = frp;		       \
  frp = (f)

#define FRAME_POP  frp = frp->prev

#define FRAME_JMP_INIT(f, t, a)						\
  FRAME_INIT(&(f)->base, (t));						\
  (f)->sp = sp;								\
  (a) = setjmp((f)->jmp_buf)

#define FRAME_RESTART_BEGIN {				\
    struct frame_jmp __frame[1];			\
    int              errorf;				\
    FRAME_JMP_INIT(__frame, FRAME_TYPE_RESTART, errorf);

#define FRAME_RESTART_END \
    FRAME_POP;		  \
  }

#define FRAME_WHILE_BEGIN {			\
    struct frame_jmp __frame[1];		\
    int              while_arg;			\
    FRAME_JMP_INIT(__frame, FRAME_TYPE_WHILE, while_arg);

#define FRAME_WHILE_POP \
  do { FRAME_POP; } while (0)

#define FRAME_WHILE_END  \
    FRAME_WHILE_POP;
  }

#define FRAME_INPUT_BEGIN(fi) {				\
    struct frame_input __frame[1];			\
    FRAME_INIT(&__frame->base, FRAME_TYPE_INPUT);	\
    __frame->file     = (fi);				\
    __frame->line     = 1;				\
    yy_inp_push(__frame);

#define FRAME_INPUT_POP \
  do { yy_inp_pop();  FRAME_POP; } while (0)

#define FRAME_INPUT_END				\
    FRAME_INPUT_POP;				\
  }

#define FRAME_METHOD_CALL_BEGIN(s, a) {				\
    struct frame_method_call __frame[1];			\
    FRAME_INIT(&__frame->base, FRAME_TYPE_METHOD_CALL);		\
    __frame->cl   = NIL;					\
    __frame->sel  = (s);					\
    __frame->args = (a);

#define FRAME_METHOD_CALL_POP \
  do { FRAME_POP; } while (0)

#define FRAME_METHOD_CALL_END \
    FRAME_METHOD_CALL_POP;
  }

#define FRAME_BLOCK_BEGIN(d) {						\
    struct frame_block __frame[1];					\
    int                block_arg;					\
    __frame->dict = (d);						\
    FRAME_JMP_INIT(&__frame->base, FRAME_TYPE_BLOCK, block_arg);

#define FRAME_BLOCK_POP \
  do { FRAME_POP; } while (0)

#define FRAME_BLOCK_END				\
    FRAME_BLOCK_POP;				\
  }

#define FRAME_MODULE_BEGIN(m) {				\
    struct frame_module __frame[1];			\
    __frame->module = (m);				\
    __frame->module_prev = module_cur;			\
    module_cur = __frame->module;			\
    FRAME_INIT(&__frame->base, FRAME_TYPE_MODULE);

#define FRAME_MODULE_POP \
  do { module_cur = frp->module_prev;  FRAME_POP; } while (0)

#define FRAME_MODULE_END			\
    FRAME_MODULE_POP;
  }

struct frame *frp;
obj_t        module_main;

void
frame_goto(enum frame_type type, int longjmp_arg)
{
    struct frame *p;

    switch (type) {
    case FRAME_TYPE_RESTART:
    case FRAME_TYPE_WHILE:
    case FRAME_TYPE_BLOCK:
	break;
    default:
	HARD_ASSERT(0);
    }

    for (;;) {
      if (frp->type == type)  break;

      switch (frp->type) {
      case FRAME_TYPE_INPUT:
	FRAME_INPUT_POP;
	continue;
	
      case FRAME_TYPE_METHOD_CALL:
	FRAME_METHOD_CALL_POP;
	continue;
	
      case FRAME_TYPE_WHILE:
	FRAME_WHILE_POP;
	continue;
	
      case FRAME_TYPE_BLOCK:
	FRAME_BLOCK_POP;
	continue;
	
      case FRAME_TYPE_MODULE:
	FRAME_MODULE_POP;
	continue;
	
      default:
	HARD_ASSERT(0);
      }
    }

    vm_dropn(FRAME_JMP(frp)->sp - sp);
    longjmp(FRAME_JMP(frp)->jmp_buf, longjmp_arg);
}

#define BLOCK_RETURN  (frame_goto(FRAME_TYPE_BLOCK, 1))
enum { WHILE_ARG_CONT = 1, WHILE_ARG_BREAK };
#define WHILE_CONT   (frame_goto(FRAME_TYPE_WHILE, WHILE_ARG_CONT))
#define WHILE_BREAK  (frame_goto(FRAME_TYPE_WHILE, WHILE_ARG_BREAK))





void
env_find(obj_t s, obj_t *pp, obj_t *pdict)
{
  struct frame *p;

  if (!is_kind_of(s, consts.cl.string))  error(ERR_INVALID_ARG, s);
  
  for (p = frp; p; p = p->prev) {
    if (p->type == FRAME_TYPE_BLOCK) {
      
    }
  }
}



void
env_find(obj_t s, obj_t *pr, obj_t *dn)
{
    struct frame *p;
    obj_t r = NIL, dd = NIL, d, mm = NIL;

    if (!is_kind_of(s, consts.cl.string))  error(ERR_INVALID_ARG, s);

    for (p = frp; p; p = p->prev) {
      switch (p->type) {
      case FRAME_TYPE_BLOCK:
	d = FRAME_BLOCK(p)->dict;
	break;
      case FRAME_TYPE_MODULE:
	if (mm == NIL)  mm = FRAME_MODULE(p)->module;
	d = MODULE(m)->dict;
	break;
      default:
	continue;
      }

      if (dd == NIL)  dd = d;
      if (pr == 0
	  ||(p->type == FRAME_TYPE_BLOCK) && (r = dict_at(d, s))
	  )  goto done;
    }

    for ( ; mm; mm = MODULE(mm)->parent) {
      if (r = dict_at(MODULE(mm)->dict, s))  break;
    }
    
 done:
    if (pr)  *pr = r;
    if (dn)  *dn = dd;

    return;
}


obj_t
env_at(obj_t s)
{
  obj_t pr;

  env_find(s, &pr, 0);
  if (pr == NIL)  error(ERR_SYM_NOT_BOUND, s);

  return (CDR(pr));
}

void
env_at_put(obj_t s, obj_t val)
{
  obj_t pr, dn;
  
  env_find(s, &pr, &dn);
  if (pr) {
    OBJ_ASSIGN(CDR(pr), val);
  } else {
    dict_at_put(dn, s, val);
  }
}

void
env_new_put(obj_t s, obj_t val)
{
  obj_t dn;

  env_find(s, 0, &dn);
  dict_at_put(dn, s, val);
}

void
env_del(obj_t s)
{
  obj_t dn;

  env_find(s, 0, &dn);
  dict_del(dn, s);
}

/***************************************************************************/

void
vm_assign(unsigned dst, obj_t val)
{
    ASSERT(dst < ARRAY_SIZE(regs));

    OBJ_ASSIGN(regs[dst], val);
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

#define VM_STACK_CHK_DN(n)  do { if ((sp - (n)) < stack)      fatal(FATAL_ERR_STACK_OVERFLOW); } while (0)
#define VM_STACK_CHK_UP(n)  do { if ((sp + (n)) > stack_end)  fatal(FATAL_ERR_STACK_UNDERFLOW); } while (0)


void
vm_pushl(obj_t obj)
{
    VM_STACK_CHK_DN(1);

    VM_STATS_UPDATE_PUSH(1);

    *--sp = obj_retain(obj);
}

void
vm_push(unsigned src)
{
    ASSERT(src < ARRAY_SIZE(regs));

    vm_pushl(regs[src]);
}

void
vm_pushm(unsigned src, unsigned n)
{
    obj_t *p;

    ASSERT((src + n) <= ARRAY_SIZE(regs));

    VM_STACK_CHK_DN(n);

    VM_STATS_UPDATE_PUSH(n);

    for (p = &regs[src]; n; --n, ++p)  *--sp = obj_retain(*p);
}

void
vm_pop(unsigned dst)
{
    ASSERT(dst < ARRAY_SIZE(regs));

    VM_STACK_CHK_UP(1);

    VM_STATS_UPDATE_POP(1);

    _obj_assign(&regs[dst], *sp++);
}

void
vm_popm(unsigned dst, unsigned n)
{
    obj_t *p;

    ASSERT((dst + n) <= ARRAY_SIZE(regs));

    VM_STACK_CHK_UP(n);

    VM_STATS_UPDATE_POP(n);

    for (p = &regs[dst + n - 1]; n; --n, --p)  _obj_assign(p, *sp++);
}

void
vm_drop(void)
{
    VM_STACK_CHK_UP(1);

    VM_STATS_UPDATE_POP(1);

    obj_release(*sp++);
}

void
vm_dropn(unsigned n)
{
    VM_STACK_CHK_UP(n);

    VM_STATS_UPDATE_POP(n);

    for (; n; --n)  obj_release(*sp++);
}

/***************************************************************************/

unsigned err_depth;

void
bt_print(obj_t outf)
{
  struct frame *p;
  FILE         *fp = _FILE(outf)->fp;
  obj_t        q;

  vm_push(0);

  fprintf(fp, "Backtrace:\n");
  for (p = frp; p; p = p->prev) {
    switch (p->type) {
    case FRAME_TYPE_INPUT:
      q = FRAME_INPUT(p)->file;
      vm_string_tocstr(_FILE(q)->filename);
      fprintf(fp, "From file %s, line %u\n", STRING(R0)->data, FRAME_INPUT(p)->line);
      break;
      
    case FRAME_TYPE_METHOD_CALL:
      fprintf(fp, "[");
      if (q = FRAME_METHOD_CALL(p)->cl) {
	vm_method_call_2(consts.str.printc, q, outf);
      } else {
	fprintf(fp, "<none>");
      }
      fprintf(fp, " ");
      vm_method_call_2(consts.str.printc, FRAME_METHOD_CALL(p)->sel, outf);
      fprintf(fp, "] ");
      vm_method_call_2(consts.str.printc, FRAME_METHOD_CALL(p)->args, outf);
      fprintf(fp, "\n");
      break;
      
    default:
      ;
    }
  }

  vm_drop(1);
}

void
error(enum errcode errcode, ...)
{
    obj_t   outf;
    FILE    *fp;
    va_list ap;
    obj_t   obj;

    if (err_depth > 0)  fatal(FATAL_ERR_DOUBLE_ERR);
    ++err_depth;

    vm_push(0);

    vm_method_call_1(consts.str._stderr, consts.cl.file);
    if (!is_kind_of(R0, consts.cl.file)) {
	fatal(FATAL_ERR_BAD_ERR_STREAM);
    }
    fp = _FILE(outf = R0)->fp;

    fprintf(fp, "\n");

    va_start(ap, errcode);
    
    switch (errcode) {
    case ERR_ASSERT:
	fprintf(fp, "Assertion failed");
	break;
    case ERR_SYM_NOT_BOUND:
	fprintf(fp, "Symbol not bound: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	break;
    case ERR_NO_METHOD:
	fprintf(fp, "No such method: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	break;
    case ERR_INVALID_METHOD:
	fprintf(fp, "Invalid method: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	break;
    case ERR_INVALID_ARG:
	fprintf(fp, "Invalid argument: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	break;
    case ERR_INVALID_VALUE_1:
	{
	    char *s;

	    s    = va_arg(ap, char *);
	    obj  = va_arg(ap, obj_t);
	    fprintf(fp, "Invalid value for %s: ", s);
	    vm_method_call_2(consts.str.printc, obj, outf);
	}
	break;
    case ERR_INVALID_VALUE_2:
      obj  = va_arg(ap, obj_t);
      fprintf(fp, "Invalid value for ");
      vm_method_call_2(consts.str.printc, obj, outf);
      obj = va_arg(ap, obj_t);
      fprintf(fp, ": ");
      vm_method_call_2(consts.str.printc, obj, outf);
      break;
    case ERR_NUM_ARGS:
	fprintf(fp, "Incorrect number of arguments");
	break;
    case ERR_IDX_RANGE:
	fprintf(fp, "Index out of range: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	break;
    case ERR_IDX_RANGE_2:
	fprintf(fp, "Indices out of range: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	fprintf(fp, ", ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
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
    case ERR_FILE_OPEN:
	{
	    int errnum;
	    
	    obj    = va_arg(ap, obj_t);
	    errnum = va_arg(ap, int);
	    fprintf(fp, "File open failed (%s): ", strerror(errnum));
	    vm_method_call_2(consts.str.printc, obj, outf);
	}
	
	break;
    case ERR_MODULE_LOAD:
	{
	    int errnum;
	    
	    obj    = va_arg(ap, obj_t);
	    errnum = va_arg(ap, int);
	    fprintf(fp, "Module load failed (%s): ", strerror(errnum));
	    vm_method_call_2(consts.str.printc, obj, outf);
	}
	
	break;
    case ERR_MODULE_MEMBER:
	fprintf(fp, "No module member: ");
	obj = va_arg(ap, obj_t);
	vm_method_call_2(consts.str.printc, obj, outf);
	break;
    case ERR_CONST:
	fprintf(fp, "Attempt to write constant");
	break;
    case ERR_OVF:
	fprintf(fp, "Arithmetic overflow");
	break;
    default:
	ASSERT(0);
    }

    fprintf(fp, "\n");
    bt_print(outf);

    va_end(ap);

    --err_depth;

    vm_drop(1);

    frame_goto(FRAME_TYPE_RESTART, 0);
}

/***************************************************************************/

void
m_inst_alloc(obj_t cl)
{
  vm_assign(0, obj_alloc(cl));
}

/***************************************************************************/

unsigned string_hash(obj_t s), string_equal(obj_t s1, obj_t s2);

void
method_run(obj_t cl, obj_t func, unsigned argc, obj_t args)
{
  vm_push(0);

  if (frp->type == FRAME_TYPE_METHOD_CALL && FRAME_METHOD_CALL(frp)->cl == NIL) {
    FRAME_METHOD_CALL(frp)->cl = cl;
  }

  if (is_kind_of(func, consts.cl.code_method)) {
    (*CODE_METHOD(func)->func)(argc, args);
    goto done;
  }
  
  if (is_kind_of(func, consts.cl.block)) {
    vm_method_call_2(consts.str.evalc, func, args);
    goto done;
  }
  
  error(ERR_INVALID_METHOD, func);

 done:
  vm_drop(1);
}

void
method_call(obj_t sel, unsigned argc, obj_t args)
{
  obj_t    recvr = CAR(args), cl, parent;
  unsigned sel_with_colon = 0;

  vm_push(0);
  vm_push(1);

  if (STRING(sel)->data[STRING(sel)->size - 1] == ':') {
    m_string_new(1, STRING(sel)->size - 1, STRING(sel)->data);
    vm_assign(1, R0);
    sel_with_colon = 1;
  } else {
    vm_assign(1, sel);
  }
  
  cl = inst_of(recvr);
  if (recvr == consts.cl.metaclass || cl == consts.cl.metaclass) {
    for (cl = recvr; cl; cl = CLASS(cl)->parent) {
      obj_t obj;
      
      if (obj = dict_at(CLASS(cl)->cl_methods, sel)) {
	method_run(cl, CDR(obj), argc - 1, CDR(args));
	goto done;
      }
      
      if (argc <= 1 && (obj = dict_at(CLASS(cl)->cl_vars, R1))) {
	if (sel_with_colon) {
	  if (STRING(R1)->data[0] == '#')  error(ERR_CONST);
	  
	  OBJ_ASSIGN(CDR(obj), CAR(CDR(args)));
	}
	vm_assign(0, CDR(obj));
	goto done;
      }
    }
  }
  
  for (cl = inst_of(recvr); cl; cl = parent) {
    obj_t obj;
    
    parent = CLASS(cl)->parent;
    
    if (obj = dict_at(CLASS(cl)->inst_methods, sel)) {
      method_run(cl, CDR(obj), argc, args);
      goto done;
    }
    
    if (parent && argc <= 1 && (obj = dict_at(CLASS(cl)->inst_vars, R1))) {
      obj_t *p = (obj_t *)((char *) recvr + (CLASS(parent)->inst_size + INTEGER(CDR(obj))->val));
      
      if (sel_with_colon) {
	if (STRING(R1)->data[0] == '#')  error(ERR_CONST);
	
	obj_assign(p, CAR(CDR(args)));
      }
      vm_assign(0, *p);
      goto done;
    }
  }
  
  error(ERR_NO_METHOD, sel);
  
 done:
  vm_pop(1);
  vm_drop();
}

void
m_method_call_1(obj_t sel, obj_t recvr)
{
  vm_push(0);

  vm_pushl(sel);
  m_cons(consts.cl.list, recvr, NIL);
  vm_push(0);
  
  method_call(sel, 1, R0);
  
  vm_dropn(3);
}

void
m_method_call_2(obj_t sel, obj_t recvr, obj_t arg)
{
  vm_push(0);
  
  vm_pushl(sel);
  m_cons(consts.cl.list, arg, NIL);
  m_cons(consts.cl.list, recvr, R0);
  vm_push(0);
  
  method_call(sel, 2, R0);
  
  vm_dropn(3);
}

void
m_method_call_3(obj_t sel, obj_t recvr, obj_t arg1, obj_t arg2)
{
  vm_push(0);
  
  vm_pushl(sel);
  m_cons(consts.cl.list, arg2, NIL);
  m_cons(consts.cl.list, arg1, R0);
  m_cons(consts.cl.list, recvr, R0);
  vm_push(0);
  
  method_call(sel, 3, R0);
  
  vm_dropn(3);
}

/***************************************************************************/

#define CRC32_INIT(crc)  ((crc) = 0xffffffff)

void
crc32(unsigned *pcrc, unsigned char *p, unsigned n)
{
#define CRC_POLY 0xEDB88320

    unsigned crc, k;

    for (crc = *pcrc; n; --n, ++p) {
	crc ^= *p;
	
	for (k = 8; k; --k) {
	    if (crc & 1) {
		crc = (crc >> 1) ^ CRC_POLY;
	    } else {
		crc >>= 1;
	    }
	}
    }

    *pcrc = crc;
}

#define CRC32(r, p, n)  (crc32(&(r), (unsigned char *)(p), (n)))

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

void _inst_walk_metaclass(obj_t inst, void (*func)(obj_t));

/* Used when walking an object whose inst_of is NIL;
   see cl_inst_walk()
*/
void
meta_metaclass_walk(obj_t inst, void (*func)(obj_t))
{
    (*func)(inst_of(inst));

    _inst_walk_metaclass(inst, func);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_name(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);

  vm_assign(0, CLASS(consts.cl.metaclass)->name);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_tostring(unsigned argc, obj_t args)
{
  cm_meta_metaclass_name(argc, args);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_parent(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);
  
  vm_assign(0, CLASS(consts.cl.metaclass)->parent);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_cl_methods(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);

  vm_assign(0, CLASS(consts.cl.metaclass)->cl_methods);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_cl_vars(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);
  
  vm_assign(0, CLASS(consts.cl.metaclass)->cl_vars);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_inst_methods(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);
  
  vm_assign(0, NIL);
}

/* Installed as a class method of Metaclass */
void
cm_meta_metaclass_inst_vars(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);

  /* Must be hard-coded, because
     inst_vars(#Metaclass) only has mutable ones
  */
  
  m_cons(consts.cl.list, consts.str.instance_variables, NIL);
  m_cons(consts.cl.list, consts.str.instance_methods, R0);
  m_cons(consts.cl.list, consts.str.class_variables, R0);
  m_cons(consts.cl.list, consts.str.class_methods, R0);
  m_cons(consts.cl.list, consts.str.parent, R0);
  m_cons(consts.cl.list, consts.str.name, R0);
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
cm_object_new(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                                error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.metaclass))  error(ERR_INVALID_ARG, recvr);
  
  m_inst_alloc(recvr);
}

void
cm_object_quote(unsigned argc, obj_t args)
{
    if (argc != 1)  error(ERR_NUM_ARGS);

    vm_assign(0, CAR(args));
}

void
cm_object_pquote(unsigned argc, obj_t args)
{
  cm_object_quote(argc, args);
}

void
cm_object_eval(unsigned argc, obj_t args)
{
  cm_object_quote(argc, args);
}

void
cm_object_instof(unsigned argc, obj_t args)
{
    if (argc != 1)  error(ERR_NUM_ARGS);

    vm_assign(0, inst_of(CAR(args)));
}

void
cm_object_eq(unsigned argc, obj_t args)
{
    if (argc != 2)  error(ERR_NUM_ARGS);

    vm_assign(0, CAR(args) == CAR(CDR(args) ? consts.bool._true : consts.bool._false);
}

void m_fqclname(obj_t cl);

void
cm_object_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;
  char  buf[64];
  
  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (recvr == NIL) {
    vm_assign(0, consts.str.nil);
    return;
  }
  
  m_fqclname(inst_of(recvr));
  m_string_new(3, snprintf(buf, sizeof(buf), "<inst @ %p, of class ", recvr), buf,
	          STRING(R0)->size, STRING(R0)->data,
	          1, ">"
	       );
}

void
cm_object_print(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);

  m_method_call_1(consts.str.tostring, recvr);
  m_method_call_1(consts.str.print, R0);
  
  vm_assign(0, recvr);
}

void
cm_object_printc(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  
  m_method_call_1(consts.str.tostring, recvr);
  m_method_call_2(consts.str.printc, R0, CAR(CDR(args)));

  vm_assign(0, recvr);
}

void
cm_object_append(unsigned argc, obj_t args)
{
  obj_t recvr, arg;
  
  if (argc != 2)     error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (recvr != NIL)  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!(arg == NIL || is_kind_of(arg, consts.cl.list)))  error(ERR_INVALID_ARG, arg);
  
  vm_assign(0, arg);
}


void
cm_object_while(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

    if (argc != 2)  error(ERR_NUM_ARGS);
    recvr = CAR(args);
    arg   = CAR(CDR(args));

    FRAME_WHILE_BEGIN {

      switch (while_arg) {
      case WHILE_ARG_CONT:
      case 0:
	for (;;) {
	  m_method_call_1(consts.str.eval, recvr);
	  if (!is_kind_of(R0, consts.cl.boolean))  error(ERR_INVALID_VALUE_2, recvr, R0);
	  if (!BOOLEAN(R0)->val)  break;
	  m_method_call_1(consts.str.eval, arg);
	}
	
      case WHILE_ARG_BREAK:
	break;

      default:
	HARD_ASSERT(0);
      }

    } FRAME_WHILE_END;
}

void
cm_object_break(unsigned argc, obj_t args)
{
    if (argc != 1)  error(ERR_NUM_ARGS);

    vm_assign(0, CAR(args));

    frame_goto(FRAME_TYPE_WHILE, WHILE_ARG_BREAK);

    error(ERR_BREAK);
}

void
cm_object_cont(unsigned argc, obj_t args)
{
    if (argc != 1)  error(ERR_NUM_ARGS);

    frame_goto(FRAME_TYPE_WHILE, WHILE_ARG_CONT);

    error(ERR_CONT);
}

void
cm_object_return(unsigned argc, obj_t args)
{
    if (argc != 1)  error(ERR_NUM_ARGS);

    vm_assign(0, CAR(args));

    frame_goto(FRAME_TYPE_BLOCK, 1);

    error(ERR_RETURN);
}

/***************************************************************************/

/* Class: Metaclass */

void
_inst_walk_metaclass(obj_t inst, void (*func)(obj_t))
{
    (*func)(CLASS(inst)->name);
    (*func)(CLASS(inst)->parent);
    (*func)(CLASS(inst)->module);
    (*func)(CLASS(inst)->cl_methods);
    (*func)(CLASS(inst)->cl_vars);
    (*func)(CLASS(inst)->inst_methods);
    (*func)(CLASS(inst)->inst_vars);
}

void inst_walk_user(obj_t cl, obj_t inst, void (*func)(obj_t));

void
inst_init_metaclass(obj_t cl, obj_t inst, va_list ap)
{
    obj_t       name      = va_arg(ap, obj_t);
    obj_t       parent    = va_arg(ap, obj_t);
    obj_t       module    = va_arg(ap, obj_t);
    unsigned    inst_size = va_arg(ap, unsigned);
    inst_init_t inst_init = va_arg(ap, inst_init_t);
    inst_walk_t inst_walk = va_arg(ap, inst_walk_t);
    inst_free_t inst_free = va_arg(ap, inst_free_t);

    vm_push(0);

    OBJ_ASSIGN(CLASS(inst)->name,   name);
    OBJ_ASSIGN(CLASS(inst)->parent, parent);
    OBJ_ASSIGN(CLASS(inst)->module, module);
    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(inst)->cl_methods, R0);
    m_string_dict_new(116);
    OBJ_ASSIGN(CLASS(inst)->cl_vars, R0);
    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(inst)->inst_methods, R0);
    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(inst)->inst_vars, R0);
    CLASS(inst)->inst_size = inst_size;
    CLASS(inst)->inst_init = inst_init;
    CLASS(inst)->inst_walk = inst_walk;
    CLASS(inst)->inst_free = inst_free;

    vm_pop(0);

    inst_init_parent(cl, inst, ap);
}

void
m_class_new(obj_t name, obj_t parent, unsigned inst_size,
	    inst_init_t _inst_init, inst_walk_t _inst_walk, inst_free_t _inst_free
	     )
{
    vm_push(0);

    m_inst_alloc(consts.cl.metaclass);
    inst_init(R0, name, parent, module_cur, inst_size,
	      _inst_init, _inst_walk, _inst_free
	      );
    
    /* Add class to environment */
    env_new_put(name, R0);

    vm_drop();
}

void
inst_walk_metaclass(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    _inst_walk_metaclass(inst, func);

    inst_walk_parent(cl, inst, func);
}

void m_fqmodname(obj_t mod);

void
m_fqclname(obj_t cl)
{
    obj_t s;

    vm_push(0);

    s = CLASS(cl)->name;
    m_fqmodname(CLASS(cl)->module);
    if (STRING(R0)->size == 0) {
      vm_assign(0, s);
    } else {
      m_string_new(3, STRING(R0)->size, STRING(R0)->data,
		      1, ".",
		      STRING(s)->size, STRING(s)->data
		   );
    }

    vm_drop();
}

void
cm_metaclass_name(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                                error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.metaclass))  error(ERR_INVALID_ARG, recvr);

  m_fqclname(recvr);
}

void
cm_metaclass_tostring(unsigned argc, obj_t args)
{
  cm_metaclass_name(argc, args);
}

void
cm_metaclass_parent(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                                error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.metaclass))  error(ERR_INVALID_ARG, recvr);

  vm_assign(0, CLASS(recvr)->parent);
}

void m_dict_keys(obj_t dict);

void
cm_metaclass_inst_vars(unsigned argc, obj_t args)
{
  obj_t recvr;
  
  if (argc != 1)                                error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.metaclass))  error(ERR_INVALID_ARG, recvr);
  
  m_dict_keys(CLASS(recvr)->inst_vars);
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

unsigned list_len(obj_t);

void
cm_metaclass_new(unsigned argc, obj_t args)
{
  obj_t    name, parent, inst_vars;
  unsigned i;
  
  if (argc != 3)  error(ERR_NUM_ARGS);
  name      = CAR(args);  args = CDR(args);
  parent    = CAR(args);  args = CDR(args);
  inst_vars = CAR(args);
  if (!is_kind_of(name, consts.cl.string))       error(ERR_INVALID_ARG, name);
  if (!is_kind_of(parent, consts.cl.metaclass))  error(ERR_INVALID_ARG, parent);
  if (!(inst_vars == NIL || is_kind_of(inst_vars, consts.cl.list)))  error(ERR_INVALID_ARG, inst_vars);
  
  vm_push(1);
  
  m_class_new(name, parent,
	      CLASS(parent)->inst_size + list_len(inst_vars) * sizeof(obj_t),
	      inst_init_parent, inst_walk_user, inst_free_parent
	      );
  
  vm_assign(1, R0);
  for (i = 0; inst_vars; inst_vars = CDR(inst_vars), i += sizeof(obj_t)){
    integer_new(i);
    dict_at_put(CLASS(R1)->inst_vars, CAR(inst_vars), R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
}

/***************************************************************************/

/* Class: Code_Method */

void
inst_init_code_method(obj_t cl, obj_t inst, va_list ap)
{
  CODE_METHOD(inst)->func = va_arg(ap, void (*)(unsigned, obj_t));
  
  inst_init_parent(cl, inst, ap);
}

void
m_code_method_new(void (*func)(unsigned, obj_t))
{
    m_inst_alloc(consts.cl.code_method);
    inst_init(R0, func);
}

void
cm_code_method_eval(unsigned argc, obj_t args)
{
  obj_t    recvr, nargs;
  
  if (argc != 2)                                  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.code_method))  error(ERR_INVALID_ARG, recvr);
  nargs = CAR(CDR(args));
  if (!(nargs == NIL || is_kind_of(nargs, consts.cl.list)))  error(ERR_INVALID_ARG, nargs);

  (*CODE_METHOD(recvr)->func)(list_len(nargs), nargs);
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
m_boolean_new(unsigned val)
{
  m_inst_alloc(consts.cl.boolean);
  inst_init(R0, val != 0);
}

void
cm_boolean_new(unsigned argc, obj_t args)
{
  obj_t    arg;
  unsigned bval;
  
  if (argc < 1) {
    bval = 0;
  } else if (argc > 1) {
    error(ERR_NUM_ARGS);
  } else {
    arg = CAR(args);

    if (is_kind_of(arg, consts.cl.boolean)) {
      vm_assign(0, arg);
      return;
    } else if (is_kind_of(arg, consts.cl.integer)) {
      bval = INTEGER(arg)->val != 0;
    } if (is_kind_of(arg, consts.cl._float)) {
      bval = FLOAT(arg)->val != 0.0;
    } else if (is_kind_of(arg, consts.cl.string)) {
      bval = STRING(arg)->size != 0;
    } else {
      error(ERR_INVALID_ARG, arg);
    }
  }

  vm_assign(0, bval ? consts.bool._true : consts.bool._false);
}

void
cm_boolean_and(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.boolean))    error(ERR_INVALID_ARG, arg);
  
  vm_assign(0, BOOLEAN(recvr)->val && BOOLEAN(arg)->val ? consts.bool._true : consts.bool_false);
}

void
cm_boolean_or(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.boolean))    error(ERR_INVALID_ARG, arg);
  
  vm_assign(0, BOOLEAN(recvr)->val || BOOLEAN(arg)->val ? consts.bool._true : consts.bool._false);
}

void
cm_boolean_xor(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.boolean))    error(ERR_INVALID_ARG, arg);
  
  vm_assign(0, (BOOLEAN(recvr)->val != 0) ^ (BOOLEAN(arg)->val != 0) ? consts.bool._true : consts.bool._false);
}

void
cm_boolean_not(unsigned argc, obj_t args)
{
  obj_t recvr;
  
  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  
  vm_assign(0, BOOLEAN(recvr)->val ? consts.bool._false : consts.bool._true);
}

void
cm_boolean_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  
  vm_assign(0, BOOLEAN(recvr)->val ? consts.str._true : consts.str._false);
}

void
cm_boolean_equals(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  
  vm_assign(0, inst_of(arg) == inst_of(recvr)
	       && BOOLEAN(arg)->val == BOOLEAN(recvr)->val
	       ? consts.bool._true : consts.bool._false
	       );
}

void
cm_boolean_if(unsigned argc, obj_t args)
{
  obj_t recvr;
  
  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  
  if (BOOLEAN(recvr)->val) {
    m_method_call_1(consts.str.eval, CAR(CDR(args)));
  } else {
    vm_assign(0, recvr);
  }
}

void
cm_boolean_if_else(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 3)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  args = CDR(args);
  
  m_method_call_1(consts.str.eval,
		  BOOLEAN(recvr)->val ? CAR(args) : CAR(CDR(args))
		  );
}

void
cm_boolean_assert(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.boolean))  error(ERR_INVALID_ARG, recvr);
  
  if (BOOLEAN(recvr)->val == 0)  error(ERR_ASSERT);
  
  vm_assign(0, recvr);
}

/***************************************************************************/

/* Class: Integer */

void
inst_init_integer(obj_t cl, obj_t inst, va_list ap)
{
    INTEGER(inst)->val = va_arg(ap, integer_val_t);

    inst_init_parent(cl, inst, ap);
}

void
m_integer_new(integer_val_t val)
{
  vm_push(0);

  m_inst_alloc(consts.cl.integer);
  inst_init(R0, val);

  vm_drop();
}

void
cm_integer_new(unsigned argc, obj_t args)
{
  obj_t         arg;
  integer_val_t ival;

  if (argc < 1) {
    ival = 0;
  } else if (argc > 1) {
    error(ERR_NUM_ARGS);
  } else {
    arg = CAR(args);

    if (is_kind_of(arg, consts.cl.boolean)) {
      ival = BOOLEAN(arg)->val != 0;
    } else if (is_kind_of(arg, consts.cl.integer)) {
      vm_assign(0, arg);
      return;
    } else if (is_kind_of(arg, consts.cl._float)) {
      ival = (integer_val_t) FLOAT(arg)->val;
    } else if (is_kind_of(arg, consts.cl.string)) {
      char *fmt;
      
      if (STRING(arg)->size >= 3
	  && STRING(arg)->data[0] == '0'
	  && (STRING(arg)->data[1] | 0x20) == 'x'
	  ) {
	fmt = INTEGER_FMT_HEX;
      } else if (STRING(arg)->size >= 2
		 && STRING(arg)->data[0] == '0'
		 ) {
	fmt = INTEGER_FMT_OCT;
      } else {
	fmt = INTEGER_FMT_DEC;
      }
      
      m_string_tocstr(arg);
      if (sscanf(STRING(R0)->data, fmt, &ival) != 1) {
	error(ERR_INVALID_ARG, arg);
      }
    } else {
      error(ERR_INVALID_ARG, arg);
    }
  }

  m_integer_new(ival);
}

void
cm_integer_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;
  char  buf[32];
  
  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  
  m_string_new(1, snprintf(buf, sizeof(buf), "%lld", INTEGER(recvr)->val), buf);
}

void
cm_integer_tostring_base(unsigned argc, obj_t args)
{
  obj_t          recvr, arg;
  integer_val_t  val, base;
  uinteger_val_t uval, ubase;
  char           buf[32], *p;
  unsigned char  negf;
  unsigned       n;
  
  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);
  base = INTEGER(arg)->val;
  if (base <= 0 || base > 36)                 error(ERR_INVALID_ARG, arg);
  ubase = (uinteger_val_t) base;

  p = &buf[ARRAY_SIZE(buf)];
  n = 0;

  val = INTEGER(recvr)->val;
  negf = 0;
  if (base == 10 && val < 0) {
    negf = 1;
    val = -val;
  }
  uval = (uinteger_val_t) val;

  for ( ; n == 0 || uval != 0; uval /= ubase) {
    uinteger_val_t d = uval % ubase;
    char           c = d + (d <= 9 ? '0' : 'A' - 10);
    
    ASSERT(n < sizeof(buf));
    
    *--p = c;
    ++n;
    
    if (uval == 0)  break;
  }
  if (negf) {
    ASSERT(n < sizeof(buf));

    *--p = '-';
    ++n;
  }

  m_string_new(1, n, p);
}

void
cm_integer_hash(unsigned argc, obj_t args)
{
  obj_t    recvr;
  unsigned r;
  
  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  
  CRC32_INIT(r);
  CRC32(r, &INTEGER(recvr)->val, sizeof(INTEGER(recvr)->val));
  
  m_integer_new(r);
}

void
cm_integer_equals(unsigned argc, obj_t args)
{
  obj_t    recvr, arg;
  unsigned bval = 0;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  
  vm_assign(0, is_kind_of(arg, consts.cl_integer)
	       && INTEGER(arg)->val == INTEGER(recvr)->val
	       ? consts.bool._true : consts.bool._false
	    );
}

void
cm_integer_minus(unsigned argc, obj_t args)
{
  obj_t recvr;
  
  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  
  m_integer_new(-INTEGER(recvr)->val);
}

int
integer_sgn(integer_val_t ival)
{
  if (ival < 0)  return (-1);
  if (ival > 0)  return (1);
  return (0);
}

integer_val_t
integer_abs(integer_val_t ival)
{
  return (ival < 0 ? -ival : ival);
}

void
cm_integer_add(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  integer_val_t ival1, ival2, iresult;
  int           s1, s2;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  ival1 = INTEGER(recvr)->val;
  ival2 = INTEGER(arg)->val;
  iresult = ival1 + ival2;
  s1 = integer_sgn(ival1);
  s2 = integer_sgn(ival2);

  if (s1 > 0 && s2 > 0) {
    if (!(iresult > ival1 && iresult > ival2))  error(ERR_OVF);
  } else if (s1 < 0 && s2 < 0) {
    if (!(iresult < ival1 && iresult < ival2))  error(ERR_OVF);
  }
  
  m_integer_new(iresult);
}

void
cm_integer_sub(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  integer_val_t ival1, ival2, iresult;
  int           s1, s2;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);
  
  ival1 = INTEGER(recvr)->val;
  ival2 = INTEGER(arg)->val;
  iresult = ival1 - ival2;
  s1 = integer_sgn(ival1);
  s2 = integer_sgn(ival2);

  if (s1 > 0 && s2 < 0) {
    if (!(iresult > ival1 && iresult > ival2))  error(ERR_OVF);
  } else if (s1 < 0 && s2 > 0) {
    if (!(iresult < ival1 && iresult < ival2))  error(ERR_OVF);
  }
  
  m_integer_new(iresult);
}

void
cm_integer_mult(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  integer_val_t ival1, ival2, iresult, uval1, uval2, uresult;
  int           s1, s2, sresult;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);
  
  ival1 = INTEGER(recvr)->val;
  ival2 = INTEGER(arg)->val;
  iresult = ival1 * ival2;
  uval1 = integer_abs(ival1);
  uval2 = integer_abs(ival2);
  uresult = integer_abs(ireseult);
  s1 = integer_sgn(ival1);
  s2 = integer_sgn(ival2);
  sresult = integer_sgn(iresult);

  if (ival1 != 0 && ival2 != 0) {
    if (!(uresult > uval1 && uresult > uval2)
	|| (s1 == s2 ? sresult < 0 : sresult > 0)
	)  error(ERR_OVF):
  }
    
  m_integer_new(iresult);
}

void
cm_integer_div(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  integer_val_t ival1, ival2;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  ival1 = INTEGER(recvr)->val;
  ival2 = INTEGER(arg)->val;
  
  if (ival2 == 0)  error(ERR_OVF);

  m_integer_new(ival1 / ival2);
}

void
cm_integer_mod(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  integer_val_t ival1, ival2;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  ival1 = INTEGER(recvr)->val;
  ival2 = INTEGER(arg)->val;
  
  if (ival2 == 0)  error(ERR_OVF);

  m_integer_new(ival1 % ival2);
}

void
m_integer_range(integer_val_t init, integer_val_t lim, integer_val_t step)
{
    integer_val_t val;
    obj_t         *p;

    vm_push(0);
    vm_push(1);

    vm_assign(1, NIL);
    for (p = &R1, val = init; val < lim; val += step) {
      m_integer_new(val);
      m_cons(consts.cl.list, R0, NIL);
      obj_assign(p, R0);
      p = &CDR(R0);
    }
    vm_assign(0, R1);

    vm_pop(1);
    vm_drop();
}

void
cm_integer_range(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  
  m_integer_range(0, INTEGER(recvr)->val, 1);
}

void
cm_integer_range_init(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);
  
  m_integer_range(INTEGER(arg)->val, INTEGER(recvr)->val, 1);
}

void
cm_integer_range_init_step(unsigned argc, obj_t args)
{
  obj_t recvr, arg0, arg1;
  
  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);  args = CDR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg0 = CAR(args);  args = CDR(args);
  if (!is_kind_of(arg0, consts.cl.integer))   error(ERR_INVALID_ARG, arg0);
  arg1 = CAR(args);
  if (!is_kind_of(arg1, consts.cl.integer))   error(ERR_INVALID_ARG, arg1);
  
  m_integer_range(INTEGER(arg0)->val, INTEGER(recvr)->val, INTEGER(arg1)->val);
}

void
cm_integer_chr(unsigned argc, obj_t args)
{
  obj_t         recvr;
  integer_val_t ival;
  char          c;
  
  if (argc != 1)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  ival = INTEGER(recvr)->val;
  if (ival < 0 || ival > 255)                 error(ERR_INVALID_ARG, recvr);
  
  c = ival;
  m_string_new(1, 1, &c);
}

void
cm_integer_lt(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  vm_assign(0, INTEGER(recvr)->val < INTEGER(arg)->val ? consts.bool._true : consts.bool._false);
}

void
cm_integer_gt(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  vm_assign(0, INTEGER(recvr)->val > INTEGER(arg)->val ? consts.bool._true : consts.bool._false);
}

void
cm_integer_le(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  vm_assign(0, INTEGER(recvr)->val <= INTEGER(arg)->val ? consts.bool._true : consts.bool._false);
}

void
cm_integer_ge(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.integer))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))    error(ERR_INVALID_ARG, arg);

  vm_assign(0, INTEGER(recvr)->val >= INTEGER(arg)->val ? consts.bool._true : consts.bool._false);
}

/***************************************************************************/

/* Class: Float */

void
inst_init_float(obj_t cl, obj_t inst, va_list ap)
{
    FLOAT(inst)->val = va_arg(ap, float_val_t);

    inst_init_parent(cl, inst, ap);
}

void
m_float_new(float_val_t val)
{
  m_inst_alloc(consts.cl._float);
  inst_init(R0, val);
}

void
cm_float_new(unsigned argc, obj_t args)
{
  obj_t       arg;
  float_val_t fval;

  if (argc < 1) {
    fval = 0.0;
  } else if (argc > 1) {
    error(ERR_NUM_ARGS);
  } else {
    arg = CAR(args);
  
    if (is_kind_of(arg, consts.cl.boolean)) {
      fval = BOOLEAN(arg)->val ? 1.0 : 0.0;
    } else if (is_kind_of(arg, consts.cl.integer)) {
      fval = (float_val_t) INTEGER(arg)->val;
    } else if (is_kind_of(arg, consts.cl._float)) {
      vm_assign(0, arg);
      return;
    } else if (is_kind_of(arg, consts.cl.string)) {
      m_string_tocstr(arg);
      if (sscanf(STRING(R0)->data, FLOAT_FMT_SCAN, &fval) != 1) {
	error(ERR_INVALID_ARG, arg);
      }
    } else {
      error(ERR_INVALID_ARG, arg);
    }
  }

  m_float_new(fval);
}

int
float_sgn(float_val_t fval)
{
  if (fval < 0.0)  return (-1);
  if (fval > 0.0)  return (1);
  return (0);
}

float_val_t
float_abs(float_val_t fval)
{
  return (fval < 0.0 ? -fval : fval);
}


void
cm_float_add(unsigned argc, obj_t args)
{
  obj_t       recvr, arg;
  float_val_t fval1, fval2, fresult;
  int         s1, s2;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl._float))    error(ERR_INVALID_ARG, arg);

  m_float_new(FLOAT(recvr)->val + FLOAT(arg)->val);
}

void
cm_float_sub(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl._float))    error(ERR_INVALID_ARG, arg);

  m_float_new(FLOAT(recvr)->val - FLOAT(arg)->val);
}

void
cm_float_mult(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl._float))    error(ERR_INVALID_ARG, arg);

  m_float_new(FLOAT(recvr)->val * FLOAT(arg)->val);
}

void
cm_float_div(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl._float))    error(ERR_INVALID_ARG, arg);

  m_float_new(FLOAT(recvr)->val / FLOAT(arg)->val);
}

void
cm_float_minus(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);

  m_float_new(-FLOAT(recvr)->val);
}

void
cm_float_hash(unsigned argc, obj_t args)
{
  obj_t    recvr;
  unsigned r;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);

  CRC32_INIT(r);
  CRC32(r, &FLOAT(recvr)->val, sizeof(FLOAT(recvr)->val));
  
  m_integer_new(r);
}

void
cm_float_equals(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));

  vm_assign(0, inst_of(arg) == inst_of(recvr)
	       && FLOAT(arg)->val == FLOAT(recvr)->val
	       ? consts.bool._true : consts.bool._false
	       );
}

void
cm_float_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;
  char  buf[64];

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl._float))  error(ERR_INVALID_ARG, recvr);

  m_string_new(1, snprintf(buf, sizeof(buf), FLOAT_FMT_PRINT, FLOAT(recvr)->val), buf);
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
m_string_new(unsigned n, ...)
{
    va_list  ap;
    unsigned nn, size;

    vm_push(0);

    va_start(ap, n);
    for (size = 0, nn = n; nn; --nn) {
        unsigned s  = va_arg(ap, unsigned);
        char     *d = va_arg(ap, char *);

        size += s;
	d = d;			/* Suppress warning about unused var */
    }
    va_end(ap);

    m_inst_alloc(consts.cl.string);
    inst_init(R0, size);

    va_start(ap, n);
    for (size = 0, nn = n; nn; --nn) {
        unsigned s  = va_arg(ap, unsigned);
        char     *d = va_arg(ap, char *);

        memcpy(STRING(R0)->data + size, d, s);
        size += s;
    }
    va_end(ap);

    vm_drop();
}

void
m_string_tocstr(obj_t s)
{
    char c = 0;

    vm_push(0);

    m_string_new(2, STRING(s)->size, STRING(s)->data,
		    1,               &c
		 );

    vm_drop();
}

unsigned
string_hash(obj_t s)
{
    unsigned r;

    ASSERT(inst_of(s) == consts.cl.string);

    CRC32_INIT(r);
    CRC32(r, STRING(s)->data, STRING(s)->size);

    return (r);
}

void
cm_string_hash(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  
  m_integer_new(string_hash(recvr));
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
cm_string_equal(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  
  vm_assign(0, inst_of(arg) == inst_of(recvr)
	       && string_equal(arg, recvr)
	       ? consts.bool._true : consts.bool._false
	    );
}

void
cm_string_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);

  vm_assign(0, recvr);
}

void
cm_string_pquote(unsigned argc, obj_t args)
{
  obj_t    recvr;
  char     *p;
  unsigned n;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);

  for (p = STRING(recvr)->data, n = STRING(recvr)->size; n; --n, ++p) {
    if (isspace(*p)) {
      m_string_new(3, 1, "\"",
		      STRING(recvr)->size, STRING(recvr)->data, 
		      1, "\""
		 );
      return;
    }
  }

  vm_assign(0, recvr);
}

void
cm_string_append(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.string))    error(ERR_INVALID_ARG, arg);

  m_string_new(2, STRING(recvr)->size, STRING(recvr)->data,
	          STRING(arg)->size, STRING(arg)->data
	       );
}

void
cm_string_eval(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);

  vm_assign(0, env_at(recvr));
}

FILE *
m_file_stdout(void)
{
  FILE *result;

  vm_push(0);

  m_method_call_1(consts.str._stdout, consts.cl.file);
  if (!is_kindof(R0, consts.cl.file))  error(ERR_INVALID_VALUE_2, "stdout", R0);
  result = _FILE(R0)->fp;

  vm_pop(0);

  return (result);
} 
 
FILE *
m_file_stderr(void)
{
  FILE *result;

  vm_push(0);

  m_method_call_1(consts.str._stderr, consts.cl.file);
  if (!is_kindof(R0, consts.cl.file))  error(ERR_INVALID_VALUE_2, "stderr", R0);
  result = _FILE(R0)->fp;

  vm_pop(0);

  return (result);
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
            fprintf(fp, "\\x%02x", * (unsigned char *) p);
        }
    }
}

void
cm_string_print(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  
  string_print(recvr, m_file_stdout());
  
  vm_assign(0, recvr);
}

void
cm_string_printc(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.file))      error(ERR_INVALID_ARG, arg);
  
  string_print(recvr, _FILE(arg)->fp);
  
  vm_assign(0, recvr);
}

void
cm_string_len(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  
  m_integer_new(STRING(recvr)->size);
}

int
m_string_substr(obj_t s, int ofs, int len)
{
  int result = 0;

  vm_push(0);

  if (ofs < 0)  ofs = (int) STRING(s)->size + ofs;
  
  if (ofs >= 0 && (ofs + len) <= (int) STRING(s)->size) {
    m_string_new(1, len, STRING(s)->data + ofs);
  } else {
    result = -1;
  }

  vm_drop();
  
  return (result);
}

void
cm_string_at(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))   error(ERR_INVALID_ARG, arg);

  if (m_string_substr(recvr, INTEGER(arg)->val, 1) < 0)  error(ERR_IDX_RANGE, arg);
}

void
cm_string_at_len(unsigned argc, obj_t args)
{
  obj_t         recvr, arg1, arg2;
  integer_val_t len;

  if (argc != 3)                              error(ERR_NUM_ARGS);
  recvr = CAR(args);  args = CDR(args);
  if (!is_kind_of(recvr, consts.cl.string))   error(ERR_INVALID_ARG, recvr);
  arg1 = CAR(args);  args = CDR(args);
  if (!is_kind_of(arg1, consts.cl.integer))   error(ERR_INVALID_ARG, arg1);
  arg2 = CAR(args);
  if (!is_kind_of(arg2, consts.cl.integer))   error(ERR_INVALID_ARG, arg2);
  len = INTEGER(arg2)->val;
  if (len < 0)                                error(ERR_INVALID_ARG, arg2);

  if (m_string_substr(recvr, INTEGER(arg1)->val, len) < 0)  error(ERR_IDX_RANGE_2, arg1, arg2);
}

void
cm_string_asc(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(is_kind_of(recvr, consts.cl.string) && STRING(recvr)->size > 0))  error(ERR_INVALID_ARG, recvr);

  m_integer_new(STRING(recvr)->data[0]);
}

void
cm_string_foreach(unsigned argc, obj_t args)
{
  obj_t    recvr, arg, *p;
  char     *s;
  unsigned n;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));

  vm_push(1);
  
  vm_assign(1, NIL);
  for (p = &R1, s = STRING(recvr)->data, n = STRING(recvr)->size; n; --n, ++s) {
    m_string_new(1, 1, s);
    m_cons(consts.cl.list, R0, NIL);
    m_method_call_2(consts.str.evalc, arg, R0);
    m_cons(consts.cl.list, R0, NIL);
    obj_assign(p, R0);
    p = &CDR(R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
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
cm_string_index(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.string))    error(ERR_INVALID_ARG, arg);

  m_integer_new(string_index(recvr, arg, 0, 1));
}

void
cm_string_rindex(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.string))    error(ERR_INVALID_ARG, arg);

  m_integer_new(string_index(recvr, arg, 0, -1));
}

void
cm_string_split(unsigned argc, obj_t args)
{
  obj_t    recvr, arg, *p;
  unsigned ofs;
    
  if (argc != 2)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.string))    error(ERR_INVALID_ARG, arg);

  vm_push(1);
  
  vm_assign(1, NIL);
  for (p = &R1, ofs = 0; ofs < STRING(recvr)->size; ) {
    int      i = string_index(recvr, arg, ofs, 1);
    unsigned n = (i < 0) ? STRING(recvr)->size - ofs : (unsigned) i - ofs;
    
    m_string_new(1, n, STRING(recvr)->data + ofs);
    m_cons(consts.cl.list, R0, NIL);
    obj_assign(p, R0);
    p = &CDR(R0);
    ofs += n + 1;
  }
  vm_assign(0, R1);
  
  vm_pop(1);
}

void
read_eval(void)
{
    obj_t *sp_save;
    
    for(sp_save = sp;;) {
        int rc = yyparse();

        while (sp < sp_save)  vm_drop(); /* Discard all objs created during parsing */

        if (rc != 0) break;

        vm_method_call_1(consts.str.eval, R0);
    }
}

void
cm_string_load(unsigned argc, obj_t args)
{
#if 0

  obj_t recvr;

  if (argc != 1)                             error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, recvr);

  yy_push_str(STRING(recvr)->data, STRING(recvr)->size);
  
  read_eval();
  
  yy_pop();

#else

  vm_assign(0, NIL);

#endif
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
m_cons(obj_t cl, obj_t car, obj_t cdr)
{
    vm_push(0);

    m_inst_alloc(cl);
    inst_init(R0, car, cdr);

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
cm_dptr_car(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dptr))  error(ERR_INVALID_ARG, recvr);

  vm_assign(0, CAR(recvr));
}

void
cm_dptr_cdr(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dptr))  error(ERR_INVALID_ARG, recvr);
  
  vm_assign(0, CDR(recvr));
}

void
cm_dptr_hash(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dptr))  error(ERR_INVALID_ARG, recvr);
  
  vm_pushm(1, 2);
  
  m_method_call_1(consts.str.hash, CAR(recvr));
  vm_assign(1, R0);
  m_method_call_1(consts.str.hash, CDR(recvr));
  vm_assign(2, R0);
  m_method_call_2(consts.str.addc, R1, R2); /* TBD: Or call directly? */
  
  vm_popm(1, 2);
}

void
cm_dptr_equals(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dptr))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.dptr)) {
    vm_assign(R0, consts.bool._false);
    return;
  }

  vm_pushm(1, 2);
  
  m_method_call_2(consts.str.equalsc, CAR(recvr), CAR(arg));
  vm_assign(1, R0);
  m_method_call_2(consts.str.equalsc, CDR(recvr), CDR(arg));
  vm_assign(2, R0);
  m_method_call_2(consts.str.andc, R1, R2); /* TBD: Or call directly? */
  
  vm_popm(1, 2);
}

/***************************************************************************/

/* Class: Pair */

void
cm_pair_new(unsigned argc, obj_t args)
{
  obj_t arg, car = NIL, cdr = NIL;

  if (argc > 1) {
    error(ERR_NUM_ARGS);
  } else if (argc == 1) {
    arg = CAR(args);
    
    if (is_kind_of(arg, consts.cl.dptr)) {
      car = CAR(arg);
      cdr = CDR(arg);
    } else {
      error(ERR_INVALID_ARG, arg);
    }
  }

  m_cons(consts.cl.pair, car, cdr);
}

void
cm_pair_eval(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.pair))  error(ERR_INVALID_ARG, recvr);

  vm_push(1);
  
  m_method_call_1(consts.str.eval, CAR(recvr));
  vm_assign(1, R0);
  m_method_call_1(consts.str.eval, CDR(recvr));
  m_cons(consts.cl.pair, R1, R0);
  
  vm_pop(1);
}

void
cm_pair_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.pair))  error(ERR_INVALID_ARG, recvr);

  vm_pushm(1, 2);
  
  m_method_call_1(consts.str.tostring, CAR(recvr));
  vm_assign(1, R0);
  m_method_call_1(consts.str.tostring, CDR(recvr));
  vm_assign(2, R0);
  m_string_new(5, 1, "(",
	          STRING(R1)->size, STRING(R1)->data,
	          2, ", ",
	          STRING(R2)->size, STRING(R2)->data,
	          1, ")"
	       );
  
  vm_popm(1, 2);
}

void
cm_pair_at(unsigned argc, obj_t args)
{
  obj_t recvr, arg, result;

  if (argc != 2)                            error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.pair))   error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))  error(ERR_INVALID_ARG, arg);

  switch (INTEGER(arg)->val) {
  case 0:
    result = CAR(recvr);
    break;
  case 1:
    result = CDR(recvr);
    break;
  default:
    error(ERR_IDX_RANGE, arg);
  }
  
  vm_assign(0, result);
}

/***************************************************************************/

/* Class: List */

unsigned
list_len(obj_t list)
{
    unsigned result;

    for (result = 0; list; list = CDR(list), ++result) {
      ASSERT(inst_of(list) == consts.cl.list);
    }

    return (result);
}

void
cm_list_new(unsigned argc, obj_t args)
{
  obj_t arg;

  if (argc == 0) {
    vm_assign(0, NIL);
    return;
  }
  
  if (argc > 1)  error(ERR_NUM_ARGS);

  arg = CAR(args);

  if (is_kind_of(arg, consts.cl.pair)) {
    m_cons(consts.cl.list, CDR(arg), NIL);
    m_cons(consts.cl.list, CAR(arg), R0);

    return;
  }
  if (is_kind_of(arg, consts.cl.list)) {
    vm_assign(0, arg);
    
    return;
  }
  if (is_kind_of(arg, consts.cl.array)) {
    obj_t    *p, *q;
    unsigned n;

    vm_push(1);
    
    vm_assign(1, NIL);
    for (p = &R1, q = ARRAY(arg)->data, n = ARRAY(arg)->size; n; --n, ++q) {
      m_cons(consts.cl.list, *q, NIL);
      obj_assign(p, R0);
      p = &CDR(R0);
    }
    vm_assign(0, R1);

    vm_pop(1);

    return;
  }
  if (is_kind_of(arg, consts.cl.dict)) {
    obj_t    *p, *q, r;
    unsigned n;

    vm_push(1);
    
    vm_assign(1, NIL);
    for (p = &R1, q = DICT(arg)->base.data, n = DICT(arg)->base.size; n; --n, ++q) {
      for (r = *q; r; r = CDR(r)) {
	m_cons(consts.cl.list, CAR(r), NIL);
	obj_assign(p, R0);
	p = &CDR(R0);
      }
    }
    vm_assign(0, R1);

    vm_pop(1);

    return;
  }

  error(ERR_INVALID_ARG, arg);
}

void
cm_list_len(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);

  m_integer_new(list_len(recvr));
}

void
_list_concat(obj_t list, obj_t obj)
{
    obj_t p, q;

    for (p = list; q = CDR(p); p = q);
    OBJ_ASSIGN(CDR(p), obj);
}

void
m_list_concat(obj_t list, obj_t obj)
{
    vm_push(0);

    m_cons(consts.cl.list, obj, NIL);
    _list_concat(list, R0);

    vm_pop(0);
}

void
m_list_tostr(obj_t list, char *delim)
{
    char  c;
    obj_t p;

    vm_push(0);
    vm_push(1);

    m_string_new(0);
    vm_assign(1, R0);
    c = delim[0];
    for (p = list; p; p = CDR(p), c = ' ') {
      m_method_call_1(consts.str.tostring, CAR(p));
      m_string_new(3, STRING(R1)->size, STRING(R1)->data,
		      1,                &c,
		      STRING(R0)->size, STRING(R0)->data
		   );
      vm_assign(1, R0);
    }
    m_string_new(2, STRING(R1)->size, STRING(R1)->data, 1, &delim[1]);

    vm_pop(1);
    vm_drop();
}

void
cm_list_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);

  m_list_tostr(recvr, "()");
}

void
m_list_eval(obj_t list)
{
  obj_t *q;
  
  vm_push(0);
  vm_push(1);
  
  vm_assign(1, NIL);
  for (q = &R1; list; list = CDR(list)) {
    m_method_call_1(consts.str.eval, CAR(list));
    m_cons(consts.cl.list, R0, NIL);
    obj_assign(q, R0);
    q = &CDR(R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
  vm_drop();
}

void
cm_list_eval(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);

  m_list_eval(recvr);
}

void
cm_list_map(unsigned argc, obj_t args)
{
  obj_t recvr, arg, *p, q;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));

  vm_push(1);

  vm_assign(1, NIL);
  for (p = &R1, q = recvr; q; q = CDR(q)) {
    m_method_call_2(consts.str.evalc, arg, CAR(q));
    m_cons(consts.cl.list, R0, NIL);
    obj_assign(p, R0);
    p = &CDR(R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
}

void
cm_list_foreach(unsigned argc, obj_t args)
{
  obj_t recvr, arg, *p, q;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));

  vm_push(1);

  vm_assign(1, NIL);
  for (p = &R1, q = recvr; q; q = CDR(q)) {
    m_cons(consts.cl.list, CAR(q), NIL);
    m_method_call_2(consts.str.evalc, arg, R0);
    m_cons(consts.cl.list, R0, NIL);
    obj_assign(p, R0);
    p = &CDR(R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
}

void
cm_list_splice(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.string))  error(ERR_INVALID_ARG, arg);

  vm_push(1);

  m_string_new(0);
  vm_assign(1, R0);
  for ( ; recvr; recvr = CDR(recvr)) {
    m_method_call_1(consts.str.tostring, CAR(recvr));
    if (STRING(R1)->size != 0) {
      m_string_new(3, STRING(R1)->size, STRING(R1)->data,
		      STRING(arg)->size, STRING(arg)->data,
		      STRING(R0)->size, STRING(R0)->data
		   );
    }
    vm_assign(1, R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
}

void
cm_list_append(unsigned argc, obj_t args)
{
  obj_t recvr, arg, *p, q;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!(arg == NIL || is_kind_of(arg, consts.cl.list)))      error(ERR_INVALID_ARG, arg);
  
  vm_push(1);
  
  vm_assign(1, NIL);
  for (p = &R1, q = recvr; q; q = CDR(q)) {
    m_cons(consts.cl.list, CAR(q), NIL);
    obj_assign(p, R0);
    p = &CDR(R0);
  }
  obj_assign(p, arg);
  vm_assign(0, R1);
  
  vm_pop(1);
}
 
void
cm_list_hash(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);

  vm_push(1);
  
  m_integer_new(0);
  vm_assign(1, R0);
  for ( ; recvr; recvr = CDR(recvr)) {
    vm_method_call_1(consts.str.hash, CAR(recvr));
    vm_method_call_2(consts.str.addc, R1, R0); /* TBD: Or call directly? */
    vm_assign(1, R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
}

void
cm_list_equals(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!(arg == NIL || is_kind_of(arg, consts.cl.list)))      error(ERR_INVALID_ARG, arg);

  vm_push(1);
  
  vm_assign(1, consts.bool._true);
  for ( ;
	BOOLEAN(R1)->val && recvr && arg;
	recvr = CDR(recvr), arg = CDR(arg)
	) {
    vm_method_call_2(consts.str.equalsc, CAR(recvr), CAR(arg));
    vm_method_call_2(consts.str.andc, R1, R0); /* TBD: Or call directly? */
    vm_assign(1, R0);
  }
  if (recvr || arg)  vm_assign(1, consts.bool._false);
  vm_assign(0, R1);
  
  vm_pop(1);
}

void
cm_list_at(unsigned argc, obj_t args)
{
  obj_t       recvr, arg, p;
  integer_val_t i;
  unsigned    len;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))  error(ERR_INVALID_ARG, arg);
  i   = INTEGER(arg)->val;
  len = list_len(recvr);
  if (i < 0)  i = (integer_val_t) len - i;
  if (i < 0 || i >= (integer_val_t) len)  error(ERR_IDX_RANGE, arg);

  for (p = recvr; p; p = CDR(p), --i) {
    if (i == 0) {
      vm_assign(0, CAR(p));
      return;
    }
  }

  HARD_ASSERT(0);
}

void
cm_list_at_len(unsigned argc, obj_t args)
{
  obj_t       recvr, idx, len, p, *q;
  integer_val_t i, n;
  unsigned    rlen;

  if (argc != 2)                            error(ERR_NUM_ARGS);
  recvr = CAR(args);  args  = CDR(args);
  if (!is_kind_of(recvr, consts.cl.list))   error(ERR_INVALID_ARG, recvr);
  idx  = CAR(args);  args = CDR(args);
  if (!is_kind_of(idx, consts.cl.integer))  error(ERR_INVALID_ARG, idx);
  len = CAR(args);
  if (!is_kind_of(len, consts.cl.integer))  error(ERR_INVALID_ARG, len);
  i   = INTEGER(idx)->val;
  n   = INTEGER(len)->val;
  rlen = list_len(recvr);
  if (i < 0)  i = (integer_val_t) rlen - i;
  if (i < 0 || (i + n) > (integer_val_t) rlen)  error(ERR_IDX_RANGE_2, idx, len);

  vm_push(1);

  vm_assign(1, NIL);
  for (q = &R1, p = recvr; p && n; p = CDR(p)) {
    if (i == 0) {
      m_cons(consts.cl.list, CAR(p), NIL);
      obj_assign(q, R0);
      q = &CDR(R0);
      --n;
    } else {
      --i;
    }
  }
  vm_assign(0, R1);

  vm_pop(1);
}

void
cm_list_filter(unsigned argc, obj_t args)
{
  obj_t recvr, arg, *p;

  if (argc != 2)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.list))  error(ERR_INVALID_ARG, recvr);
  arg = CDR(CDR(args));
  if (!is_kind_of(arg, consts.cl.list))    error(ERR_INVALID_ARG, arg);

  vm_push(1);

  vm_assign(1, NIL);
  for (p = &R1; recvr && arg; recvr = CDR(recvr), arg = CDR(arg)) {
    obj_t f = CAR(arg);

    if (!is_kind_of(f, consts.cl.boolean))  error(ERR_INVALID_ARG, arg);
    if (!BOOLEAN(f)->val)  continue;
    
    m_cons(consts.cl.list, CAR(recvr), NIL);
    obj_assign(p, R0);
    p = &CDR(R0);
  }
  vm_assign(0, R1);

  vm_pop(1);
}

void
cm_list_reduce(unsigned argc, obj_t args)
{
  obj_t recvr, func, p;

  if (argc != 3)  error(ERR_NUM_ARGS);
  recvr = CAR(args);  args = CDR(args);
  if (!(recvr == NIL || is_kind_of(recvr, consts.cl.list)))  error(ERR_INVALID_ARG, recvr);
  func = CAR(args);  args = CDR(args);

  vm_push(1);
  
  vm_assign(1, CAR(args));
  for (p = recvr; p; p = CDR(p)) {
    m_cons(consts.cl.list, CAR(p), NIL);
    m_cons(consts.cl.list, R1, R0);
    vm_method_call_2(consts.str.evalc, func, R0);
    vm_assign(1, R0);
  }
  vm_assign(0, R1);
  
  vm_pop(1);
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
m_method_call_new(obj_t list)
{
    vm_push(0);

    m_inst_alloc(consts.cl.method_call);
    inst_init(R0, list);

    vm_drop();
}

void
cm_method_call_new(unsigned argc, obj_t args)
{
  obj_t arg;

  if (argc != 1)                         error(ERR_NUM_ARGS);
  arg = CAR(args);
  if (!is_kind_of(arg, consts.cl.list))  error(ERR_INVALID_ARG, arg);

  m_method_call_new(arg);
}

void
cm_method_call_eval(unsigned argc, obj_t args)
{
  obj_t    recvr;
  unsigned n, nargc, s, quotef = 0;
  obj_t    li, p, *q;
  char     *r;
  
  if (argc != 1)                                  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.method_call))  error(ERR_INVALID_ARG, recvr);

  /* Scan to calculate length of selector and number of args */
  
  li = METHOD_CALL(recvr)->list;
  for (s = 0, n = 0, p = li; p; p = CDR(p), ++n) {
    if (n & 1) {
      ASSERT(is_kind_of(CAR(p), consts.cl.string));

      s += STRING(CAR(p))->size;
    }
  }
  
  if (n == 2) {
    nargc = 1;
    
    quotef = string_equal(CAR(CDR(li)), consts.str.quote);
  } else if (n >= 3) {
    ASSERT((n & 1) == 1);
    
    nargc = 1 + (n >> 1);
  } else  ASSERT(0);

  vm_pushm(1, 2);

  vm_assign(1, NIL);
  m_inst_alloc(consts.cl.string);
  inst_init(R0, s);
  vm_assign(2, R0);
  for (q = &R1, r = STRING(R2)->data, n = 0, p = li; p; p = CDR(p), ++n) {
    if (n & 1) {
      s = STRING(CAR(p))->size;
      memcpy(r, STRING(CAR(p))->data, s);
      r += s;
      continue;
    }
    
    vm_assign(0, CAR(p));
    if (!quotef)  m_method_call_1(consts.str.eval, R0);
    m_cons(consts.cl.list, R0, NIL);
    obj_assign(q, R0);
    q = &CDR(R0);
  }
    
  vm_push(2);
  vm_push(1);

  FRAME_METHOD_CALL_BEGIN(R2, R1) {

    method_call(R2, nargc, R1);

  } FRAME_METHOD_CALL_END;

  vm_dropn(2);
  
  vm_popm(1, 2);
}

void
cm_method_call_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                                  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.method_call))  error(ERR_INVALID_ARG, recvr);

  list_tostr(METHOD_CALL(recvr)->list, "[]");
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
m_block_new(obj_t list)
{
  vm_push(0);

  m_inst_alloc(consts.cl.block);
  inst_init(R0, list);
  
  vm_drop();
}

void
cm_block_eval(unsigned argc, obj_t args)
{
  obj_t recvr, arg, li, p;

  if (argc != 2)                            error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.block))  error(ERR_INVALID_ARG);
  li = BLOCK(recvr)->list;
  if (li == NIL)                            error(ERR_BAD_FORM, recvr);
  p = CAR(li);
  if (!(p == NIL || is_kind_of(p, consts.cl.list)))      error(ERR_BAD_FORM, recvr);
  arg = CAR(CDR(args));
  if (!(arg == NIL || is_kind_of(arg, consts.cl.list)))  error(ERR_INVALID_ARG);
  if (list_len(p) != list_len(arg))         error(ERR_NUM_ARGS);

  m_string_dict_new(16);
  for ( ; p; p = CDR(p), arg = CDR(arg)) {
    dict_at_put(R0, CAR(p), CAR(arg));
  }
  vm_push(0);
  
  FRAME_BLOCK_BEGIN(R0) {
    
    if (block_arg == 0) {
      vm_assign(0, NIL);
      for (p = CDR(li); p; p = CDR(p)) {
	m_method_call_1(consts.str.eval, CAR(p));
      }
    }
    
  } FRAME_BLOCK_END;
  
  vm_drop();
}

void
cm_block_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.block))  error(ERR_INVALID_ARG, recvr);

  list_tostr(BLOCK(recvr)->list, "{}");
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
m_array_new(unsigned size)
{
    m_inst_alloc(consts.cl.array);
    inst_init(R0, size);
}

unsigned dict_count(obj_t d);

void
cm_array_new(unsigned argc, obj_t args)
{
  obj_t arg;

  if (argc != 1)  error(ERR_NUM_ARGS);
  arg = CAR(args);

  if (is_kind_of(arg, consts.cl.integer)) {
    integer_val_t size = INTEGER(arg)->val;

    if (size < 0)  error(ERR_INVALID_ARG, arg);

    m_array_new(size);
    return;
  }
  if (is_kind_of(arg, consts.cl.list)) {
    obj_t    *p;
    unsigned n;
    
    m_array_new(list_len(arg));
    for (p = ARRAY(R0)->data, n = ARRAY(R0)->size; n; --n, ++p, arg = CDR(arg)) {
      obj_assign(p, CAR(arg));
    }
    return;
  }
  if (is_kind_of(arg, consts.cl.array)) {
    obj_t    *p, *q;
    unsigned n;

    m_array_new(ARRAY(arg)->size);
    for (p = ARRAY(R0)->data, q = ARRAY(arg)->data, n = ARRAY(arg)->size;
	 n;
	 --n, ++p, ++q
	 ) {
      obj_assign(p, *q);
    }
    return;
  }
  if (is_kind_of(arg, consts.cl.dict)) {
    unsigned size = dict_count(arg), n;
    obj_t    *p, *q, r;

    m_array_new(size);
    for (p = ARRAY(R0)->data, q = DICT(arg)->base.data, n = DICT(arg)->base.size;
	 n;
	 --n, ++q
	 ) {
      for (r = *q; r; r = CDR(r)) {
	obj_assign(p, CAR(r));
	++p;
      }
    }
  }
  
  error(ERR_INVALID_ARG, arg);
}

void
cm_array_at(unsigned argc, obj_t args)
{
  obj_t       recvr, arg;
  integer_val_t idx;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.array))   error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))   error(ERR_INVALID_ARG, arg);
  idx = INTEGER(arg)->val;
  if (idx < 0 || idx >= ARRAY(recvr)->size)  error(ERR_IDX_RANGE, arg);

  vm_assign(0, ARRAY(recvr)->data[idx]);
}

void
cm_array_at_put(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  integer_val_t idx;

  if (argc != 3)  error(ERR_NUM_ARGS);
  recvr = CAR(args);  args = CDR(args);
  if (!is_kind_of(recvr, consts.cl.array))   error(ERR_INVALID_ARG, recvr);
  arg = CAR(args);  args = CDR(args);
  if (!is_kind_of(arg, consts.cl.integer))   error(ERR_INVALID_ARG, arg);
  idx = INTEGER(arg)->val;
  if (idx < 0 || idx >= ARRAY(recvr)->size)  error(ERR_IDX_RANGE, arg);
  arg = CAR(args);

  OBJ_ASSIGN(ARRAY(recvr)->data[idx], arg);
  
  vm_assign(0, arg);
}

void
m_collection_tostring(obj_t obj)
{
  vm_push(0);

  m_method_call_2(consts.str.newc, consts.cl.list, obj);
  m_method_call_1(consts.str.tostring, R0); /* TBD: Or call directly? */

  vm_drop();
}

void
cm_array_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.array))  error(ERR_INVALID_ARG, recvr);

  m_collection_tostring(obj);
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
_dict_new(unsigned size, unsigned (*hash_func)(obj_t), unsigned (*equal_func)(obj_t, obj_t))
{
    m_inst_alloc(consts.cl.dict);
    inst_init(R0, hash_func, equal_func, size);
}

void
m_string_dict_new(unsigned size)
{
  vm_push(0);

  _dict_new(size, string_hash, string_equal);

  vm_drop();
}


unsigned
m_dict_key_hash_default(obj_t k)
{
  unsigned result;

  vm_push(0);
  
  vm_method_call_1(consts.str.hash, k);
  result = (unsigned) INTEGER(R0)->val;

  vm_pop(0);

  return (result);
}

unsigned
m_dict_key_eq_default(obj_t k1, obj_t k2)
{
  unsigned result;
  
  vm_push(0);
  
  vm_method_call_2(consts.str.equalsc, k1, k2);
  result = BOOLEAN(R0)->val;

  vm_pop(0);

  return (result);
}

void
m_dict_new(unsigned size)
{
  vm_push(0);

  _dict_new(size, m_dict_key_hash_default, m_dict_key_eq_default);

  vm_drop();
}

unsigned
m_dict_size_dflt(void)
{
  unsigned result;

  vm_push(0);

  m_method_call_1(consts.str.default_size, consts.cl.dict);
  if (!is_kind_of(R0, consts.cl.integer))  error(ERR_INVALID_VALUE);
  result = INTEGER(R0)->val;
  if (result <= 0)                         error(ERR_INVALID_VALUE);

  vm_pop(0);

  return (result);
}

void
cm_dict_new(unsigned argc, obj_t args)
{
  obj_t arg;

  if (argc == 0) {
    m_dict_new(m_dict_size_dflt());
    return;
  }

  if (argc > 1)  error(ERR_NUM_ARGS);

  arg = CAR(args);

  if (is_kind_of(arg, consts.cl.integer)) {
    integer_val_t size = INTEGER(arg)->val;

    if (size <= 0)  error(ERR_INVALID_ARG, arg);

    m_dict_new((unsigned) size);
    return;
  }
  if (is_kind_of(arg, consts.cl.list)) {
    obj_t p;

    for (p = arg; p; p = CDR(p)) {
      if (!is_kind_of(CAR(p), consts.cl.pair))  error(ERR_INVALID_ARG, arg);
    }

    m_dict_new(m_dict_size_dflt());

    for (p = arg; p; p = CDR(p)) {
      obj_t q = CAR(p);
      
      dict_at_put(R0, CAR(q), CDR(q));
    }

    return;
  }

  error(ERR_INVALID_ARG, arg);
}

obj_t
dict_find(obj_t dict, obj_t key, obj_t **pprev)
{
    obj_t p, *pp, *b = &DICT(dict)->base.data[(*DICT(dict)->hash_func)(key) % DICT(dict)->base.size];

    for (pp = b; p = *pp; pp = &CDR(p)) {
        obj_t q = CAR(p);

        if ((*DICT(dict)->equal_func)(CAR(q), key)) {
	    if (pprev)  *pprev = pp; 
	    return (p);
        }
    }

    if (pprev)  *pprev = b;
    return (NIL);
}

obj_t
dict_at(obj_t dict, obj_t key)
{
    obj_t p;

    return ((p = dict_find(dict, key, 0)) ? CAR(p) : NIL);
}

void
cm_dict_at(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dict))  error(ERR_INVALID_ARG, recvr);

  vm_assign(0, dict_at(recvr, CAR(CDR(args))));
}

void
dict_const_chk(obj_t key)
{
    if (inst_of(key) == consts.cl.string
	&& STRING(key)->size > 0
	&& STRING(key)->data[0] == '#'
	) {
	error(ERR_CONST);
    }
}

void
dict_at_put(obj_t dict, obj_t key, obj_t val)
{
    obj_t p, *pp;

    if (p = dict_find(dict, key, &pp)) {
	dict_const_chk(key);

        OBJ_ASSIGN(CDR(CAR(p)), val);
    } else {
      vm_push(0);
      
      m_cons(consts.cl.pair, key, val);
      m_cons(consts.cl.list, R0, *pp);
      obj_assign(pp, R0);

      vm_pop(0);
    }
}

void
cm_dict_at_put(unsigned argc, obj_t args)
{
  obj_t recvr, k, v;

  if (argc != 3)  error(ERR_NUM_ARGS);
  recvr = CAR(args);  args = CDR(args);
  if (!is_kind_of(recvr, consts.cl.dict))  error(ERR_INVALID_ARG, recvr);
  k = CAR(args);  args = CDR(args);
  v = CAR(args);
  
  dict_at_put(recvr, k, v);
  
  vm_assign(0, v);
}

void
dict_del(obj_t dict, obj_t key)
{
    obj_t p, *pp;

    if ((p = dict_find(dict, key, &pp)) == 0)  return;

    vm_push(1);

    vm_assign(1, p);
    obj_assign(pp, CDR(p));

    vm_pop(1);
}

void
cm_dict_del(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dict))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  
  dict_del(recvr, arg);
  
  vm_assign(0, arg);
}

void
m_dict_keys(obj_t dict)
{
    obj_t    *p, *q, r;
    unsigned n;

    vm_push(0);
    vm_push(1);

    vm_assign(1, NIL);
    for (p = &R1, q = DICT(dict)->base.data, n = DICT(dict)->base.size; n; --n, ++q) {
        for (r = *q; r; r = CDR(r)) {
            m_cons(consts.cl.list, CAR(CAR(r)), NIL);
            obj_assign(p, R0);
            p = &CDR(R0);
        }
    }
    vm_assign(0, R1);

    vm_pop(1);
    vm_drop();
}

void
cm_dict_keys(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dict))  error(ERR_INVALID_ARG, recvr);

  m_dict_keys(recvr);
}

void
cm_dict_tostring(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dict))  error(ERR_INVALID_ARG, recvr);

  m_collection_tostring(recvr);
}

unsigned
dict_count(obj_t d)
{
  unsigned result, n;
  obj_t    *p;

  for (result = 0, p = DICT(d)->base.data, n = DICT(d)->base.size; n; ++p) {
    result += list_len(*p);
  }

  return (result);
}

void
cm_dict_count(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.dict))  error(ERR_INVALID_ARG, recvr);

  m_integer_new(dict_count(recvr));
}

/***************************************************************************/

/* Class: Environment */

void
cm_env_new_put(unsigned argc, obj_t args)
{
  obj_t val;

  if (argc != 2)  error(ERR_NUM_ARGS);

  env_new_put(CAR(args), val = CAR(CDR(args)));

  vm_assign(0, val);
}

void
cm_env_new(unsigned argc, obj_t args)
{
  obj_t val = NIL;

  if (argc != 1)  error(ERR_NUM_ARGS);

  env_new_put(CAR(args), val);

  vm_assign(0, val);
}

void
cm_env_at_put(unsigned argc, obj_t args)
{
  obj_t val;

  if (argc != 2)  error(ERR_NUM_ARGS);

  env_at_put(CAR(args), val = CAR(CDR(args)));

  vm_assign(0, val);
}

void
cm_env_at(unsigned argc, obj_t args)
{
  if (argc != 1)  error(ERR_NUM_ARGS);

  vm_assign(0, env_at(CAR(args)));
}

void
cm_env_del(unsigned argc, obj_t args)
{
  if (argc != 1)  error(ERR_NUM_ARGS);
  
  env_del(CAR(args));
  
  vm_assign(0, NIL);
}

/***************************************************************************/

/* Class: System */

extern int yydebug, yy_flex_debug;

#ifdef DEBUG

void
cm_system_debug(unsigned argc, obj_t args)
{
  obj_t    arg;
  unsigned old, new;

  if (argc != 1)                            error(ERR_NUM_ARGS);
  arg = CAR(args);
  if (!is_kind_of(arg, consts.cl.integer))  error(ERR_INVALID_ARG, arg);

  old = debug.parse;   old <<= 1;
  old |= debug.mem;    old <<= 1;
  old |= debug.vm;

  new = (unsigned) INTEGER(arg)->val;
  
  debug.vm    = new;  new >>= 1;
  debug.mem   = new;  new >>= 1;
  debug.parse = new;
  yy_flex_debug = yydebug = debug.parse;
  
  m_integer_new(old);
}

void
cm_system_collect(unsigned argc, obj_t args)
{
  collect();
  
  vm_assign(0, NIL);
}

#endif

void
cm_system_exit(unsigned argc, obj_t args)
{
  if (argc != 0)  error(ERR_NUM_ARGS);

  exit(0);
}

void
cm_system_exitc(unsigned argc, obj_t args)
{
  obj_t arg;

  if (argc != 1)                            error(ERR_NUM_ARGS);
  arg = CAR(args);
  if (!is_kind_of(arg, consts.cl.integer))  error(ERR_INVALID_ARG, arg);

  exit((int) INTEGER(arg)->val);
}

/***************************************************************************/

/* Class: File */

void
inst_init_file(obj_t cl, obj_t inst, va_list ap)
{
    obj_t filename = va_arg(ap, obj_t);
    obj_t mode     = va_arg(ap, obj_t);
    FILE *fp       = va_arg(ap, FILE *);

    OBJ_ASSIGN(_FILE(inst)->filename, filename);
    OBJ_ASSIGN(_FILE(inst)->mode,     mode);
    _FILE(inst)->fp = fp;

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
m_file_new(obj_t filename, obj_t mode, FILE *fp)
{
  vm_push(0);

  m_inst_alloc(consts.cl.file);
  inst_init(R0, filename, mode, fp);

  vm_pop();
}

void
cm_file_new(unsigned argc, obj_t args)
{
  obj_t filename, mode;
  FILE *fp;

  if (argc != 2)                                error(ERR_NUM_ARGS);
  filename = CAR(args);
  if (!is_kind_of(filename, consts.cl.string))  error(ERR_INVALID_ARG, filename);
  mode = CAR(CDR(args));
  if (!is_kind_of(mode, consts.cl.string))      error(ERR_INVALID_ARG, mode);

  vm_pushm(1, 2);
  
  m_string_tocstr(filename);
  vm_assign(1, R0);
  m_string_tocstr(mode);
  vm_assign(2, R0);
  
  fp = fopen(STRING(R1)->data, STRING(R2)->data);
  
  if (fp == 0)  error(ERR_FILE_OPEN, filename, errno);
  
  vm_popm(1, 2);
  
  m_file_new(filename, mode, fp);
}

void
cm_file_load(unsigned argc, obj_t args)
{
#if 0

  obj_t recvr;

  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.file))  error(ERR_INVALID_ARG, recvr);
  
  yy_push_file(_FILE(recvr)->fp, recvr);
  
  read_eval();
  
  yy_pop();

#endif
}

void
cm_file_read(unsigned argc, obj_t args)
{
  obj_t         recvr, arg;
  FILE          *fp;
  integer_val_t len;
  char          *p;
  unsigned      i;
  
  if (argc != 2)                            error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.file))   error(ERR_INVALID_ARG, recvr);
  fp = _FILE(recvr)->fp;
  arg = CAR(CDR(args));
  if (!is_kind_of(arg, consts.cl.integer))  error(ERR_INVALID_ARG, arg);
  len = INTEGER(arg)->val;
  if (len < 0)                              error(ERR_INVALID_ARG, arg);

  m_inst_alloc(consts.cl.string);
  inst_init(R0, (unsigned) len);

  for (i = 0, p = STRING(R0)->data; len; --len, ++p, ++i) {
    int c = fgetc(fp);
    
    if (c == EOF)  break;
    
    *p = c;
  }

  m_string_new(1, i, STRING(R0)->data);
}

void
cm_file_readln(unsigned argc, obj_t args)
{
  obj_t     recvr;
  FILE      *fp;
  char      *p;
  unsigned  i;
  
  if (argc != 1)                           error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.file))  error(ERR_INVALID_ARG, recvr);
  fp = _FILE(recvr)->fp;

  vm_push(1);
  
  m_inst_alloc(consts.cl.string);
  inst_init(R0, 32);
  
  for (i = 0, p = STRING(R0)->data; ; ++p, ++i) {
    int c = fgetc(fp);
    
    if (c == EOF || c == '\n')  break;
    
    if (i >= STRING(R0)->size) {
      vm_assign(1, R0);
      m_inst_alloc(consts.cl.string);
      inst_init(R0, STRING(R1)->size << 1);
      memcpy(STRING(R0)->data, STRING(R1)->data, i);
      p = STRING(R0)->data + i;
    }
    
    *p = c;
  }
  
  m_string_new(1, i, STRING(R0)->data);
  
  vm_pop(1);
}

/***************************************************************************/

/* Class: Module */

void
inst_init_module(obj_t cl, obj_t inst, va_list ap)
{
    obj_t name     = va_arg(ap, obj_t);
    obj_t parent   = va_arg(ap, obj_t);

    vm_push(0);

    OBJ_ASSIGN(MODULE(inst)->name, name);
    OBJ_ASSIGN(MODULE(inst)->parent, parent);
    m_string_dict_new(64);
    OBJ_ASSIGN(MODULE(inst)->dict, R0);

    vm_pop(0);

    inst_init_parent(cl, inst, ap);
}

void
inst_walk_module(obj_t cl, obj_t inst, void (*func)(obj_t))
{
    (*func)(MODULE(inst)->name);
    (*func)(MODULE(inst)->parent);
    (*func)(MODULE(inst)->dict);
    (*func)(MODULE(inst)->filename);

    inst_walk_parent(cl, inst, func);
}

void
inst_free_module(obj_t cl, obj_t inst)
{
    void *p;

    if (p = MODULE(inst)->ptr)  dlclose(p);

    inst_free_parent(cl, inst);
}

void
m_module_new(obj_t name, obj_t parent)
{
    vm_push(0);

    m_inst_alloc(consts.cl.module);
    inst_init(R0, name, parent);

    /* Add of module to environment deferred */

    vm_drop();
}

void
m_fqmodname(obj_t mod)
{
    obj_t p, s;

    vm_push(0);

    m_string_new(0);
    for ( ; p = MODULE(mod)->parent; mod = p) {
	s = MODULE(mod)->name;

	if (STRING(R0)->size == 0) {
	    vm_assign(0, s);
	    continue;
	}

	m_string_new(3, STRING(s)->size, STRING(s)->data,
		        1, ".",
		        STRING(R0)->size, STRING(R0)->data
		     );
    }

    vm_drop();
}

void
cm_module_name(unsigned argc, obj_t args)
{
  obj_t recvr;

  if (argc != 1)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.module))  error(ERR_INVALID_ARG, recvr);
  
  m_fqmodname(recvr);
}

void
cm_module_tostring(unsigned argc, obj_t args)
{
  cm_module_name(argc, args);
}

void
m_module_path(void)
{
  obj_t p, q;

  vm_push(0);

  m_method_call_1(consts.str.path, consts.cl.module);
  if (!is_kind_of(R0, consts.cl.list))  error(ERR_INVALID_VALUE_1, "module path", R0);
  for (p = R0; p; p = CDR(p)) {
    q = CAR(p);
    if (!is_kind_of(q, consts.cl.string))  error(ERR_INVALID_VALUE_1, "module path member", q);
  }

  vm_drop();
}

void
cm_module_new(unsigned argc, obj_t args)
{
  obj_t arg, p, q, module_prev;
  void  *ptr = 0;
  FILE  *fp = 0;
  
  if (argc != 1)  error(ERR_NUM_ARGS);
  arg = CAR(args);		/* arg = module name */
  if (!is_kind_of(arg, consts.cl.string))  error(ERR_INVALID_ARG, arg);
  
  vm_pushm(1, 4);
  
  m_module_path();
  vm_assign(1, R0);		/* R1 = path list */
  m_string_tocstr(arg);
  vm_assign(2, R0);		/* R2 = module name as C string */
  m_string_new(2, STRING(arg)->size, STRING(arg)->data,
	          4, ".so"
	       );
  vm_assign(3, R0);		/* R3 = module name + ".so" as C string */

  m_module_new(arg, module_cur);
  vm_assign(4, R0);		/* R4 = new module */

  FRAME_MODULE_BEGIN(R4) {

    for (p = R1; p; p = CDR(p)) {
      q = CAR(p);
      
      m_string_new(3, STRING(q)->size, STRING(q)->data,
		      1, "/",
		      STRING(R3)->size, STRING(R3)->data
		   );
      ptr = dlopen(STRING(R0)->data, RTLD_NOW);
      if (ptr != 0)  break;
      
      m_string_new(3, STRING(q)->size, STRING(q)->data,
		      1, "/",
		      STRING(R2)->size, STRING(R2)->data
		   );
      if (fp = fopen(STRING(R0)->data, "r+")) {
#if 0
	/* TODO: Use file infrastructure */
	
	yy_push_file(fp, NIL);
	
	read_eval();
	
	yy_pop();
#endif
	
	fclose(fp);
	
	break;
      }
    }
    
    if (p == NIL) {
      /* Load failed */
      
      error(ERR_MODULE_LOAD, arg, errno);
    }
    
    m_string_new(1, STRING(R0)->size - 1, STRING(R0)->data);
    OBJ_ASSIGN(MODULE(R4)->filename, R0);
    MODULE(R5)->ptr = ptr;

  } FRAME_MODULE_END;

  env_new_put(arg, R4); /* Add module to parent environment */
  
  vm_assign(0, R4);
  
  vm_popm(1, 4);
}

void
cm_module_at(unsigned argc, obj_t args)
{
  obj_t recvr, arg;

  if (argc != 2)  error(ERR_NUM_ARGS);
  recvr = CAR(args);
  if (!is_kind_of(recvr, consts.cl.module))  error(ERR_INVALID_ARG, recvr);
  arg = CAR(CDR(args));
  if (!is_kind_of(recvr, consts.cl.string))  error(ERR_INVALID_ARG, arg);

  vm_assign(0, dict_at(MODULE(recvr)->dict, arg));
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
      inst_walk_module,
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
    { &consts.str.Code_Method, "#Code-Method" },    
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
    { &consts.str.main,        "main" },
    { &consts.str.mapc,        "map:" },
    { &consts.str.minus,       "minus" },
    { &consts.str.mode,        "#mode" },
    { &consts.str.modc,        "mod:" },
    { &consts.str.multc,       "mult:" },
    { &consts.str.name,        "#name" },
    { &consts.str.new,         "new" },
    { &consts.str.newc,        "new:" },
    { &consts.str.newc_modec,  "new:mode:" },
    { &consts.str.newc_parentc_instance_variablesc, "new:parent:instance-variables:" },
    { &consts.str.newc_putc,   "new:put:" },
    { &consts.str.nil,         "#nil" },
    { &consts.str.not,         "not" },
    { &consts.str.orc,         "or:" },
    { &consts.str.parent,      "#parent" },
    { &consts.str.path,        "path" },
    { &consts.str.pquote,      "pquote" },
    { &consts.str.print,       "print" },
    { &consts.str.printc,      "print:" },
    { &consts.str.quote,       "quote" },
    { &consts.str.range,       "range" },
    { &consts.str.rangec,      "range:" },
    { &consts.str.rangec_stepc, "range:step:" },
    { &consts.str.readc,       "read:" },
    { &consts.str.readln,      "readln" },
    { &consts.str.reducec_initc, "reduce:init:" },
    { &consts.str._return,     "return" },
    { &consts.str.rindexc,     "rindex:" },
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
    { &consts.str.assert,      "assert" },
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
    { &consts.cl.system,      &consts.str.exit,     cm_system_exit },
    { &consts.cl.system,      &consts.str.exitc,    cm_system_exitc },
    { &consts.cl.env,         &consts.str.newc,     cm_env_new },
    { &consts.cl.env,         &consts.str.newc_putc, cm_env_new_put },
    { &consts.cl.env,         &consts.str.atc,      cm_env_at },
    { &consts.cl.env,         &consts.str.atc_putc, cm_env_at_put },
    { &consts.cl.env,         &consts.str.deletec,  cm_env_del }
#ifdef DEBUG
    ,
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
    { &consts.cl.file,        &consts.str.readln,     cm_file_readln },
    { &consts.cl.file,        &consts.str.load,       cm_file_load },
    { &consts.cl.module,      &consts.str.atc,        cm_module_at }
#ifdef DEBUG
    ,
    { &consts.cl.boolean,     &consts.str.assert,     cm_boolean_assert }
#endif
};

const struct init_inst_var init_inst_var_tbl[] = {
    { &consts.cl.metaclass, &consts.str.class_methods,    3 * sizeof(obj_t) },
    { &consts.cl.metaclass, &consts.str.class_variables,  4 * sizeof(obj_t) },
    { &consts.cl.metaclass, &consts.str.instance_methods, 5 * sizeof(obj_t) },
    { &consts.cl.file,      &consts.str.name,             0 * sizeof(obj_t) },
    { &consts.cl.file,      &consts.str.mode,             1 * sizeof(obj_t) }
};


void
init_cls(const struct init_cl *tbl, unsigned n)
{
    vm_push(0);

    for ( ; n; --n, ++tbl) {
      m_class_new(*tbl->pname, *tbl->pparent, tbl->inst_size,
		  *tbl->inst_init, *tbl->inst_walk, *tbl->inst_free
		  );
      obj_assign(tbl->pcl, R0);
    }

    vm_pop(0);
}

void
init_strs(const struct init_str *tbl, unsigned n)
{
    vm_push(0);

    for ( ; n; --n, ++tbl) {
      m_string_new(1, strlen(tbl->str), (char *) tbl->str);
      obj_assign(tbl->pobj, R0);
    }

    vm_pop(0);
}

void
init_cl_methods(const struct init_method *tbl, unsigned n)
{
    vm_push(0);

    for ( ; n; --n, ++tbl) {
        code_method_new(tbl->func);
        dict_at_put(CLASS(*tbl->pcl)->cl_methods, *tbl->psel, R0);
    }

    vm_pop(0);
}

void
init_inst_methods(const struct init_method *tbl, unsigned n)
{
    vm_push(0);

    for ( ; n; --n, ++tbl) {
        code_method_new(tbl->func);
        dict_at_put(CLASS(*tbl->pcl)->inst_methods, *tbl->psel, R0);
    }

    vm_pop(0);
}

void
init_inst_vars(const struct init_inst_var *tbl, unsigned n)
{
    vm_push(0);

    for ( ; n; --n, ++tbl) {
        integer_new(tbl->ofs);
        dict_at_put(CLASS(*tbl->pcl)->inst_vars, *tbl->psel, R0);
    }

    vm_pop(0);
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

    /* Initialization must be done in several steps, because of references
       between objects.
    */

    /* Step 1.  Set up Metaclass */

    OBJ_ASSIGN(consts.cl.metaclass, (obj_t) zcmalloc(sizeof(struct inst_metaclass)));
    list_insert(&consts.cl.metaclass->list_node, LIST_END(OBJ_LIST_ACTIVE));
    CLASS(consts.cl.metaclass)->inst_size = sizeof(struct inst_metaclass);
    CLASS(consts.cl.metaclass)->inst_init = inst_init_metaclass;
    CLASS(consts.cl.metaclass)->inst_walk = inst_walk_metaclass;
    CLASS(consts.cl.metaclass)->inst_free = inst_free_parent;

    /* Step 2.  Init all information for classes that does not depend on other
       classes */

    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        m_inst_alloc(consts.cl.metaclass);
        obj_assign(init_cl_tbl[i].pcl, R0);
        CLASS(*init_cl_tbl[i].pcl)->inst_size = init_cl_tbl[i].inst_size;
        CLASS(*init_cl_tbl[i].pcl)->inst_init = init_cl_tbl[i].inst_init;
        CLASS(*init_cl_tbl[i].pcl)->inst_walk = init_cl_tbl[i].inst_walk;
        CLASS(*init_cl_tbl[i].pcl)->inst_free = init_cl_tbl[i].inst_free;
    }

    /* Step 3.  Fix up Metaclass */

    OBJ_ASSIGN(consts.cl.metaclass->inst_of, consts.cl.object);

    /* Step 10.  Fix up classes, part 1 - parentage */

    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->parent, consts.cl.object);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        if (init_cl_tbl[i].pparent)  OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->parent, *init_cl_tbl[i].pparent);
    }

    /* Step 5.  Initialize all class dictionaries */

    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->cl_methods, R0);
    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->inst_methods, R0);
    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->cl_vars, R0);
    m_string_dict_new(16);
    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->inst_vars, R0);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
      m_string_dict_new(16);
      OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->cl_methods, R0);
      m_string_dict_new(16);
      OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->inst_methods, R0);
      m_string_dict_new(16);
      OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->cl_vars, R0);
      m_string_dict_new(16);
      OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->inst_vars, R0);
    }

    /* Step 6.  Initialize all strings */

    init_strs(init_str_tbl, ARRAY_SIZE(init_str_tbl));

    /* Step 7.  Initialize all methods */

    init_cl_methods(init_cl_method_tbl, ARRAY_SIZE(init_cl_method_tbl));
    init_inst_methods(init_inst_method_tbl, ARRAY_SIZE(init_inst_method_tbl));
    init_inst_vars(init_inst_var_tbl, ARRAY_SIZE(init_inst_var_tbl));

    /* Step 8.  Add all constants (classes and strings) to root set for
       collection */

    root_add(&consts.hdr, (sizeof(consts) - sizeof(consts.hdr)) / sizeof(obj_t));

    /* Step 9.  Set up the top-level Environment */

    module_new(consts.str.main, NIL);
    OBJ_ASSIGN(module_main, R0);

    dict_at_put(MODULE(module_main)->dict, consts.str.nil, NIL);
    boolean_new(1);
    dict_at_put(MODULE(module_main)->dict, consts.str._true, R0);
    boolean_new(0);
    dict_at_put(MODULE(module_main)->dict, consts.str._false, R0);

    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->name, consts.str.Metaclass);
    dict_at_put(MODULE(module_main)->dict, consts.str.Metaclass, consts.cl.metaclass);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
        OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->name, *init_cl_tbl[i].pname);
        dict_at_put(MODULE(module_main)->dict, *init_cl_tbl[i].pname, *init_cl_tbl[i].pcl);
    }

    /* Step 10.  Fix up classes, part 2 - module membership */

    OBJ_ASSIGN(CLASS(consts.cl.metaclass)->module, module_main);
    for (i = 0; i < ARRAY_SIZE(init_cl_tbl); ++i) {
	OBJ_ASSIGN(CLASS(*init_cl_tbl[i].pcl)->module, module_main);
    }

    /* Step 11.  Init class variables */

    file_new(NIL, NIL, stdin);
    dict_at_put(CLASS(consts.cl.file)->cl_vars, consts.str._stdin, R0);
    file_new(NIL, NIL, stdout);
    dict_at_put(CLASS(consts.cl.file)->cl_vars, consts.str._stdout, R0);
    file_new(NIL, NIL, stderr);
    dict_at_put(CLASS(consts.cl.file)->cl_vars, consts.str._stderr, R0);

    m_string_new(1, 1, ".");
    m_cons(consts.cl.list, R0, NIL);
    dict_at_put(CLASS(consts.cl.module)->cl_vars, consts.str.path, R0);
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


void
interactive(void)
{
  FRAME_RESTART_BEGIN {

    errorf = errorf;		/* Silence complaint about unused variable */

    for (;;) {
        printf("\nok ");
        fflush(stdout);

        if (yyparse() != 0)  break;

	vm_dropn(stack_end - sp); /* Discard all objs created during parsing */

        vm_method_call_1(consts.str.eval, R0);
        vm_method_call_1(consts.str.print, R0);
    }

  } FRAME_RESTART_END;
}

void
file_run(char *filename)
{
  vm_push(1);

  FRAME_RESTART_BEGIN {

    if (!errorf) {
      m_string_new(1, strlen(filename), filename);
      vm_assign(1, R0);
      m_string_new(1, 2, "r+");
      vm_method_call_3(consts.str.newc_modec, consts.cl.file, R1, R0);
      vm_method_call_1(consts.str.load, R0);
    }

  } FRAME_RESTART_END;

  vm_pop(1);
}

int
main(int argc, char **argv)
{
#ifdef YYDEBUG
  yydebug = 1;
#endif
#ifndef YY_FLEX_DEBUG
  yy_flex_debug = 0;
#endif
  
  init();
  
  FRAME_MODULE_BEGIN(module_main) {

    if (argc == 1) {
      interactive();
    } else {
      file_run(argv[1]);
    }

  } FRAME_MODULE_END;
  
  fini();
  
  return (0);
}

