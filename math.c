#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <math.h>

#include "ool.h"

#define ASSERT  assert

#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

struct {
    struct root_hdr hdr;
    obj_t module;
    struct {
	obj_t sin;
	obj_t cos;
	obj_t exp;
    } str;
} math_consts;


void
cm_float_sin(unsigned argc)
{
    float_new(0, sinl(FLOAT(FRAME_RECVR)->val));
}

void
cm_float_cos(unsigned argc)
{
    float_new(0, cosl(FLOAT(FRAME_RECVR)->val));
}

void
cm_float_exp(unsigned argc)
{
    float_new(0, expl(FLOAT(FRAME_RECVR)->val));
}

const struct init_str math_init_str_tbl[] = {
    { &math_consts.str.sin, "sin" },
    { &math_consts.str.cos, "cos" },
    { &math_consts.str.exp, "exp" }
};

const struct init_cl math_init_cl_tbl[] = {
};

const struct init_method math_init_cl_method_tbl[] = {
};

const struct init_method math_init_inst_method_tbl[] = {
    { &consts.cl._float, &math_consts.str.sin, cm_float_sin },
    { &consts.cl._float, &math_consts.str.cos, cm_float_cos },
    { &consts.cl._float, &math_consts.str.exp, cm_float_exp }
};

__attribute__((constructor))
void math_init(void)
{
    VM_ASSIGN(math_consts.module, R0);

    init_strs((const struct init_str *) &math_init_str_tbl, ARRAY_SIZE(math_init_str_tbl));

    init_cls((const struct init_cl *) &math_init_cl_tbl, ARRAY_SIZE(math_init_cl_tbl));

    init_cl_methods((const struct init_method *) &math_init_cl_method_tbl, ARRAY_SIZE(math_init_cl_method_tbl));
    init_inst_methods((const struct init_method *) &math_init_inst_method_tbl, ARRAY_SIZE(math_init_inst_method_tbl));

    root_add(&math_consts.hdr, (sizeof(math_consts) - sizeof(math_consts.hdr)) / sizeof(obj_t));
}


__attribute__((destructor))
void math_fini(void)
{
    
}

