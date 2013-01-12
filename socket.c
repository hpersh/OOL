#include <assert.h>
#include <stdarg.h>
#include <string.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netinet/in.h>

#include "ool.h"

#define ASSERT  assert

#define ARRAY_SIZE(a)  (sizeof(a) / sizeof((a)[0]))

struct inst_socket {
    struct obj base;
    int        fd;
};
#define SOCKET(obj)  ((struct inst_socket *)(obj))

struct {
    struct root_hdr hdr;
    obj_t module;
    struct {
	obj_t socket;
    } cl;
    struct {
	obj_t Socket;
	obj_t bindc;
	obj_t connectc;
	obj_t sendc;
	obj_t recvc;
    } str;
} socket_consts;


void
inst_init_socket(obj_t cl, obj_t inst, va_list ap)
{
    int fd = va_arg(ap, int);

    SOCKET(inst)->fd = fd;
    cl_inst_init(CLASS(cl)->parent, inst, ap);
}

void
inst_free_socket(obj_t cl, obj_t inst)
{
    close(SOCKET(inst)->fd);
    cl_inst_free(CLASS(cl)->parent, inst);
}

void
cm_socket_new(unsigned argc)
{
    int fd = socket(AF_INET, SOCK_STREAM, 0);

    ASSERT(fd >= 0);

    vm_inst_alloc(0, socket_consts.cl.socket);
    inst_init(R0, fd);
}

void
cm_socket_bind(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0, ipaddr = CAR(arg), port = CDR(arg);
    struct sockaddr_in sockaddr;
    int rc;

    VM_PUSH(R1);

    string_tocstr(1, ipaddr);

    memset(&sockaddr, 0, sizeof(sockaddr));
    sockaddr.sin_family = AF_INET;
    inet_aton(STRING(R1)->data, &sockaddr.sin_addr);
    sockaddr.sin_port   = htons(INTEGER(port)->val);
    rc = bind(SOCKET(recvr)->fd, (const struct sockaddr *) &sockaddr, sizeof(sockaddr));

    ASSERT(rc == 0);

    VM_POP(R1);

    VM_ASSIGN(R0, recvr);
}

void
cm_socket_connect(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0, ipaddr = CAR(arg), port = CDR(arg);
    struct sockaddr_in sockaddr;
    int rc;

    VM_PUSH(R1);

    string_tocstr(1, ipaddr);

    memset(&sockaddr, 0, sizeof(sockaddr));
    sockaddr.sin_family = AF_INET;
    inet_aton(STRING(R1)->data, &sockaddr.sin_addr);
    sockaddr.sin_port   = htons(INTEGER(port)->val);
    rc = connect(SOCKET(recvr)->fd, (const struct sockaddr *) &sockaddr, sizeof(sockaddr));

    ASSERT(rc == 0);

    VM_POP(R1);

    VM_ASSIGN(R0, recvr);
}

void
cm_socket_send(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;
    int rc;

    rc = send(SOCKET(recvr)->fd, STRING(arg)->data, STRING(arg)->size, 0);

    ASSERT(rc >= 0);

    VM_ASSIGN(R0, recvr);
}

void
cm_socket_recv(unsigned argc)
{
    obj_t recvr = MC_FRAME_RECVR, arg = MC_FRAME_ARG_0;
    int   n, rc;

    VM_PUSHM(R1, 2);

    vm_inst_alloc(1, consts.cl.string);
    inst_init(R1, n = INTEGER(arg)->val);
    memset(STRING(R1)->data, 0, n);

    rc = recv(SOCKET(recvr)->fd, STRING(R1)->data, n, 0);

    ASSERT(rc >= 0);

    integer_new(2, rc);
    cons(0, consts.cl.pair, R2, R1);

    VM_POPM(R1, 2);
}

const struct init_str socket_init_str_tbl[] = {
    { &socket_consts.str.Socket,   "#Socket" },
    { &socket_consts.str.bindc,    "bind:" },
    { &socket_consts.str.connectc, "connect:" },
    { &socket_consts.str.sendc,    "send:" },
    { &socket_consts.str.recvc,    "recv:" }
};

const struct init_cl socket_init_cl_tbl[] = {
    { &socket_consts.cl.socket,
      &consts.cl.object,
      &socket_consts.str.Socket,
      sizeof(struct inst_socket),
      inst_init_socket,
      inst_walk_passthru,
      inst_free_socket
    }
};

const struct init_method socket_init_cl_method_tbl[] = {
    { &socket_consts.cl.socket, &consts.str.new, cm_socket_new }
};

const struct init_method socket_init_inst_method_tbl[] = {
    { &socket_consts.cl.socket, &socket_consts.str.bindc,    cm_socket_bind },
    { &socket_consts.cl.socket, &socket_consts.str.connectc, cm_socket_connect },
    { &socket_consts.cl.socket, &socket_consts.str.sendc,    cm_socket_send },
    { &socket_consts.cl.socket, &socket_consts.str.recvc,    cm_socket_recv }
};

__attribute__((constructor))
void socket_init(void)
{
    VM_ASSIGN(socket_consts.module, R0);

    init_strs((const struct init_str *) &socket_init_str_tbl, ARRAY_SIZE(socket_init_str_tbl));

    init_cls((const struct init_cl *) &socket_init_cl_tbl, ARRAY_SIZE(socket_init_cl_tbl));

    init_cl_methods((const struct init_method *) &socket_init_cl_method_tbl, ARRAY_SIZE(socket_init_cl_method_tbl));
    init_inst_methods((const struct init_method *) &socket_init_inst_method_tbl, ARRAY_SIZE(socket_init_inst_method_tbl));

    root_add(&socket_consts.hdr, (sizeof(socket_consts) - sizeof(socket_consts.hdr)) / sizeof(obj_t));
}


__attribute__((destructor))
void socket_fini(void)
{
    
}

