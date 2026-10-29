#include <lean/lean.h>
#include <z3.h>

#include <string>

#include <errno.h>
#include <pthread.h>
#include <time.h>

extern "C" int pthread_cond_clockwait(pthread_cond_t *condition,
                                       pthread_mutex_t *mutex,
                                       clockid_t clock,
                                       const struct timespec *timeout) {
  if (clock != CLOCK_MONOTONIC)
    return EINVAL;
  return pthread_cond_timedwait(condition, mutex, timeout);
}

namespace {

lean_obj_res io_error(const std::string &message) {
  return lean_io_result_mk_error(
      lean_mk_io_error_other_error(0, lean_mk_string(message.c_str())));
}

} // namespace

extern "C" lean_obj_res bap_z3_check_sat(lean_obj_arg script, lean_obj_arg) {
  Z3_config config = Z3_mk_config();
  Z3_context context = Z3_mk_context(config);
  Z3_del_config(config);
  if (!context)
    return io_error("unable to create Z3 context");
  Z3_solver solver = Z3_mk_solver(context);
  if (!solver) {
    Z3_del_context(context);
    return io_error("unable to create Z3 solver");
  }
  Z3_solver_inc_ref(context, solver);
  Z3_solver_from_string(context, solver, lean_string_cstr(script));
  Z3_lbool result = Z3_solver_check(context, solver);
  if (result == Z3_L_UNDEF) {
    Z3_solver_dec_ref(context, solver);
    Z3_del_context(context);
    return io_error("Z3 returned unknown");
  }
  bool satisfiable = result == Z3_L_TRUE;
  Z3_solver_dec_ref(context, solver);
  Z3_del_context(context);
  return lean_io_result_mk_ok(lean_box(satisfiable ? 1 : 0));
}
