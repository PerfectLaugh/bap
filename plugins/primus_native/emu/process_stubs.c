#include <stdlib.h>

#define CAML_NAME_SPACE
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>

#ifndef _WIN32
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <time.h>
#include <unistd.h>

struct deadline {
    double seconds;
    int code;
    volatile sig_atomic_t cancelled;
};

static void *deadline_watch(void *arg) {
    struct deadline *deadline = arg;
    struct timespec delay;
    delay.tv_sec = (time_t)deadline->seconds;
    delay.tv_nsec = (long)((deadline->seconds - (double)delay.tv_sec) * 1e9);
    while (nanosleep(&delay, &delay) < 0 && errno == EINTR) {
    }
    if (!deadline->cancelled)
        _exit(deadline->code);
    return NULL;
}

value bap_emu_process_deadline_start(value seconds, value code) {
    CAMLparam2(seconds, code);
    struct deadline *deadline = malloc(sizeof(*deadline));
    pthread_t thread;
    if (deadline == NULL)
        caml_raise_out_of_memory();
    deadline->seconds = Double_val(seconds);
    deadline->code = Int_val(code);
    deadline->cancelled = 0;
    if (pthread_create(&thread, NULL, deadline_watch, deadline) != 0) {
        free(deadline);
        caml_failwith("failed to start the deadline watchdog");
    }
    pthread_detach(thread);
    CAMLreturn(caml_copy_int64((uint64_t)deadline));
}

value bap_emu_process_deadline_cancel(value handle) {
    struct deadline *deadline = (struct deadline *)Int64_val(handle);
    deadline->cancelled = 1;
    return Val_unit;
}
#else
value bap_emu_process_deadline_start(value seconds, value code) {
    caml_failwith("native deadlines are not supported on this platform");
}

value bap_emu_process_deadline_cancel(value handle) {
    return Val_unit;
}
#endif
