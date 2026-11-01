/* Thread-local storage that goes by a module and an offset, which `__tls_get_addr` of libtlsrt.c turns into an address, or on the targets
   that have it, a descriptor: -ftls-model=global-dynamic, and for those -mtls-dialect=gnu2 on x86, which AArch64 does by default. */
extern __thread int per_thread;
__thread int dynamic_per_thread = 21;
int dynamic_own(void) { return dynamic_per_thread; }
int dynamic_other(void) { return per_thread; }
int dynamic_set(int value) { dynamic_per_thread = value; return dynamic_per_thread; }
