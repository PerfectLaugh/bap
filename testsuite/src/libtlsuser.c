/* What is thread-local in another library, and its own besides, in the model that needs a static offset: see libtls.c. */
extern __thread int per_thread;
__thread int own_per_thread = 11;
int other_get(void) { return per_thread; }
int own_get(void) { return own_per_thread; }
