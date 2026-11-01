/* What libmain.so needs, for the loader of Bap.Linux.Library:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libdep.so libdep.c -o libdep.so */

int dep_counter = 5;
int dep_order[8];
int dep_orders;

void dep_note(int who) { dep_order[dep_orders++] = who; }
int dep_add(int a, int b) { return a + b + dep_counter; }
const char *dep_name(void) { return "dep"; }

/* What another library has the same name for, which comes from whichever is found first. */
int either_one(void) { return 1; }

__attribute__((constructor)) static void dep_start(void) {
    dep_counter += 100;
    dep_note(1);
}
__attribute__((destructor)) static void dep_stop(void) { dep_note(9); }
