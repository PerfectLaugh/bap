/* What imports two names of one function, and something that the host serves, for Bap.Linux.Library:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libuser.so libuser.c libalias.so -o libuser.so */

extern int alias_one(int);
extern int alias_two(int);
extern void host_note(int);

int call_one(int value) { return alias_one(value); }
int call_two(int value) { return alias_two(value); }

__attribute__((constructor)) static void user_start(void) { host_note(2); }
