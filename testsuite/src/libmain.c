/* A library for the loader of Bap.Linux.Library, with each thing that a loader has to get right, without a libc:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libmain.so -Wl,--no-undefined? libmain.c libdep.so -o libmain.so
   It imports what the host gives it, which doesn't come from any library. */

extern int dep_counter;
extern int dep_add(int, int);
extern const char *dep_name(void);
extern void dep_note(int);
extern int either_one(void);
extern int host_given(int);
extern int absent_weak(void) __attribute__((weak));
extern int absent_weak_data __attribute__((weak));

int main_data = 7;
int main_bss[4096];

static int twice(int value) { return value * 2; }
static int thrice(int value) { return value * 3; }

/* Words that have to be moved: what is local, in a table and in data that goes read-only after. */
static int (*const functions[])(int) = {twice, thrice};
int *const to_own_data = &main_data;
static const char *const text_of[] = {"zero", "one", "two"};
/* And words of what is elsewhere. */
int *const to_dep_data = &dep_counter;
int (*const to_dep_function)(int, int) = dep_add;
/* With something added to it. */
int *const into_own_bss = &main_bss[3];

int table_call(int which, int value) { return functions[which](value); }
int own_data(void) { return *to_own_data; }
int bss_is_zero(void) {
    int total = 0;
    for (int index = 0; index < 4096; index++) total |= main_bss[index];
    return total == 0;
}
int bss_offset_right(void) { return into_own_bss == &main_bss[3]; }
int set_bss(int index, int value) { main_bss[index] = value; return main_bss[index]; }
char text_char(int which, int at) { return text_of[which][at]; }
int dep_data_through_pointer(void) { return *to_dep_data; }
int dep_data_directly(void) { return dep_counter; }
int dep_call(int a, int b) { return dep_add(a, b); }
int dep_call_through_pointer(int a, int b) { return to_dep_function(a, b); }
char dep_text(int at) { return dep_name()[at]; }
int from_host(int value) { return host_given(value); }
int weak_is_absent(void) { return absent_weak == 0 && &absent_weak_data == 0; }
int which_one(void) { return either_one(); }
int many(int a, int b, int c, int d) { return a + 10 * b + 100 * c + 1000 * d; }

__attribute__((constructor)) static void main_start(void) {
    main_data += 1000;
    dep_note(2);
}
__attribute__((constructor(101))) static void main_earlier(void) { dep_note(3); }
__attribute__((destructor)) static void main_stop(void) { dep_note(8); }
