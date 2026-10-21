/* the weak functions and data, that nothing defines, are null, and the
   program tests them, as crtstuff tests __gmon_start__ */
#include "common.h"

extern void missing_function(void) __attribute__((weak));
extern int missing_data __attribute__((weak));

int main(void) {
    line("function", missing_function ? 1 : 0);
    line("data", &missing_data ? 1 : 0);
    if (missing_function) missing_function();
    return 0;
}

void _start(void) { exit(main()); }
