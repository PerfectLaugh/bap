/* the stream, that the program imports, e.g., stdin, which it reads
   through the slot of the GOT, also when the file has no sections */
#include "common.h"

extern void *stdin;
extern int fgetc(void *);

int main(void) {
    int c = fgetc(stdin);
    line("read", c);
    return 0;
}

void _start(void) { exit(main()); }
