/* Prints A and loops forever:

   gcc -O1 -fno-builtin forever.c -o ../bin/x86_64-linux-gnu-forever */

#include <stdio.h>

int main(void) {
    volatile unsigned x = 0;
    putchar(0x41);
    putchar(10);
    for (;;) x++;
}
