/* the data, the bss, and a data object, that the program imports from
   msvcrt, e.g., _fmode, through the import address table */
#include "pe.h"

__declspec(dllimport) extern int _fmode;
int data = 0x55;
static char bss[2 * 4096 + 3];

void start(void) {
    unsigned long sum = 0;
    for (unsigned i = 0; i < sizeof(bss); i++) sum += bss[i];
    line("bss is zero", sum);
    line("data", data);
    _fmode = 0x8000;
    line("fmode", _fmode);
    ExitProcess(0);
}
