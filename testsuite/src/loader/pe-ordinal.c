/* the function, that the program imports by its ordinal, see
   ordinal.def, which has no name, so nothing links it */
#include "pe.h"

__declspec(dllimport) int unnamed(int);

void start(void) {
    line("before", 1);
    line("unnamed", unnamed(2));
    ExitProcess(0);
}
