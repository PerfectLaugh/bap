#ifndef BAP_UNICORN_REGS_H
#define BAP_UNICORN_REGS_H

#include <unicorn/unicorn.h>

struct bap_uc_reg {
    const char *name;
    int id;
};

/* the registers of the architecture, terminated with a null name, or
   null if the architecture is not built */
const struct bap_uc_reg *bap_uc_reg_table(uc_arch arch);

#endif
