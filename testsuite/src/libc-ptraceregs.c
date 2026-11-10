// The registers of a tracee of MIPS or PowerPC, as PTRACE_GETREGSET of NT_PRSTATUS and PTRACE_GETREGS give them: the regset is the size of
// the kernel's elf_gregset_t, and in both the pc is in the program and the stack pointer is where a local of the tracee is
// (testLinuxRaises). The tracee sends where its local is before it stops.
#define _GNU_SOURCE
#include <elf.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/ptrace.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <unistd.h>

extern char __executable_start, etext;

#if defined(__mips__)
#define REGSET_PC 40
#define REGSET_SP 35
#define REGS_PC 34
#define REGS_SP 29
typedef uint64_t RegsWord;
#elif defined(__powerpc__)
#define REGSET_PC 32
#define REGSET_SP 1
#define REGS_PC 32
#define REGS_SP 1
typedef unsigned long RegsWord;
#endif

static int inProgram(unsigned long pc) { return pc >= (unsigned long)&__executable_start && pc < (unsigned long)&etext; }
static int atStack(unsigned long sp, unsigned long local) { return sp <= local && local - sp < 65536; }

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  int channel[2];
  pipe(channel);
  pid_t child = fork();
  if (child == 0) {
    int local = 0;
    unsigned long where = (unsigned long)&local;
    write(channel[1], &where, sizeof where);
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    _exit(local);
  }
  unsigned long local;
  read(channel[0], &local, sizeof local);
  int status;
  waitpid(child, &status, 0);
  unsigned long regset[64] = {0};
  struct iovec vector = {regset, sizeof regset};
  long got = ptrace(PTRACE_GETREGSET, child, NT_PRSTATUS, &vector);
  printf("regset: %ld, of %zu words, pc in the program %d, sp at the stack %d\n", got, vector.iov_len / sizeof(unsigned long),
         inProgram(regset[REGSET_PC]), atStack(regset[REGSET_SP], local));
  RegsWord regs[64] = {0};
  got = ptrace(12, child, 0, regs);
  printf("getregs: %ld, pc in the program %d, sp at the stack %d\n", got, inProgram((unsigned long)regs[REGS_PC]),
         atStack((unsigned long)regs[REGS_SP], local));
  got = ptrace(13, child, 0, regs);
  printf("setregs of what getregs gave: %ld\n", got);
  ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
  printf("exited %d\n", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  return 0;
}
