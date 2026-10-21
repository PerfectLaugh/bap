/* The runtime of the programs, that the recompile pass of BAP makes.

   The recompiled code works on the memory of the original program, at its
   original addresses, so the runtime maps the loadable segments of the
   original file there, applies its dynamic relocations against the
   libraries of this process, e.g., the copy of stdout, and runs the
   program on a stack of its own, whose return address, that main finally
   returns to, is the magic value, that the recompiled code knows. */

#define _GNU_SOURCE
#include <dlfcn.h>
#include <elf.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

/* defined by the recompiled program */
extern const char bap_image_path[];
extern uint64_t bap_RSP, bap_RDI, bap_RSI, bap_RDX, bap_RAX;
extern void bap_start(uint64_t ret);

#define MAGIC 0xbadc0ffee0ddf00dULL
#define STACK_SIZE (8UL << 20)

static void fail(const char *fmt, uint64_t x) {
  fprintf(stderr, "bap-recompile: ");
  fprintf(stderr, fmt, x);
  fputc('\n', stderr);
  abort();
}

void bap_rt_unknown(uint64_t target) {
  fail("no code at %#lx, which the program jumps to", target);
}

void bap_rt_interrupt(uint64_t n) { fail("the interrupt %lu", n); }

void bap_rt_unsupported(uint64_t addr) {
  fail("the subroutine at %#lx wasn't recompiled", addr);
}

void bap_rt_intrinsic(const char *name) {
  fprintf(stderr, "bap-recompile: the intrinsic %s\n", name);
  abort();
}

static void read_at(int fd, void *dst, size_t size, off_t off) {
  if (pread(fd, dst, size, off) != (ssize_t)size)
    fail("can't read the image at %#lx", (uint64_t)off);
}

static void map_segments(int fd, const Elf64_Ehdr *eh, Elf64_Phdr *ph) {
  long page = sysconf(_SC_PAGESIZE);
  for (int i = 0; i < eh->e_phnum; i++) {
    if (ph[i].p_type != PT_LOAD)
      continue;
    uint64_t start = ph[i].p_vaddr & ~(uint64_t)(page - 1);
    uint64_t end = (ph[i].p_vaddr + ph[i].p_memsz + page - 1) & ~(uint64_t)(page - 1);
    void *mem = mmap((void *)start, end - start, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0);
    if (mem != (void *)start)
      fail("can't map the segment at %#lx", ph[i].p_vaddr);
    read_at(fd, (void *)ph[i].p_vaddr, ph[i].p_filesz, ph[i].p_offset);
  }
}

static void relocate(const Elf64_Rela *rel, size_t size, const Elf64_Sym *syms,
                     const char *strs) {
  for (size_t i = 0; i < size / sizeof(*rel); i++) {
    const Elf64_Sym *sym = &syms[ELF64_R_SYM(rel[i].r_info)];
    const char *name = strs + sym->st_name;
    void *where = (void *)rel[i].r_offset;
    void *value = *name ? dlsym(RTLD_DEFAULT, name) : NULL;
    switch (ELF64_R_TYPE(rel[i].r_info)) {
    case R_X86_64_COPY:
      if (!value)
        fail("can't find the data of the relocation at %#lx",
             rel[i].r_offset);
      memcpy(where, value, sym->st_size);
      break;
    case R_X86_64_GLOB_DAT:
    case R_X86_64_JUMP_SLOT:
      *(uint64_t *)where = (uint64_t)value;
      break;
    case R_X86_64_64:
      *(uint64_t *)where = (uint64_t)value + rel[i].r_addend;
      break;
    case R_X86_64_RELATIVE:
      *(uint64_t *)where = rel[i].r_addend;
      break;
    default:
      break;
    }
  }
}

static void apply_relocations(const Elf64_Ehdr *eh, const Elf64_Phdr *ph) {
  for (int i = 0; i < eh->e_phnum; i++) {
    if (ph[i].p_type != PT_DYNAMIC)
      continue;
    const Elf64_Rela *rela = NULL, *jmprel = NULL;
    const Elf64_Sym *syms = NULL;
    const char *strs = NULL;
    size_t relasz = 0, pltrelsz = 0;
    for (const Elf64_Dyn *d = (const Elf64_Dyn *)ph[i].p_vaddr;
         d->d_tag != DT_NULL; d++) {
      switch (d->d_tag) {
      case DT_RELA: rela = (const Elf64_Rela *)d->d_un.d_ptr; break;
      case DT_RELASZ: relasz = d->d_un.d_val; break;
      case DT_JMPREL: jmprel = (const Elf64_Rela *)d->d_un.d_ptr; break;
      case DT_PLTRELSZ: pltrelsz = d->d_un.d_val; break;
      case DT_SYMTAB: syms = (const Elf64_Sym *)d->d_un.d_ptr; break;
      case DT_STRTAB: strs = (const char *)d->d_un.d_ptr; break;
      }
    }
    if (rela)
      relocate(rela, relasz, syms, strs);
    if (jmprel)
      relocate(jmprel, pltrelsz, syms, strs);
  }
}

static void load_image(const char *path) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) {
    perror(path);
    exit(1);
  }
  Elf64_Ehdr eh;
  read_at(fd, &eh, sizeof(eh), 0);
  if (memcmp(eh.e_ident, ELFMAG, SELFMAG) || eh.e_type != ET_EXEC)
    fail("expected an executable of ELF, which isn't PIE, %lu", 0);
  Elf64_Phdr *ph = malloc(sizeof(*ph) * eh.e_phnum);
  read_at(fd, ph, sizeof(*ph) * eh.e_phnum, eh.e_phoff);
  map_segments(fd, &eh, ph);
  apply_relocations(&eh, ph);
  free(ph);
  close(fd);
}

int main(int argc, char **argv, char **envp) {
  const char *path = getenv("BAP_RECOMPILE_IMAGE");
  load_image(path ? path : bap_image_path);
  char *stack = mmap(NULL, STACK_SIZE, PROT_READ | PROT_WRITE,
                     MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (stack == MAP_FAILED)
    fail("can't map the stack of %lu bytes", STACK_SIZE);
  /* the return address of main, as the call left it, so that the stack
     is aligned, as the ABI expects at the entry of a function */
  uint64_t top = ((uint64_t)stack + STACK_SIZE) & ~(uint64_t)15;
  top -= 8;
  *(uint64_t *)top = MAGIC;
  bap_RSP = top;
  bap_RDI = (uint64_t)argc;
  bap_RSI = (uint64_t)argv;
  bap_RDX = (uint64_t)envp;
  bap_start(MAGIC);
  return (int)bap_RAX;
}
