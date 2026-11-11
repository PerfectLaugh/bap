// What Linux does with what execve runs that a fifth review found the machine didn't:
//   script: the first line of a script is split by spaces and tabs, as load_script has it: the name is after them, to the next of them,
//     and all of the rest of the line, without them at either end, is one argument, tabs within it too.
//   interp: a program whose interpreter is of another class or machine is ELIBBAD, as load_elf_binary has it.
// Each in a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#if defined(__x86_64__)
#define MACHINE EM_X86_64
#elif defined(__aarch64__)
#define MACHINE EM_AARCH64
#endif

static void write_file(const char *path, const void *data, size_t size) {
  int fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0755);
  write(fd, data, size);
  close(fd);
}

// What it is run as by its script: it says its arguments, one to a line, with tabs as \t.
static int said(int count, char **arguments) {
  for (int index = 1; index < count; index++) {
    printf("  [");
    for (char *at = arguments[index]; *at; at++) printf(*at == '\t' ? "\\t" : "%c", *at);
    printf("]\n");
  }
  return 0;
}

static void run(const char *path) {
  pid_t child = fork();
  if (child == 0) {
    char *arguments[] = {(char *)path, "last", 0};
    execv(path, arguments);
    printf("  execve errno %d\n", errno);
    _exit(0);
  }
  waitpid(child, 0, 0);
}

static const char *self;

static void script(void) {
  char text[4096];
  snprintf(text, sizeof text, "#! \t%s\t first\targ \t \nnothing\n", self);
  write_file("script", text, strlen(text));
  printf("script:\n");
  run("./script");
}

static void interp(void) {
  // The interpreter: a header of ELF of 32 bits of i386, in a page, as what is shorter than a header that Linux reads is EIO.
  static unsigned char page[4096];
  Elf32_Ehdr small = {0};
  memcpy(small.e_ident, ELFMAG, SELFMAG);
  small.e_ident[EI_CLASS] = ELFCLASS32;
  small.e_ident[EI_DATA] = ELFDATA2LSB;
  small.e_ident[EI_VERSION] = EV_CURRENT;
  small.e_type = ET_DYN;
  small.e_machine = EM_386;
  small.e_version = EV_CURRENT;
  small.e_ehsize = sizeof small;
  small.e_phentsize = sizeof(Elf32_Phdr);
  memcpy(page, &small, sizeof small);
  write_file("ld32", page, sizeof page);
  // The program, of this machine, of a segment of one page, which never runs.
  static const char name[] = "./ld32";
  unsigned char image[0x2000] = {0};
  Elf64_Ehdr *header = (void *)image;
  memcpy(header->e_ident, ELFMAG, SELFMAG);
  header->e_ident[EI_CLASS] = ELFCLASS64;
  header->e_ident[EI_DATA] = ELFDATA2LSB;
  header->e_ident[EI_VERSION] = EV_CURRENT;
  header->e_type = ET_EXEC;
  header->e_machine = MACHINE;
  header->e_version = EV_CURRENT;
  header->e_entry = 0x400000;
  header->e_phoff = sizeof *header;
  header->e_ehsize = sizeof *header;
  header->e_phentsize = sizeof(Elf64_Phdr);
  header->e_phnum = 2;
  Elf64_Phdr *headers = (void *)(image + sizeof *header);
  size_t at = sizeof *header + 2 * sizeof(Elf64_Phdr);
  memcpy(image + at, name, sizeof name);
  headers[0] = (Elf64_Phdr){PT_INTERP, PF_R, at, 0, 0, sizeof name, sizeof name, 1};
  headers[1] = (Elf64_Phdr){PT_LOAD, PF_R | PF_X, 0x1000, 0x400000, 0x400000, 0x1000, 0x1000, 0x1000};
  write_file("program", image, sizeof image);
  printf("interp: of 32 bits of i386:\n");
  run("./program");
  // And one that isn't of ELF.
  memset(page, 'x', sizeof page);
  write_file("ld32", page, sizeof page);
  printf("interp: of what isn't ELF:\n");
  run("./program");
}

int main(int count, char **arguments) {
  setvbuf(stdout, 0, _IONBF, 0);
  if (count > 1) return said(count, arguments);
  // Its own path, from the directory that it works in.
  static char path[4096];
  snprintf(path, sizeof path, arguments[0][0] == '/' ? "%s" : "../%s", arguments[0]);
  self = path;
  mkdir("r18-work", 0755);
  chdir("r18-work");
  script();
  interp();
  unlink("script");
  unlink("ld32");
  unlink("program");
  chdir("..");
  rmdir("r18-work");
  printf("done\n");
  return 0;
}
