/* runner: executes x86 instructions natively and prints their results.

   Each input line is "CODE | INPUTS | OUTPUTS", where CODE is the encoding
   in hex bytes, INPUTS are NAME=VALUE bindings and OUTPUTS are names. A
   name is a general purpose register, XMM<n>, a flag (CF, PF, AF, ZF, SF,
   DF, OF), or M<n>@ADDR, the n-byte little-endian word at ADDR in the data
   region. The instruction runs at CODE_ADDR. For each line, the runner
   prints "INPUTS | OUTPUTS" with the values of the outputs, or FAULT if the
   instruction raised a signal. */
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>

#define CODE_ADDR 0x10000
#define DATA_ADDR 0x200000
#define DATA_SIZE 0x10000
#define DEFAULT_SP 0x208000

#ifdef __x86_64__
#define NGPR 16
#define NXMM 16
typedef uint64_t reg;
static const char *gprs[NGPR] = {"RAX", "RCX", "RDX", "RBX", "RSP", "RBP",
                                 "RSI", "RDI", "R8",  "R9",  "R10", "R11",
                                 "R12", "R13", "R14", "R15"};
struct state {
  reg gpr[NGPR];
  reg flags;
  reg pad;
  uint8_t xmm[NXMM][16];
};
#else
#define NGPR 8
#define NXMM 8
typedef uint32_t reg;
static const char *gprs[NGPR] = {"EAX", "ECX", "EDX", "EBX",
                                 "ESP", "EBP", "ESI", "EDI"};
struct state {
  reg gpr[NGPR];
  reg flags;
  reg pad[3];
  uint8_t xmm[NXMM][16];
};
#endif
#define SP 4

static const struct {
  const char *name;
  int bit;
} flags[] = {{"CF", 0}, {"PF", 2}, {"AF", 4},  {"ZF", 6},
             {"SF", 7}, {"DF", 10}, {"OF", 11}};
#define NFLAGS (sizeof flags / sizeof flags[0])

void run_code(struct state *, void *);
extern char run_back[];

static sigjmp_buf fault;
static void on_fault(int sig) { siglongjmp(fault, sig); }

static uint8_t hexval(char c) {
  return c <= '9' ? c - '0' : (c | 0x20) - 'a' + 10;
}

/* parses the number in s into the little-endian bytes of b */
static void parse_value(const char *s, uint8_t *b, int n) {
  memset(b, 0, n);
  if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
    size_t len = strlen(s + 2);
    for (size_t i = 0; i < len && (int)(i / 2) < n; i++) {
      uint8_t d = hexval(s[2 + len - 1 - i]);
      b[i / 2] |= i % 2 ? d << 4 : d;
    }
  } else {
    unsigned long long v = strtoull(s, 0, 10);
    for (int i = 0; i < n && i < 8; i++) b[i] = v >> (8 * i);
  }
}

static void print_value(const uint8_t *b, int n) {
  int i = n - 1;
  while (i > 0 && b[i] == 0) i--;
  printf("0x%x", b[i]);
  for (i--; i >= 0; i--) printf("%02x", b[i]);
}

static int gpr_index(const char *name) {
  for (int i = 0; i < NGPR; i++)
    if (!strcmp(name, gprs[i])) return i;
  return -1;
}

static int flag_index(const char *name) {
  for (unsigned i = 0; i < NFLAGS; i++)
    if (!strcmp(name, flags[i].name)) return i;
  return -1;
}

static void unknown(const char *name) {
  fprintf(stderr, "unknown location %s\n", name);
  exit(1);
}

static void set(struct state *s, char *name, const char *value) {
  int i, n;
  unsigned long addr;
  if ((i = gpr_index(name)) >= 0)
    parse_value(value, (uint8_t *)&s->gpr[i], sizeof(reg));
  else if ((i = flag_index(name)) >= 0) {
    if (strtoul(value, 0, 0)) s->flags |= (reg)1 << flags[i].bit;
  } else if (sscanf(name, "XMM%d", &i) == 1 && i < NXMM)
    parse_value(value, s->xmm[i], 16);
  else if (sscanf(name, "M%d@%li", &n, &addr) == 2)
    parse_value(value, (uint8_t *)addr, n);
  else
    unknown(name);
}

static void get(const struct state *s, const char *name) {
  int i, n;
  unsigned long addr;
  if ((i = gpr_index(name)) >= 0)
    print_value((const uint8_t *)&s->gpr[i], sizeof(reg));
  else if ((i = flag_index(name)) >= 0)
    printf("%d", (int)((s->flags >> flags[i].bit) & 1));
  else if (sscanf(name, "XMM%d", &i) == 1 && i < NXMM)
    print_value(s->xmm[i], 16);
  else if (sscanf(name, "M%d@%li", &n, &addr) == 2)
    print_value((const uint8_t *)addr, n);
  else
    unknown(name);
}

int main(void) {
  uint8_t *code = mmap((void *)CODE_ADDR, 0x1000, PROT_READ | PROT_WRITE | PROT_EXEC,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
  uint8_t *data = mmap((void *)DATA_ADDR, DATA_SIZE, PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
  if (code == MAP_FAILED || data == MAP_FAILED) {
    perror("mmap");
    return 1;
  }
  static uint8_t altstack[65536];
  stack_t ss = {.ss_sp = altstack, .ss_size = sizeof altstack};
  sigaltstack(&ss, 0);
  struct sigaction sa = {.sa_handler = on_fault, .sa_flags = SA_ONSTACK | SA_NODEFER};
  sigaction(SIGFPE, &sa, 0);
  sigaction(SIGSEGV, &sa, 0);
  sigaction(SIGBUS, &sa, 0);
  sigaction(SIGILL, &sa, 0);
  sigaction(SIGTRAP, &sa, 0);

  char line[65536];
  while (fgets(line, sizeof line, stdin)) {
    line[strcspn(line, "\n")] = 0;
    char *bar1 = strchr(line, '|'), *bar2 = bar1 ? strchr(bar1 + 1, '|') : 0;
    if (!bar2) {
      fprintf(stderr, "bad line: %s\n", line);
      return 1;
    }
    *bar1 = *bar2 = 0;
    char *inputs = bar1 + 1, *outputs = bar2 + 1;

    /* the code is followed by a jump back to the trampoline */
    int len = 0;
    for (char *t = strtok(line, " "); t; t = strtok(0, " "))
      code[len++] = strtoul(t, 0, 16);
    int32_t rel = (int32_t)((uintptr_t)run_back - (uintptr_t)(code + len + 5));
    code[len] = 0xe9;
    memcpy(code + len + 1, &rel, 4);
    __builtin___clear_cache((char *)code, (char *)code + len + 5);

    struct state s;
    memset(&s, 0, sizeof s);
    memset(data, 0, DATA_SIZE);
    s.flags = 0x202;
    s.gpr[SP] = DEFAULT_SP;
    char copy[65536];
    strcpy(copy, inputs);
    for (char *t = strtok(copy, " "); t; t = strtok(0, " ")) {
      char *eq = strchr(t, '=');
      if (!eq) unknown(t);
      *eq = 0;
      set(&s, t, eq + 1);
    }

    if (sigsetjmp(fault, 1)) {
      printf("FAULT\n");
      continue;
    }
    run_code(&s, code);

    /* the inputs are printed back without the trailing spaces */
    char *end = inputs + strlen(inputs);
    while (end > inputs && end[-1] == ' ') *--end = 0;
    while (*inputs == ' ') inputs++;
    printf("%s |", inputs);
    for (char *t = strtok(outputs, " "); t; t = strtok(0, " ")) {
      printf(" %s=", t);
      get(&s, t);
    }
    printf("\n");
  }
  return 0;
}
