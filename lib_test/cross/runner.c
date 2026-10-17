/* runner: executes instructions of a foreign architecture under QEMU user
   mode and prints their results, the counterpart of lib_test/x86/gen/runner.c
   for the architectures other than x86.

   Each input line is "CODE | INPUTS | OUTPUTS" or "CODE | INPUTS | OUTPUTS |
   LANDINGS", where CODE is the encoding in hex bytes, in memory order,
   INPUTS are NAME=VALUE bindings, OUTPUTS are names and LANDINGS are offsets
   from the instruction, at INSN_ADDR, where a branch may land, e.g.,
   -0x400. An architecture file that defines ALT_EPILOGUE has a second
   epilogue, in the other instruction set, e.g., T32 for A32, which is
   copied at the landings prefixed with *, e.g., *0x100, for the branches
   that change the instruction set. A name is a register of the architecture, see arch-*.h, or a
   flag, a bit of a register, e.g., of the condition register of PowerPC,
   M<n>@ADDR, the n-byte word at ADDR in the data region, in the byte order
   of the architecture, or PC, the address where the execution continued
   after the instruction. For each line, the runner prints "INPUTS |
   OUTPUTS" with the values of the outputs, or FAULT if the instruction
   raised a signal.

   The registers are loaded from the state by run_code, which jumps to the
   instruction with the stack pointer set to the state. The instruction is
   followed by a copy of the epilogue, as is each landing, which stores the
   registers in the state, relative to the stack pointer, and the address
   where it starts, and returns from run_code. So the instruction can't use
   the stack pointer. Each line runs in a child process, so that a fault
   doesn't stop the runner.

   The runner doesn't use the C library: the system calls are made by sys()
   of the architecture file, which also starts the program. */

#include ARCH_HEADER

typedef unsigned long long u64;
typedef unsigned char u8;

/* the instruction is at INSN_ADDR, in the middle of the code region, so
   that the branches can land before and after it */
#define CODE_ADDR 0x10000UL
#define CODE_SIZE 0x20000UL
#define INSN_ADDR 0x20000UL
#define DATA_ADDR 0x200000UL
#define DATA_SIZE 0x10000UL

long sys(long n, long a, long b, long c, long d, long e, long f);
void run_code(word *state);
extern u8 epi_start[], epi_mark[], epi_end[];
#ifdef ALT_EPILOGUE
/* the mark of the alternative epilogue is at the offset of epi_mark */
extern u8 alt_start[], alt_end[];
#endif

static word state[STATE_SIZE];

/* the compiler may call them for the loops */
void *memset(void *p, int c, unsigned long n) {
  volatile u8 *d = p;
  while (n--) *d++ = (u8)c;
  return p;
}

void *memcpy(void *dst, const void *src, unsigned long n) {
  volatile u8 *d = dst;
  const u8 *s = src;
  while (n--) *d++ = *s++;
  return dst;
}

/* output */

static char out[65536];
static int outlen;

static void flush(void) {
  int off = 0;
  while (off < outlen) {
    long n = sys(SYS_write, 1, (long)(out + off), outlen - off, 0, 0, 0);
    if (n <= 0) break;
    off += n;
  }
  outlen = 0;
}

static void puts_(const char *s) {
  while (*s) out[outlen++] = *s++;
}

static void putc_(char c) { out[outlen++] = c; }

static void die(const char *msg) {
  int n = 0;
  flush();
  while (msg[n]) n++;
  sys(SYS_write, 2, (long)msg, n, 0, 0, 0);
  sys(SYS_write, 2, (long)"\n", 1, 0, 0, 0);
  sys(SYS_exit_group, 1, 0, 0, 0, 0, 0);
}

/* strings */

static int streq(const char *a, const char *b) {
  while (*a && *a == *b) a++, b++;
  return *a == *b;
}

static int hexval(char c) {
  if (c >= '0' && c <= '9') return c - '0';
  if (c >= 'a' && c <= 'f') return c - 'a' + 10;
  if (c >= 'A' && c <= 'F') return c - 'A' + 10;
  return -1;
}

/* parses the number in s into the n little-endian bytes of b */
static void parse_value(const char *s, u8 *b, int n) {
  for (int i = 0; i < n; i++) b[i] = 0;
  if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) {
    int len = 0;
    s += 2;
    while (hexval(s[len]) >= 0) len++;
    for (int i = 0; i < len && i / 2 < n; i++) {
      int d = hexval(s[len - 1 - i]);
      b[i / 2] |= i % 2 ? d << 4 : d;
    }
  } else {
    u64 v = 0;
    while (*s >= '0' && *s <= '9') v = v * 10 + (*s++ - '0');
    for (int i = 0; i < n && i < 8; i++) b[i] = v >> (8 * i);
  }
}

static u64 parse_u64(const char *s) {
  u8 b[8];
  u64 v = 0;
  parse_value(s, b, 8);
  for (int i = 7; i >= 0; i--) v = v << 8 | b[i];
  return v;
}

/* prints the n little-endian bytes of b */
static void print_value(const u8 *b, int n) {
  static const char digits[] = "0123456789abcdef";
  int i = n - 1;
  while (i > 0 && b[i] == 0) i--;
  puts_("0x");
  if (b[i] >> 4) putc_(digits[b[i] >> 4]);
  putc_(digits[b[i] & 15]);
  for (i--; i >= 0; i--) {
    putc_(digits[b[i] >> 4]);
    putc_(digits[b[i] & 15]);
  }
}

static void print_u64(u64 v) {
  u8 b[8];
  for (int i = 0; i < 8; i++) b[i] = v >> (8 * i);
  print_value(b, 8);
}

/* locations */

static const struct reg *find_reg(const char *name) {
  for (unsigned i = 0; i < sizeof regs / sizeof regs[0]; i++)
    if (streq(name, regs[i].name)) return &regs[i];
  return 0;
}

/* M<n>@ADDR */
static int parse_mem(const char *name, int *n, u8 **addr) {
  if (name[0] != 'M') return 0;
  name++;
  *n = 0;
  while (*name >= '0' && *name <= '9') *n = *n * 10 + (*name++ - '0');
  if (*name++ != '@') return 0;
  *addr = (u8 *)(unsigned long)parse_u64(name);
  return 1;
}

/* the byte i of an n-byte word in the byte order of the architecture */
static int byte_index(int n, int i) { return BIG_ENDIAN_ARCH ? n - 1 - i : i; }

static void set(const char *name, const char *value) {
  const struct reg *r = find_reg(name);
  int n;
  u8 *addr, b[64];
  if (r && r->bit) {
    word m = (word)1 << (r->bit - 1);
    state[r->slot] = parse_u64(value) ? state[r->slot] | m : state[r->slot] & ~m;
  } else if (r) {
    u8 *slot = (u8 *)&state[r->slot];
    parse_value(value, b, r->size);
    for (int i = 0; i < r->size; i++) slot[byte_index(r->size, i)] = b[i];
  } else if (parse_mem(name, &n, &addr)) {
    parse_value(value, b, n);
    for (int i = 0; i < n; i++) addr[byte_index(n, i)] = b[i];
  } else {
    puts_("unknown location ");
    die(name);
  }
}

static void get(const char *name) {
  const struct reg *r = find_reg(name);
  int n;
  u8 *addr, b[64];
  if (r && r->bit) {
    print_u64(state[r->slot] >> (r->bit - 1) & 1);
  } else if (r) {
    u8 *slot = (u8 *)&state[r->slot];
    for (int i = 0; i < r->size; i++) b[i] = slot[byte_index(r->size, i)];
    print_value(b, r->size);
  } else if (streq(name, "PC")) {
    print_u64((u64)state[SLOT_LAND] - (u64)(epi_mark - epi_start));
  } else if (parse_mem(name, &n, &addr)) {
    for (int i = 0; i < n; i++) b[i] = addr[byte_index(n, i)];
    print_value(b, n);
  } else {
    puts_("unknown location ");
    die(name);
  }
}

/* input */

static char in[65536];
static int inlen, inpos;

static int getline_(char *line, int max) {
  int n = 0;
  for (;;) {
    if (inpos == inlen) {
      inlen = sys(SYS_read, 0, (long)in, sizeof in, 0, 0, 0);
      inpos = 0;
      if (inlen <= 0) {
        inlen = 0;
        line[n] = 0;
        return n > 0;
      }
    }
    char c = in[inpos++];
    if (c == '\n') break;
    if (n < max - 1) line[n++] = c;
  }
  line[n] = 0;
  return 1;
}

/* splits s at the separator c, returns the rest or 0 */
static char *split(char *s, char c) {
  while (*s && *s != c) s++;
  if (!*s) return 0;
  *s = 0;
  return s + 1;
}

static char *skip_spaces(char *s) {
  while (*s == ' ') s++;
  return s;
}

/* the next space-separated token of *s, or 0 */
static char *token(char **s) {
  char *t = skip_spaces(*s);
  if (!*t) return 0;
  char *e = t;
  while (*e && *e != ' ') e++;
  if (*e) *e++ = 0;
  *s = e;
  return t;
}

static void copy(u8 *dst, const u8 *src, long n) {
  for (long i = 0; i < n; i++) dst[i] = src[i];
}

/* copies the epilogue from start to end at the offset off from the
   instruction, which must not overlap the instruction or the other copies */
static void place(u8 *start, u8 *end, u8 *insn, long off, long placed[][2],
                  long *n) {
  long epi = end - start;
  u8 *at = insn + off;
  if (at < (u8 *)CODE_ADDR || at + epi > (u8 *)(CODE_ADDR + CODE_SIZE))
    die("the landing is out of the code region");
  for (long i = 0; i < *n; i++)
    if (off < placed[i][1] && placed[i][0] < off + epi)
      die("the landing overlaps the instruction or another landing");
  if (*n == 64) die("too many landings");
  placed[*n][0] = off;
  placed[(*n)++][1] = off + epi;
  copy(at, start, epi);
}

static void run_line(char *line) {
  char *inputs = split(line, '|');
  char *outputs = inputs ? split(inputs, '|') : 0;
  char *landings = outputs ? split(outputs, '|') : 0;
  u8 *code = (u8 *)CODE_ADDR, *insn = (u8 *)INSN_ADDR;
  long placed[64][2], nplaced = 0;
  long len = 0;
  char *t, *s;

  if (!outputs) die("bad line");
  for (long i = 0; i < CODE_SIZE; i++) code[i] = 0;
  /* the bytes are in hex without a prefix */
  s = line;
  while ((t = token(&s))) {
    if (hexval(t[0]) < 0 || hexval(t[1]) < 0 || t[2]) die("bad code byte");
    insn[len++] = hexval(t[0]) << 4 | hexval(t[1]);
  }
  placed[nplaced][0] = 0;
  placed[nplaced++][1] = len;
  place(epi_start, epi_end, insn, len, placed, &nplaced);
  while (landings && (t = token(&landings))) {
    u8 *start = epi_start, *end = epi_end;
    if (t[0] == '*') {
#ifdef ALT_EPILOGUE
      start = alt_start, end = alt_end, t++;
#else
      die("the architecture has no alternative epilogue");
#endif
    }
    long off = t[0] == '-' ? -(long)parse_u64(t + 1) : (long)parse_u64(t);
    place(start, end, insn, off, placed, &nplaced);
  }
  flush_icache(code, CODE_SIZE);

  long pid = sys_fork();
  if (pid < 0) die("fork");
  if (pid == 0) {
    for (int i = 0; i < STATE_SIZE; i++) state[i] = 0;
    initialize_state(state);
    state[SLOT_CODE] = (word)INSN_ADDR;
    /* the inputs are printed back, the tokens are taken from a copy */
    static char copy_of_inputs[65536];
    int k = 0;
    while ((copy_of_inputs[k] = inputs[k])) k++;
    char *u = copy_of_inputs;
    while ((t = token(&u))) {
      char *v = split(t, '=');
      if (!v) die("expected NAME=VALUE");
      set(t, v);
    }
    run_code(state);
    /* the inputs are printed back without the surrounding spaces */
    char *p = skip_spaces(inputs);
    int n = 0;
    while (p[n]) n++;
    while (n > 0 && p[n - 1] == ' ') n--;
    p[n] = 0;
    puts_(p);
    puts_(" |");
    while ((t = token(&outputs))) {
      putc_(' ');
      puts_(t);
      putc_('=');
      get(t);
    }
    putc_('\n');
    flush();
    sys(SYS_exit_group, 0, 0, 0, 0, 0, 0);
  }
  int status = 0;
  sys_wait(pid, &status);
  if ((status & 0x7f) != 0) {
    puts_("FAULT\n");
    flush();
  }
}

int main(void) {
  static char line[65536];
  long code = sys(SYS_mmap, CODE_ADDR, CODE_SIZE, 7, MAP_PRIVATE_ANON_FIXED,
                  -1, 0);
  long data = sys(SYS_mmap, DATA_ADDR, DATA_SIZE, 3, MAP_PRIVATE_ANON_FIXED,
                  -1, 0);
  if (code != (long)CODE_ADDR || data != (long)DATA_ADDR) die("mmap");
  while (getline_(line, sizeof line)) {
    if (!line[0]) continue;
    run_line(line);
  }
  flush();
  return 0;
}
