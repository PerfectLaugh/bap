/* Of what Bap.Analysis.Partition finds of a program without running it: jump tables of switches, of a range from 0, of one
   that doesn't start at 0, and of bytes; a function that never returns, and one that only calls it; a thunk; a tail call; and tail calls of tail calls. It
   is never run: _start doesn't end. Each is built freestanding, see BapTests/Partition.lean, e.g.

     clang --target=x86_64-linux-gnu -O2 -ffreestanding -fno-builtin -nostdlib -static -fuse-ld=lld -fno-pic -no-pie \
       -Wl,-e,_start partition.c -o ../bin/x86_64-linux-none-partition

   and of i686-linux-gnu, aarch64-linux-gnu, riscv64-linux-gnu, armv7a-linux-gnueabihf (arm, and thumb with -mthumb),
   mips-linux-gnu, mipsel-linux-gnu and mips64el-linux-gnuabi64 (with -mno-abicalls), powerpc-linux-gnu and powerpc64le-linux-gnu,
   each as ../bin/ARCH-linux-none-partition. */

volatile int sink;

__attribute__((noinline)) int dense(int x) {
  switch (x) {
  case 0: return sink + 11;
  case 1: return sink * 3;
  case 2: return sink - 7;
  case 3: return sink ^ 5;
  case 4: return sink + 1000;
  case 5: return sink << 2;
  case 6: return sink >> 1;
  case 7: return sink | 64;
  case 8: return sink & 15;
  case 9: return -sink;
  default: return 0;
  }
}

__attribute__((noinline)) int offset(int x) {
  switch (x) {
  case 100: sink = 1; break;
  case 101: sink = 22; break;
  case 102: sink = 333; break;
  case 103: sink = 4444; break;
  case 104: sink = 55555; break;
  case 105: sink = 666666; break;
  case 106: sink = 7777777; break;
  case 107: sink = 88; break;
  case 109: sink = 99; break;
  default: sink = -1; break;
  }
  return sink;
}

__attribute__((noinline)) int letters(unsigned char c) {
  switch (c) {
  case 'a': return sink + 'a';
  case 'b': return sink * 'b';
  case 'c': return sink - 'c';
  case 'd': return sink ^ 'd';
  case 'e': return sink + 'e' * 3;
  case 'f': return sink | 'f';
  case 'g': return sink & 'g';
  case 'h': return sink % 7;
  default: return -2;
  }
}

__attribute__((noinline, noreturn)) void die(int code) {
  sink = code;
  __builtin_trap();
}

__attribute__((noinline, noreturn)) void fail(void) {
  die(3);
}

__attribute__((noinline)) int target(int x) { return x * sink + 1; }

__attribute__((noinline)) int thunk(int x) { return target(x); }

__attribute__((noinline)) int tail(int x) {
  sink = x;
  return target(x + 2);
}

/* Tail calls of what itself only calls in its tail: each returns, as the last of them does, and what calls the first goes on */
__attribute__((noinline)) int chainLeaf(int x) {
  sink = x;
  return x + 1;
}

__attribute__((noinline)) int chainMid(int x) { return chainLeaf(x ^ 5); }

__attribute__((noinline)) int chainTop(int x) { return chainMid(x + 3); }

__attribute__((noinline)) int chainUser(int x) {
  int result = chainTop(x);
  sink = result;
  return result * 3;
}

void _start(void) {
  int total = 0;
  for (int i = 0; i < 120; i++) total += dense(i) + offset(i) + letters((unsigned char)i) + thunk(i) + tail(i) + chainUser(i);
  if (total == 12345) fail();
  sink = total;
  for (;;) {
  }
}
