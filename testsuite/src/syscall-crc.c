/* Computes the CRC of 100 bytes and prints it, 1489580789, with the write
   system call of Linux on x86-64, instead of the functions of libc:

   gcc -O1 -fno-builtin -DITERATIONS=100 syscall-crc.c \
     -o ../bin/x86_64-linux-gnu-syscall-crc */

static long sys_write(long fd, const char *buf, long len) {
    long r;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(1L), "D"(fd), "S"(buf), "d"(len)
                     : "rcx", "r11", "memory");
    return r;
}

int main(void) {
    unsigned crc = 0xFFFFFFFF;
    for (unsigned i = 0; i < ITERATIONS; i++) {
        crc ^= i & 0xff;
        for (int j = 0; j < 8; j++)
            crc = (crc >> 1) ^ (0xEDB88320 & -(crc & 1));
    }
    char buf[16];
    int n = sizeof(buf);
    buf[--n] = '\n';
    unsigned x = ~crc;
    do {
        buf[--n] = '0' + x % 10;
        x /= 10;
    } while (x);
    return sys_write(1, buf + n, sizeof(buf) - n) < 0;
}
