/* Returns 3 * argc + 7, twice, through the locals on the stack, and
   computes the noise, which doesn't flow to the result, so that the
   backward slice of the result, at the return of main, has the
   instructions, that compute it, and not the ones of the noise:

   gcc -O0 -no-pie -fcf-protection=none slice.c -o ../bin/x86_64-linux-gnu-slice */

int noise_sink;

int main(int argc, char **argv) {
    int a = argc * 3;
    int noise = argc + 100;
    int b = 7;
    int buf[4];
    buf[1] = a + b;
    noise_sink = noise * 5;
    int c = buf[1] * 2;
    return c;
}
