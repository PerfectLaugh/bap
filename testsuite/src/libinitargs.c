/* What an initializer is given, as glibc's `call_init` gives it: the count of the arguments of the program, their addresses and those of
   its environment (testLinuxLibraries):
     clang --target=aarch64-linux-musl -shared -fPIC -nostdlib -O1 -fuse-ld=lld libinitargs.c -o libinitargs.so */
static int seenCount = -1;
static char **seenArguments;
static char **seenEnvironment;
__attribute__((constructor)) static void initialize(int count, char **arguments, char **environment) {
  seenCount = count;
  seenArguments = arguments;
  seenEnvironment = environment;
}
int init_count(void) { return seenCount; }
int init_second_letter(void) { return seenArguments ? seenArguments[1][0] : -1; }
int init_environment_ends(void) { return seenEnvironment && seenArguments[seenCount] == 0 && seenEnvironment == seenArguments + seenCount + 1; }
