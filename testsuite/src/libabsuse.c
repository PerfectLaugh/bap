// What refers to `magic` of libabs, which is 0x1234 wherever libabs is (loader.sh, testLinuxLoaderOrder).
extern char magic[];
char *magic_pointer = magic;
unsigned long where_magic(void) { return (unsigned long)magic_pointer; }
