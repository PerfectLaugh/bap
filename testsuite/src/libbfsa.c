// What the root of testLinuxLoaderOrder needs first, which needs libbfsc, whose `which` comes after that of libbfsb (loader.sh).
int bfs_a(void) { return 0; }
