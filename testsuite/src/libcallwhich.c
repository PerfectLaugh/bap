// What calls `which` of what it needs, as the loader bound it (loader.sh, testLinuxLoaderOrder).
int which(void);
int call_which(void) { return which(); }
