/* Functions of Thumb, for Bap.Linux.Library: the value of each of their symbols has bit 0, which says so.
     clang --target=arm-linux-musleabihf -mthumb -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libthumb.so libthumb.c -o libthumb.so */
static int hidden_twice(int value) { return value * 2; }
int thumb_twice(int value) { return hidden_twice(value) + 1; }
int (*thumb_hidden(void))(int) { return hidden_twice; }
