
all: echo symexec

.PHONY: echo echo-32 symexec cff ollvm
echo: echo.c
		sh build.sh echo.c
		x86_64-linux-gnu-gcc -m32 -w echo.c  -o ../bin/x86-linux-gnu-echo

symexec: symexec-*.c
	sh build.sh $?

# the flattened control flow, whose state is on the stack, as the code
# isn't optimized, see the deflattening of the recompile plugin
cff: cff.c
	x86_64-linux-gnu-gcc -O0 -g -w -no-pie -fno-pie -fcf-protection=none cff.c -o ../bin/x86_64-linux-gnu-cff

# the control flow, that Obfuscator-LLVM flattens, see ollvm/build.sh
ollvm: ollvm/collatz.c ollvm/flattening.cpp
	sh ollvm/build.sh
