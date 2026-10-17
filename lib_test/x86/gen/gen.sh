#!/bin/bash
# gen.sh BITS SPEC SUITE: prints the OCaml tests for the instructions in SPEC,
# with the expected values computed by executing them natively.
#
# Each line of SPEC is "ASM | INPUTS | OUTPUTS", ASM is in the Intel syntax.
# An input is NAME=VALUE, a fixed value, NAME, which takes each value of the
# set of its kind (a general purpose register, a flag or XMM<n>), or NAME@SET,
# which takes each value of SET. The vectors are all the combinations of the
# values of the inputs, the vectors where the instruction faults are dropped.
# An output is a location whose value is compared, see the runner. Lines
# starting with # are section comments.
#
# The instructions are assembled with GNU as and executed by the runner,
# built with gcc, BITS=32 needs the 32-bit C library (gcc -m32).
bits=$1 spec=$2 suite=$3
dir=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d)
trap 'rm -rf $W' EXIT
run=$W/run
if [ $bits = 64 ]; then
  gcc -O2 -static -o $run $dir/runner.c $dir/tramp64.S
else
  gcc -m32 -O2 -no-pie -o $run $dir/runner.c $dir/tramp32.S
fi || { echo "ERROR building the runner" >&2; exit 1; }

if [ $bits = 64 ]; then
  gpr="0 1 0x7f 0x80 0x7fffffff 0x80000000 0xffffffff 0x7fffffffffffffff 0x8000000000000000 0xffffffffffffffff 0x123456789abcdef0 0xfedcba9876543210"
  gpr2="0 1 0x80 0x7fffffff 0x80000000 0xffffffffffffffff 0x8000000000000000 0x123456789abcdef0"
  sp=RSP mode=x86_64
else
  gpr="0 1 0x7f 0x80 0x7fff 0x8000 0x7fffffff 0x80000000 0xffffffff 0x12345678 0xfedcba98"
  gpr2="0 1 0x80 0x7fff 0x80000000 0xffffffff 0x7fffffff 0x12345678"
  sp=ESP mode=i686
fi
declare -A sets=(
  [count]="0 1 7 8 15 16 31 32 33 63 64 0xff"
  [bool]="0 1"
  [xmm]="0 0x3ff0000000000000 0x40000000000000003ff8000000000000 0xc0040000000000007ff0000000000000 0x7ff8000000000000fff0000000000000 0x80000000000000000000000000000001 0x3f800000c02000007f8000003fc00000 0x0123456789abcdeffedcba9876543210 0x7fc00000ff800000000000004f000000 0x4004000000000000bff8000000000000 0xbfe0000000000000c004000000000000 0x40200000c02000003f000000bfc00000"
  [byte]="0 1 0x7f 0x80 0xff"
  [nz]="1 0x80 0x7fffffff 0x80000000 0xffffffff 0x8000000000000000 0xffffffffffffffff 0x123456789abcdef0 0x10"
  [nz32]="1 0x80 0x7fff 0x8000 0x80000000 0xffffffff 0x12345678 0x10"
  [vec]="0 0xffffffffffffffffffffffffffffffff 0x0123456789abcdeffedcba9876543210 0x80007fff00010000ffff800000ff7f01 0x7f80017fff00fe81807f7f8001ff0080"
  [mxcsr]="0x1f80 0x3f80 0x5f80 0x7f80"
)

kind() {
  case $1 in
    CF|PF|AF|ZF|SF|DF|OF) echo bool ;;
    XMM*) echo xmm ;;
    *) echo gpr ;;
  esac
}

# prints the input lines of the combinations of the values of the inputs
expand() {
  local fixed="" names=() ss=() t n s nvar=0
  for t in $1; do
    case $t in
      *=*) fixed="$fixed $t" ;;
      *@*) if [ -n "${sets[${t##*@}]}" ]; then names+=("${t%@*}"); ss+=("${sets[${t##*@}]}")
           else names+=("$t"); ss+=("@gpr"); nvar=$((nvar + 1)); fi ;;
      *) names+=("$t"); k=$(kind $t); [ $k = gpr ] && nvar=$((nvar + 1))
         if [ $k = gpr ]; then ss+=("@gpr"); else ss+=("${sets[$k]}"); fi ;;
    esac
  done
  local i
  for i in "${!ss[@]}"; do
    if [ "${ss[$i]}" = "@gpr" ]; then
      if [ $nvar -ge 2 ]; then ss[$i]=$gpr2; else ss[$i]=$gpr; fi
    fi
  done
  combine "$fixed" 0
}

combine() {
  local acc=$1 i=$2 v
  if [ $i -ge ${#names[@]} ]; then echo "$acc"; return; fi
  for v in ${ss[$i]}; do combine "$acc ${names[$i]}=$v" $((i + 1)); done
}

assemble() {
  printf '.intel_syntax noprefix\n.text\n%s\n' "$1" > $W/a.s
  as --$bits $W/a.s -o $W/a.o 2> $W/err || { echo "ERROR assembling '$1': $(cat $W/err)" >&2; exit 1; }
  objcopy -O binary --only-section=.text $W/a.o $W/a.bin
  od -An -tx1 -v $W/a.bin | tr -s ' \n' ' ' | sed 's/^ //; s/ $//'
}

# the BAP names of the locations, the XMM registers are the low halves of
# the YMM registers
bap_names() { sed -E 's/\bXMM([0-9]+)=/YMM\1=/g'; }

echo "(* generated from gen/$(basename $spec) by gen/gen.sh *)"
echo
echo "let mode = X86_tests_helpers.$mode"
echo
echo "let suite ="
echo "  OUnit2.( >::: ) \"$suite\""
echo "    ["
while IFS='|' read -r asm inputs outputs; do
  asm=$(echo "$asm" | sed 's/^ *//; s/ *$//')
  [ -z "$asm" ] && continue
  if [[ "$asm" == \#* ]]; then echo "      (* ${asm#\# } *)"; continue; fi
  code=$(assemble "$asm") || exit 1
  case " $inputs " in *" $sp"[=@\ ]*) ;; *) inputs="$sp=0x208000 $inputs" ;; esac
  expand "$inputs" | sed "s/^/$code |/; s/\$/ | $outputs/" > $W/in
  $run < $W/in > $W/out || { echo "ERROR running '$asm'" >&2; exit 1; }
  # the instructions that fault for all inputs, e.g., those that the
  # processor does not implement, are skipped
  if ! grep -qv '^FAULT$' $W/out; then
    echo "warning: skipping '$asm', it faults for all inputs" >&2
    continue
  fi
  echo "      Lifter_test.case mode \"$asm\" \"$code\""
  echo "        (Lifter_test.vectors"
  echo "           {|"
  grep -v '^FAULT$' $W/out | bap_names
  echo "|});"
done < $spec
echo "    ]"
