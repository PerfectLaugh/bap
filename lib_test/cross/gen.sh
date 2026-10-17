#!/bin/bash
# gen.sh CONFIG SPEC SUITE: prints the OCaml tests for the instructions in
# SPEC, with the expected values computed by executing them under QEMU user
# mode with runner.c.
#
# CONFIG is a shell file that describes the architecture, it sets
#   cc_target    the clang target of the runner, e.g., mips-linux-gnu
#   cc_flags     the additional flags of clang
#   arch         the name of the files arch-$arch.h and arch-$arch.S
#   qemu         the QEMU user mode emulator, e.g., qemu-mips
#   qemu_cpu     the processor that QEMU emulates
#   mc_triple    the llvm-mc triple that assembles the instructions
#   mc_flags     the additional flags of llvm-mc, e.g., -mcpu=mips32r2
#   prelude      the assembler directives that precede an instruction
#   mode         the mode of the tests in the helpers of the suite
#   helpers      the module of the helpers of the suite
#   gpr, gpr2    the values of the general purpose registers, when there are
#                fewer or more than one of them in the inputs
#   drop         the outputs that are not compared, e.g., the flags that the
#                processor doesn't have
#   sets         an associative array of the other sets of values
# and defines the function kind, that maps a register name to the name of
# its set of values, gpr for the general purpose registers.
#
# Each line of SPEC is "ASM | INPUTS | OUTPUTS" or "ASM | INPUTS | OUTPUTS |
# LANDINGS", see runner.c for the locations and the landings. An input is
# NAME=VALUE, a fixed value, NAME, which takes each value of the set of its
# kind, or NAME@SET, which takes each value of SET. The vectors are all the
# combinations of the values of the inputs, the vectors where the
# instruction faults are dropped. Lines starting with # are section
# comments.
#
# The runner is built with clang and lld, and the instructions are assembled
# with llvm-mc.
config=$1 spec=$2 suite=$3
dir=$(cd "$(dirname "$0")" && pwd)
W=$(mktemp -d)
trap 'rm -rf $W' EXIT
declare -A sets
cc_flags="" mc_flags="" prelude="" qemu_cpu="" drop=""
. "$config" || exit 1

run=$W/run
clang --target=$cc_target -ffreestanding -nostdlib -static -fno-pic -O2 \
  $cc_flags -DARCH_HEADER="\"arch-$arch.h\"" -I"$dir" \
  "$dir/runner.c" "$dir/arch-$arch.S" -fuse-ld=lld \
  -Wl,--image-base=0x1000000 -o $run ||
  { echo "ERROR building the runner" >&2; exit 1; }

# prints the input lines of the combinations of the values of the inputs
expand() {
  local fixed="" names=() ss=() t k nvar=0
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
  printf '%s\n.text\n%s\n' "$prelude" "$1" > $W/a.s
  llvm-mc --triple=$mc_triple $mc_flags -filetype=obj $W/a.s -o $W/a.o 2> $W/err ||
    { echo "ERROR assembling '$1': $(cat $W/err)" >&2; exit 1; }
  llvm-objcopy -O binary --only-section=.text $W/a.o $W/a.bin
  od -An -tx1 -v $W/a.bin | tr -s ' \n' ' ' | sed 's/^ //; s/ $//'
}

echo "(* generated from gen/$(basename $spec) by lib_test/cross/gen.sh *)"
echo
echo "let mode = $helpers.$mode"
echo
echo "let suite ="
echo "  OUnit2.( >::: ) \"$suite\""
echo "    ["
while IFS='|' read -r asm inputs outputs landings; do
  asm=$(echo "$asm" | sed 's/^ *//; s/ *$//')
  [ -z "$asm" ] && continue
  if [[ "$asm" == \#* ]]; then echo "      (* ${asm#\# } *)"; continue; fi
  code=$(assemble "$asm") || exit 1
  for d in $drop; do outputs=$(echo " $outputs " | sed "s/ $d / /g"); done
  expand "$inputs" | sed "s/^/$code |/; s/\$/ | $outputs | $landings/" > $W/in
  $qemu ${qemu_cpu:+-cpu $qemu_cpu} $run < $W/in > $W/out 2> $W/err ||
    { echo "ERROR running '$asm': $(grep -v 'uncaught target signal' $W/err)" >&2; exit 1; }
  # the instructions that fault for all inputs, e.g., those that the
  # processor does not implement, are skipped
  if ! grep -qv '^FAULT$' $W/out; then
    echo "warning: skipping '$asm', it faults for all inputs" >&2
    continue
  fi
  echo "      Lifter_test.case mode \"$asm\" \"$code\""
  echo "        (Lifter_test.vectors"
  echo "           {|"
  grep -v '^FAULT$' $W/out
  echo "|});"
done < $spec
echo "    ]"
