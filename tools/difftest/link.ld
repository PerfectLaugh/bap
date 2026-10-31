/* One read, write and execute segment at a fixed address, so the slot and the window have the same addresses in every run. */
SECTIONS {
  . = 0x10000000 + SIZEOF_HEADERS;
  .MIPS.abiflags : { *(.MIPS.abiflags) }
  .text : { *(.text*) *(.rodata*) }
  .got : { *(.got*) *(.toc*) }
  .data : { *(.data*) *(.sdata*) }
  .bss : { *(.bss*) *(.sbss*) *(COMMON) }
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.ARM.*) *(.MIPS.options) *(.reginfo) *(.mdebug*) *(.gnu*) *(.riscv*) *(.pdr) }
}
