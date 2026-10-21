/* one segment, which is readable, writable, and executable */
PHDRS {
  all PT_LOAD FLAGS(7);
}
SECTIONS {
  . = 0x20000;
  .text : { *(.text .text.*) } :all
  .rodata : { *(.rodata .rodata.*) } :all
  .data : { *(.data .data.* .sdata .sdata.*) } :all
  .bss : { *(.bss .bss.* .sbss .sbss.* COMMON) } :all
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.MIPS.*) *(.reginfo) *(.ARM.*) }
}
