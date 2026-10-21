/* the image at the top of the address space, at high_base, where the
   executors may keep their own memory, e.g., the trampolines */
PHDRS {
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS {
  . = high_base;
  .text : { *(.text .text.*) } :text
  .rodata : { *(.rodata .rodata.*) } :text
  . = ALIGN(0x1000);
  .data : { *(.data .data.* .sdata .sdata.*) } :data
  .bss : { *(.bss .bss.* .sbss .sbss.* COMMON) } :data
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.MIPS.*) *(.reginfo) *(.ARM.*) }
}
