/* A program whose first segment starts at its program headers, not at the start of the file, with a PT_PHDR. */
PHDRS {
  hdr PT_PHDR PHDRS;
  text PT_LOAD PHDRS FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS {
  . = 0x400040 + SIZEOF_HEADERS - 0x40;
  .text : { *(.text .text.*) *(.init) *(.fini) } :text
  .rodata : { *(.rodata .rodata.*) } :text
  . = ALIGN(0x1000) + (. & 0xfff);
  .data : { *(.data .data.* .init_array* .fini_array*) } :data
  .bss : { *(.bss .bss.* COMMON) } :data
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
