/* The code and the data of a program in segments that share a page, the data one writable and executable. */
PHDRS {
  text PT_LOAD FILEHDR PHDRS FLAGS(5);
  data PT_LOAD FLAGS(7);
}
SECTIONS {
  . = 0x400000 + SIZEOF_HEADERS;
  .text : { *(.text .text.*) *(.init) *(.fini) } :text
  .rodata : { *(.rodata .rodata.*) } :text
  .data : { *(.data .data.* .init_array* .fini_array*) } :data
  .bss : { *(.bss .bss.* COMMON) } :data
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) }
}
