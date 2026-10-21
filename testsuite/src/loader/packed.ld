/* all sections in one page, one after another, without the alignment
   of the pages, in the segments of their permissions */
PHDRS {
  text PT_LOAD FLAGS(5);
  data PT_LOAD FLAGS(6);
}
SECTIONS {
  . = 0x10000;
  .text : { *(.text .text.*) } :text
  .rodata : { *(.rodata .rodata.*) } :text
  .data : { *(.data .data.* .sdata .sdata.*) } :data
  .bss : { *(.bss .bss.* .sbss .sbss.* COMMON) } :data
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.MIPS.*) *(.reginfo) *(.ARM.*) }
}
