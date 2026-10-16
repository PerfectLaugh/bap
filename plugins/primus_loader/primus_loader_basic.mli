open Bap_primus.Std

(** Basic generic loader that works more or less correctly for all architectures
    and abi.

    The loader performs the following tasks:

    - Loads memory segments, including the virtual one, sets up brk, end, edata,
      etext, and environ variables (see any unix man page for the description of
      these symbols). Note (edata and etext are not guaranteed, while end and
      brk are)

    - Adds CPU registers to the environment and initializes them with zero.

    - Allocates a thread-local storage region and initializes the target's
      thread register, if the target defines one. The thread register points
      to the thread control block, which is followed by the TLS block of the
      executable (the variant I of the TLS layout), initialized from its TLS
      template, if the executable has one.

    - Applies the relocations, including the relative ones, whose values are
      biased, and, after all components are initialized, the relocations of
      the indirect functions (IRELATIVE), whose values are computed by calling
      their resolvers.

    - Set's the main frame (copies arguments from the ctxt to the stack)

    - Allocates a stack segment. The [stack_base] address points to the first
      byte beyond the end of the stack segment. The memory region between
      [(stack_base - stack_size, stack_base)] is the stack segment. Note, that
      the [stack_base] address doesn't belong to it. The memory is initialized
      to random values, and can be used to store automatic variables and pass
      arguments.

    After the image is loaded, the SP will point to the number of command line
    arguments, and the arguments will follow it, e.g. if an address size is 4
    bytes, then SP+4 will point to the first argument (program name), SP+8 to
    the first specified command line argument, and so on. A null will follow the
    last argument. After that the same null terminated table of environment
    variables will follow. (It can be easy accessed via the [environ] symbol)
    It is followed by the auxiliary vector, a table of type and value pairs
    that ends with AT_NULL, which describes the program headers (AT_PHDR,
    AT_PHENT, AT_PHNUM), the entry point (AT_ENTRY), the page size, and points
    to 16 bytes of zeros (AT_RANDOM). The strings of the arguments and of the
    environment are stored after the 16 bytes.

    Note: the layout of the main function stack frame is not standartized in the
    C standard, neither it is a part of any ABI. A system loader may put
    arguments and environment variables in any place, including stack, heap, or,
    even, ROM. We chose to put it in the stack just above the stack_base
    address. As a result, the actual size of the stack is a little big biger,
    and it is possible to access to the memory that is beyond the stack_base
    address. *)

module type Param = sig
  val stack_size : int
  val stack_base : int64
end

module Make (P : Param) : Primus.Machine.Component
