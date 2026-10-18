// Registers the LLVM disassembler in the program, the only function of
// the program that the plugin calls. It is compiled apart, in the large
// code model on Windows, where the plugin may be further than 2 GB from
// the program, so that the rest of the plugin is in the default model,
// whose references flexlink makes much fewer sections of, see dune.
#include <memory>
#include <string>
#include "disasm.hpp"

int llvm_register_disassembler(std::shared_ptr<bap::disasm_factory> f) {
    return bap::register_disassembler("llvm", f);
}
