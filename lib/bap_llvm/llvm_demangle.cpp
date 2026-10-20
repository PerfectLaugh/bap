// Demangles the names of the symbols with the demangler of LLVM, which
// knows the manglings of Itanium, e.g., of GCC and Clang, of MSVC, of
// Rust, and of D, instead of the c++filt of binutils.

#include <string>

#include <llvm/Demangle/Demangle.h>

extern "C" {
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
}

// [bap_llvm_demangle name] the demangled [name], or [name], if it is not
// mangled, or the demangler fails
extern "C" value bap_llvm_demangle(value name) {
    CAMLparam1(name);
    std::string mangled(String_val(name), caml_string_length(name));
    std::string demangled = llvm::demangle(mangled);
    CAMLreturn(caml_alloc_initialized_string(demangled.size(), demangled.data()));
}
