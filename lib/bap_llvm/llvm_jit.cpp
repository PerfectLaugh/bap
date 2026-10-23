// The JIT of LLVM, which compiles the modules of LLVM IR, in their text,
// to the native code of the host, see bap_llvm_jit.mli.

#include <memory>
#include <string>

#include <llvm/AsmParser/Parser.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/PassInstrumentation.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>

extern "C" {
#include <caml/alloc.h>
#include <caml/custom.h>
#include <caml/fail.h>
#include <caml/memory.h>
#include <caml/mlvalues.h>
}

using namespace llvm;
using namespace llvm::orc;

namespace {

// the JITs live as long as the program, as the code, that they made,
// may be called anytime
struct jit {
    std::unique_ptr<LLJIT> lljit;
};

jit *jit_val(value v) { return *static_cast<jit **>(Data_custom_val(v)); }

// the code of a module, which is removed, when it is released, rather
// than when it is collected, as the code may run, while nothing of OCaml
// refers to it
struct code {
    ResourceTrackerSP tracker;
    uint64_t address;
};

code *code_val(value v) {
    return *static_cast<code **>(Data_custom_val(v));
}

void finalize_code(value v) {
    code *c = code_val(v);
    if (c) {
        // the tracker stays, unless the code was released
        c->tracker.reset();
        delete c;
    }
}

struct custom_operations code_ops = {
    "bap.llvm.jit.code",      finalize_code,
    custom_compare_default,   custom_hash_default,
    custom_serialize_default, custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

struct custom_operations jit_ops = {
    "bap.llvm.jit",           custom_finalize_default,
    custom_compare_default,   custom_hash_default,
    custom_serialize_default, custom_deserialize_default,
    custom_compare_ext_default, custom_fixed_length_default};

[[noreturn]] void fail(const std::string &msg) { caml_failwith(msg.c_str()); }

std::string message(Error err) {
    std::string msg;
    raw_string_ostream os(msg);
    os << err;
    return os.str();
}

// the passes, that promote the variables to the registers, and fold the
// expressions, as the code generator does the rest, rather than the
// pipelines of PassBuilder, which links all the passes of LLVM
void optimize(Module &m) {
    FunctionAnalysisManager fam;
    fam.registerPass([] { return PassInstrumentationAnalysis(); });
    fam.registerPass([] { return DominatorTreeAnalysis(); });
    fam.registerPass([] { return AssumptionAnalysis(); });
    fam.registerPass([] { return TargetLibraryAnalysis(); });
    fam.registerPass([] { return TargetIRAnalysis(); });
    FunctionPassManager fpm;
    fpm.addPass(SROAPass(SROAOptions::ModifyCFG));
    fpm.addPass(EarlyCSEPass());
    fpm.addPass(SimplifyCFGPass());
    fpm.addPass(DCEPass());
    for (auto &f : m)
        if (!f.isDeclaration()) fpm.run(f, fam);
}

} // namespace

extern "C" value bap_llvm_jit_create(value unit) {
    CAMLparam1(unit);
    CAMLlocal1(r);
    static bool initialized = false;
    if (!initialized) {
        if (InitializeNativeTarget() || InitializeNativeTargetAsmPrinter())
            fail("the JIT of LLVM doesn't have the target of the host");
        initialized = true;
    }
    auto lljit = LLJITBuilder().create();
    if (!lljit) fail(message(lljit.takeError()));
    r = caml_alloc_custom(&jit_ops, sizeof(jit *), 0, 1);
    *static_cast<jit **>(Data_custom_val(r)) = new jit{std::move(*lljit)};
    CAMLreturn(r);
}

// [define jit name addr] the symbol [name] of the modules is at [addr]
extern "C" value bap_llvm_jit_define(value v, value name, value addr) {
    CAMLparam3(v, name, addr);
    jit *j = jit_val(v);
    auto &lib = j->lljit->getMainJITDylib();
    SymbolMap symbols;
    symbols[j->lljit->mangleAndIntern(String_val(name))] = {
        ExecutorAddr(static_cast<uint64_t>(Nativeint_val(addr))),
        JITSymbolFlags::Exported | JITSymbolFlags::Absolute};
    if (auto err = lib.define(absoluteSymbols(std::move(symbols))))
        fail(message(std::move(err)));
    CAMLreturn(Val_unit);
}

// [compile jit ir name] the code of the module, whose text is [ir],
// which is optimized, and the address of its function [name]
extern "C" value bap_llvm_jit_compile(value v, value ir, value name) {
    CAMLparam3(v, ir, name);
    CAMLlocal1(r);
    jit *j = jit_val(v);
    auto ctx = std::make_unique<LLVMContext>();
    SMDiagnostic diag;
    auto m = parseAssemblyString(
        StringRef(String_val(ir), caml_string_length(ir)), diag, *ctx);
    if (!m) {
        std::string msg;
        raw_string_ostream os(msg);
        diag.print("jit", os);
        fail(os.str());
    }
    std::string errors;
    raw_string_ostream os(errors);
    if (verifyModule(*m, &os)) fail("the module is invalid: " + os.str());
    m->setDataLayout(j->lljit->getDataLayout());
    m->setTargetTriple(j->lljit->getTargetTriple());
    optimize(*m);
    auto tracker = j->lljit->getMainJITDylib().createResourceTracker();
    if (auto err = j->lljit->addIRModule(
            tracker, ThreadSafeModule(std::move(m), std::move(ctx))))
        fail(message(std::move(err)));
    auto sym = j->lljit->lookup(String_val(name));
    if (!sym) {
        std::string msg = message(sym.takeError());
        if (auto err = tracker->remove()) consumeError(std::move(err));
        fail(msg);
    }
    r = caml_alloc_custom(&code_ops, sizeof(code *), 0, 1);
    *static_cast<code **>(Data_custom_val(r)) =
        new code{tracker, sym->getValue()};
    CAMLreturn(r);
}

extern "C" value bap_llvm_jit_address(value v) {
    CAMLparam1(v);
    code *c = code_val(v);
    if (!c->tracker) caml_invalid_argument("Bap_llvm_jit.address: released");
    CAMLreturn(caml_copy_nativeint(static_cast<intnat>(c->address)));
}

// removes the code, which must not run anymore
extern "C" value bap_llvm_jit_release(value v) {
    CAMLparam1(v);
    code *c = code_val(v);
    if (c->tracker) {
        if (auto err = c->tracker->remove()) fail(message(std::move(err)));
        c->tracker.reset();
    }
    CAMLreturn(Val_unit);
}
