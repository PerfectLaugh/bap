// The JIT of LLVM, which compiles the modules of LLVM IR, in their text,
// to the native code of the host, see bap_llvm_jit.mli.

#include <memory>
#include <string>

#include <llvm/AsmParser/Parser.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/Path.h>
#include <llvm/Target/TargetMachine.h>
#include <llvm/ExecutionEngine/Orc/JITTargetMachineBuilder.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Analysis/AliasAnalysis.h>
#include <llvm/Analysis/AssumptionCache.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/Analysis/TargetLibraryInfo.h>
#include <llvm/Analysis/TargetTransformInfo.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/PassInstrumentation.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/Scalar/DCE.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Scalar/Sink.h>
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
    // the code generator of the objects, that the JIT links, which are
    // cached, see [compile]
    std::unique_ptr<TargetMachine> tm;
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
    fam.registerPass([] { return LoopAnalysis(); });
    fam.registerPass([] { return AAManager(); });
    FunctionPassManager fpm;
    fpm.addPass(SROAPass(SROAOptions::ModifyCFG));
    fpm.addPass(EarlyCSEPass());
    fpm.addPass(SimplifyCFGPass());
    fpm.addPass(DCEPass());
    // the values, that only the exits of a loop use, e.g., the flags of
    // its last iteration, which the loop doesn't compute each time
    fpm.addPass(SinkingPass());
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
    // the code calls the functions of the program, e.g., of its runtime,
    // that may be further than 2 GB from it, so its calls are absolute,
    // in the large model, rather than relative, which the linker of the
    // JIT doesn't relocate on every host, e.g., the one of COFF on Windows
    auto host = JITTargetMachineBuilder::detectHost();
    if (!host) fail(message(host.takeError()));
    host->setCodeModel(CodeModel::Large);
    auto tm = host->createTargetMachine();
    if (!tm) fail(message(tm.takeError()));
    auto lljit = LLJITBuilder().setJITTargetMachineBuilder(std::move(*host)).create();
    if (!lljit) fail(message(lljit.takeError()));
    r = caml_alloc_custom(&jit_ops, sizeof(jit *), 0, 1);
    *static_cast<jit **>(Data_custom_val(r)) =
        new jit{std::move(*lljit), std::move(*tm)};
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

namespace {

// the object of the module, whose text is [ir], which is optimized
std::unique_ptr<MemoryBuffer> compile_object(jit *j, value ir,
                                             const char *name) {
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
    SmallVector<char, 0> buf;
    raw_svector_ostream out(buf);
    legacy::PassManager pm;
    if (j->tm->addPassesToEmitFile(pm, out, nullptr,
                                   CodeGenFileType::ObjectFile))
        fail("the code generator can't emit the objects");
    pm.run(*m);
    return MemoryBuffer::getMemBufferCopy(StringRef(buf.data(), buf.size()),
                                          name);
}

// writes the object to the file, through a new temporary file in its
// folder, so that the file is never partly written
void save(const std::string &path, const MemoryBuffer &obj) {
    SmallString<256> tmp;
    int fd;
    if (sys::fs::createUniqueFile(path + ".%%%%%%.tmp", fd, tmp)) return;
    {
        raw_fd_ostream out(fd, /*shouldClose=*/true);
        out << obj.getBuffer();
        if (out.has_error()) {
            out.clear_error();
            sys::fs::remove(tmp);
            return;
        }
    }
    if (sys::fs::rename(tmp, path)) sys::fs::remove(tmp);
}

} // namespace

// [compile jit ir name path] the code of the module, whose text is [ir],
// which is optimized, and the address of its function [name], whose
// object is cached in the file [path], unless it is empty, and is read
// from it, if it is there
extern "C" value bap_llvm_jit_compile(value v, value ir, value name,
                                      value path) {
    CAMLparam4(v, ir, name, path);
    CAMLlocal1(r);
    jit *j = jit_val(v);
    std::string file(String_val(path), caml_string_length(path));
    std::unique_ptr<MemoryBuffer> obj;
    bool cached = false;
    if (!file.empty()) {
        auto b = MemoryBuffer::getFile(file);
        if (b) {
            obj = std::move(*b);
            cached = true;
        }
    }
    for (;;) {
        if (!obj) {
            obj = compile_object(j, ir, String_val(name));
            if (!file.empty()) save(file, *obj);
        }
        auto tracker = j->lljit->getMainJITDylib().createResourceTracker();
        uint64_t address = 0;
        Error err = j->lljit->addObjectFile(tracker, std::move(obj));
        if (!err) {
            auto sym = j->lljit->lookup(String_val(name));
            if (sym)
                address = sym->getValue();
            else
                err = sym.takeError();
        }
        if (err) {
            std::string msg = message(std::move(err));
            if (auto e = tracker->remove()) consumeError(std::move(e));
            // the cached object, that is broken, is compiled anew
            if (cached) {
                cached = false;
                sys::fs::remove(file);
                continue;
            }
            fail(msg);
        }
        r = caml_alloc_custom(&code_ops, sizeof(code *), 0, 1);
        *static_cast<code **>(Data_custom_val(r)) = new code{tracker, address};
        CAMLreturn(r);
    }
}

// [symbol jit name] the address of the symbol [name] of a module, e.g.,
// of its data, which stays, until its code is released
extern "C" value bap_llvm_jit_symbol(value v, value name) {
    CAMLparam2(v, name);
    jit *j = jit_val(v);
    auto sym = j->lljit->lookup(String_val(name));
    if (!sym) fail(message(sym.takeError()));
    CAMLreturn(caml_copy_nativeint(static_cast<intnat>(sym->getValue())));
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
