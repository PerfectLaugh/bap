#ifndef LLVM_LOADER_HPP
#define LLVM_LOADER_HPP

#include <iostream>

#include "llvm_error_or.hpp"
#include "llvm_coff_loader.hpp"
#include "llvm_elf_loader.hpp"
#include "llvm_macho_loader.hpp"

namespace loader {

using namespace llvm;
using namespace llvm::object;

error_or<object::Binary> get_binary(const char* data, std::size_t size) {
    StringRef data_ref(data, size);
    MemoryBufferRef buf(data_ref, "binary");
    auto binary = createBinary(buf);
    if (!binary)
        return failure(toString(binary.takeError()));
    error_or<object::Binary> v(binary->release());
    return v;
}

error_or<std::string> unsupported_filetype() { return success(std::string("")); }

template <typename T>
error_or<std::string> load_base(tables &s, const object::Binary *binary) {
    if (auto bin = llvm::dyn_cast<T>(binary))
        return load(s, *bin);
    else
        return unsupported_filetype();
}

error_or<std::string> load_elf(tables &s, const object::Binary *binary) {
    if (isa<ELF32LEObjectFile>(*binary))
        return load_base<ELF32LEObjectFile>(s, binary);
    else if (isa<ELF32BEObjectFile>(*binary))
        return load_base<ELF32BEObjectFile>(s, binary);
    else if (isa<ELF64LEObjectFile>(*binary))
        return load_base<ELF64LEObjectFile>(s, binary);
    else if (isa<ELF64BEObjectFile>(*binary))
        return load_base<ELF64BEObjectFile>(s, binary);
    else
        return unsupported_filetype();
}

error_or<std::string> load_coff(tables &s,const object::Binary *binary, const char * pdb_path) {
     if (auto bin = llvm::dyn_cast<COFFObjectFile>(binary))
         return load(s, *bin, pdb_path);
    else
        return unsupported_filetype();
}

error_or<std::string> load_macho(tables &s, const object::Binary *binary) {
    return load_base<MachOObjectFile>(s, binary);
}

template <typename T>
void verbose_fails(const error_or<T> &loaded) {
    if(const char* env_p = std::getenv("BAP_DEBUG")) {
        if (std::string(env_p) == "1" || std::string(env_p) == "true")
            if (!loaded)
                std::cerr << "ogre llvm loader error: " << loaded.message() << std::endl;
        for (auto w : loaded.warnings())
            std::cerr << "ogre llvm loader warning: " << w << std::endl;
    }
}

int addr_size(const Triple &target, const object::ObjectFile *obj) {
    if (target.isArch64Bit()) {
        return 64;
    } else if (target.isArch32Bit()) {
        return 32;
    } else if (target.isArch16Bit()) {
        return 16;
    } else {
        return obj->getBytesInAddress() * 8;
    }
}

// the subarchitecture, or the release 6 of MIPS, which the flags of ELF
// tell, as the triple doesn't
std::string subarch(const Triple &target, const object::ObjectFile *obj) {
    switch (target.getArch()) {
    case Triple::mips:
    case Triple::mipsel:
    case Triple::mips64:
    case Triple::mips64el:
        if (auto elf = dyn_cast<ELFObjectFileBase>(obj)) {
            auto arch = elf->getPlatformFlags() & ELF::EF_MIPS_ARCH;
            if (arch == ELF::EF_MIPS_ARCH_32R6 || arch == ELF::EF_MIPS_ARCH_64R6)
                return "r6";
        }
        break;
    default:
        break;
    }
    return prim::string_of_subarch(target.getSubArch());
}

void emit_common_header(tables &s, const object::ObjectFile *obj) {
    auto target = obj->makeTriple();
    s.entry("arch") << Triple::getArchTypeName(target.getArch());
    s.entry("subarch") << subarch(target, obj);
    s.entry("vendor") << target.getVendorName();
    s.entry("system") << target.getOSName();
    s.entry("abi") << prim::string_of_abi(target.getEnvironment());
    s.entry("bits") << addr_size(target, obj);
    s.entry("is-little-endian") << target.isLittleEndian();
}

error_or<std::string> load(const char* data, std::size_t size, const char * pdb_path) {
    error_or<object::Binary> result = get_binary(data, size);
    if (!result) { verbose_fails(result); return unsupported_filetype(); }
    auto object = llvm::dyn_cast<object::ObjectFile>(result.get());
    if (!object) return unsupported_filetype();
    tables s;
    emit_common_header(s, object);
    if (object->isCOFF())   return load_coff(s, object, pdb_path);
    else if (object->isELF())    return load_elf(s, object);
    else if (object->isMachO())  return load_macho(s, object);
    else return unsupported_filetype();
}

typedef error_or<std::string> bap_llvm_loader;

const bap_llvm_loader * create(const char* data, std::size_t size, const char *pdb_path) {
    error_or<std::string> loaded = load(data, size, pdb_path);
    verbose_fails(loaded);
    return new bap_llvm_loader(std::move(loaded));
}

bool file_not_supported(const bap_llvm_loader * loader) {
    return (!loader->has_error() && (*loader)->size() == 0);
}

void destroy(const bap_llvm_loader *loader) { delete loader; }

} // namespace loader

#endif // LLVM_LOADER_HPP
