#ifndef LLVM_ELF_LOADER_HPP
#define LLVM_ELF_LOADER_HPP

#include <algorithm>
#include <cstring>
#include <iostream>
#include <iomanip>

#include <llvm/Object/ELFObjectFile.h>

#include "llvm_error_or.hpp"
#include "llvm_loader_utils.hpp"
#include "llvm_primitives.hpp"

namespace loader {
namespace elf_loader {

using namespace llvm;
using namespace llvm::object;

template <typename T>
bool has_addresses(const ELFObjectFile<T> &obj) {
#if LLVM_VERSION_MAJOR >= 12
    auto hdr = &obj.getELFFile().getHeader();
#else
    auto hdr = obj.getELFFile()->getHeader();
#endif
    return (hdr->e_type == ELF::ET_EXEC ||
            hdr->e_type == ELF::ET_DYN ||
            hdr->e_type == ELF::ET_CORE);
}


template <typename T>
bool is_executable(const ELFObjectFile<T> &obj) {
#if LLVM_VERSION_MAJOR >= 12
    auto hdr = &obj.getELFFile().getHeader();
#else
    auto hdr = obj.getELFFile()->getHeader();
#endif
    return (hdr->e_type == ELF::ET_EXEC ||
            hdr->e_type == ELF::ET_DYN);
}

// computes the base address of an ELF file.
//
// The base address is derived as a difference between the
// virtual address of any loadable code segment and its offset.
//
// If there are no loadable segments then the base is 0.
template <typename T>
uint64_t base_address(const ELFObjectFile<T> &obj) {
    uint64_t base = 0L;
#if LLVM_VERSION_MAJOR >= 12
    auto elf = obj.getELFFile();
#else
    auto elf = *obj.getELFFile();
#endif
    auto segs = prim::elf_program_headers(elf);
    auto code = segs.end();

    for (auto it = segs.begin(); it != segs.end(); ++it)
        if (it->p_type == ELF::PT_LOAD && (it->p_flags & ELF::PF_X))
            code = it;

    if (code != segs.end())
        base = code->p_vaddr - code->p_offset;
    return base;
}

template <typename T>
uint64_t minimal_progbits_offset(const ELFObjectFile<T> &obj) {
    auto smallest = std::numeric_limits<uint64_t>::max();
#if LLVM_VERSION_MAJOR >= 12
    auto &elf_file = obj.getELFFile();
#else
    auto &elf_file = *obj.getELFFile();
#endif
    for (auto sec :  prim::elf_sections(elf_file)) {
        if (sec.sh_type == ELF::SHT_PROGBITS && sec.sh_offset < smallest) {
            smallest = sec.sh_offset;
        }
    }
    return smallest == std::numeric_limits<uint64_t>::max() ? 0L : smallest;
}

template <typename T>
void emit_entry_point(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto hdr = &obj.getELFFile().getHeader();
#else
    auto hdr = obj.getELFFile()->getHeader();
#endif
    s.entry("llvm:entry-point") << hdr->e_entry;
}

std::string name_of_index(std::size_t i) {
    std::ostringstream s;
    s << std::setfill('0') << std::setw(2) << i;
    return s.str();
}

template <typename T>
void emit_program_headers(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto hdrs = prim::elf_program_headers(obj.getELFFile());
#else
    auto hdrs = prim::elf_program_headers(*obj.getELFFile());
#endif
    for (auto it = hdrs.begin(); it != hdrs.end(); ++it) {
        bool ld = (it->p_type == ELF::PT_LOAD);
        bool r = static_cast<bool>(it->p_flags & ELF::PF_R);
        bool w = static_cast<bool>(it->p_flags & ELF::PF_W);
        bool x = static_cast<bool>(it->p_flags & ELF::PF_X);
        auto off = it->p_offset;
        auto filesz = it->p_filesz;
        auto name = name_of_index(it - hdrs.begin());
        s.entry("llvm:elf-program-header") << name << off << filesz;
        s.entry("llvm:elf-virtual-program-header") << name << it->p_vaddr << it->p_memsz;
        s.entry("llvm:elf-program-header-flags") << name << ld << r << w << x;
    }
}

template <typename T>
uint64_t section_offset(const ELFObjectFile<T> &obj, section_iterator it) {
    if (it == obj.section_end()) return 0L;
    else {
        auto sec_elf = obj.getSection(it->getRawDataRefImpl());
        return sec_elf->sh_offset;
    }
}

template <typename T>
uint64_t section_address(const ELFObjectFile<T> &obj,
                         const typename ELFFile<T>::Elf_Shdr *sec) {
    return has_addresses(obj)
        ? sec->sh_addr
        : sec->sh_offset - minimal_progbits_offset(obj);
}

template <typename T>
uint64_t section_address(const ELFObjectFile<T> &obj, const SectionRef& sec) {
    return section_address(obj, obj.getSection(sec.getRawDataRefImpl()));
}

template <typename T>
uint64_t section_address(const ELFObjectFile<T> &obj, section_iterator it) {
    if (it == obj.section_end()) return 0;
    else return section_address(obj, *it);
}


template <typename T>
error_or<uint64_t> symbol_file_offset(const ELFObjectFile<T> &obj, const SymbolRef &sym) {
    auto addr = prim::symbol_address(sym);
    auto sect = prim::symbol_section(obj, sym);
    if (auto er = addr || sect) return er;
    uint64_t off = section_offset(obj, *sect) + (*addr - section_address(obj, *sect));
    return success(off);
}
template <typename T>
void emit_section(const ELFObjectFile<T> &obj,
                  const SectionRef& sec,
                  tables &s) {
    uint64_t addr = section_address(obj, sec);
    auto hdr = obj.getSection(sec.getRawDataRefImpl());
    if (auto name = prim::section_name(sec)) {
        if (!name->empty()) {
            s.entry("llvm:section-entry") << *name << addr << hdr->sh_size << hdr->sh_offset;
            bool w = static_cast<bool>(hdr->sh_flags & ELF::SHF_WRITE);
            bool x = static_cast<bool>(hdr->sh_flags & ELF::SHF_EXECINSTR);
            s.entry("llvm:section-flags") << *name << true << w << x;
            if (x)
                s.entry("llvm:code-entry") << *name << hdr->sh_offset << hdr->sh_size;
        }
    }
}

template <typename T>
void emit_section_headers(const ELFObjectFile<T> &obj, tables &s) {
    for (auto sec : prim::sections(obj))
        emit_section(obj, sec, s);
}

bool is_external(uint64_t addr, uint64_t offset, uint64_t size) {
    return !addr && !offset && !size;
}

template <typename T>
void emit_symbol_entry(const ELFObjectFile<T> &obj, const SymbolRef &sym, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto sym_elf_or_error = obj.getSymbol(sym.getRawDataRefImpl());
    if (!sym_elf_or_error)
        return;
    auto sym_elf = *sym_elf_or_error;
#else
    auto sym_elf = obj.getSymbol(sym.getRawDataRefImpl());
#endif
    auto name = prim::symbol_name(sym);
    auto addr = prim::symbol_address(sym);
    auto off = symbol_file_offset(obj, sym);
    if (name && addr && off && !name->empty()) {
        if (is_external(*addr, *off, sym_elf->st_size) && sym_elf->st_value) {
            s.entry("llvm:name-reference") << sym_elf->st_value << *name;
        } else if (sym_elf->getType() == ELF::STT_FUNC) {
            s.entry("llvm:symbol-entry") << *name
                                         << *addr
                                         << sym_elf->st_size
                                         << *off
                                         << sym_elf->st_value;
            s.entry("llvm:code-entry") << *name << *off << sym_elf->st_size ;
        }
    }
}

template <typename T>
void emit_symbol_entries(const ELFObjectFile<T> &obj, symbol_iterator begin, symbol_iterator end, tables &s) {
    for (auto it = begin; it != end; ++it)
        emit_symbol_entry(obj, *it, s);
}

template <typename T>
void emit_symbol_entries(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto elf = &obj.getELFFile();
#else
    auto elf = obj.getELFFile();
#endif
    emit_symbol_entries(obj, obj.symbol_begin(), obj.symbol_end(), s);
    auto secs = prim::elf_sections(*elf);
    emit_symbol_entries(obj, obj.dynamic_symbol_begin(), obj.dynamic_symbol_end(), s);
}

// the type of the relocations that store the address returned by a
// resolver function (STT_GNU_IFUNC), or 0 if the machine has none
inline uint64_t irelative_relocation_type(uint64_t machine) {
    switch (machine) {
    case ELF::EM_X86_64: return ELF::R_X86_64_IRELATIVE;
    case ELF::EM_386: return ELF::R_386_IRELATIVE;
    case ELF::EM_AARCH64: return ELF::R_AARCH64_IRELATIVE;
    case ELF::EM_ARM: return ELF::R_ARM_IRELATIVE;
    case ELF::EM_RISCV: return ELF::R_RISCV_IRELATIVE;
    case ELF::EM_PPC64: return ELF::R_PPC64_IRELATIVE;
    default: return 0;
    }
}

template <typename T>
uint64_t elf_machine(const ELFFile<T> &elf) {
#if LLVM_VERSION_MAJOR >= 12
    return elf.getHeader().e_machine;
#else
    return elf.getHeader()->e_machine;
#endif
}

template <typename T>
void emit_relocations(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto &elf = obj.getELFFile();
#else
    auto &elf = *obj.getELFFile();
#endif
    auto rel_reloc = elf.getRelativeRelocationType();
    auto irel_reloc = irelative_relocation_type(elf_machine(elf));
    for (auto sec : obj.sections()) {
        for (auto rel : sec.relocations()) {
            auto sym = rel.getSymbol();
            uint64_t raddr = prim::relocation_offset(rel);
            if (sym != prim::end_symbols(obj)) {
                auto typ = prim::symbol_type(*sym);
                if (typ && (*typ == SymbolRef::ST_Function ||
                            *typ == SymbolRef::ST_Data ||
                            *typ == SymbolRef::ST_Unknown)) {
                    if (auto addr = prim::symbol_address(*sym))
                        if (*addr) s.entry("llvm:relocation") << raddr << *addr;
                    if (auto name = prim::symbol_name(*sym))
                        if (!name->empty())
                            s.entry("llvm:name-reference") << raddr << *name;
                }
            } else {
                auto typ = prim::relocation_type(rel);
                if (typ == rel_reloc) s.entry("llvm:relative-relocation") << raddr;
                // e.g., the .rela.iplt of a static executable
                if (irel_reloc && typ == irel_reloc) {
                    auto addend = ELFRelocationRef(rel).getAddend();
                    if (addend)
                        s.entry("llvm:irelative-relocation") << raddr << uint64_t(*addend);
                    else
                        consumeError(addend.takeError());
                }
            }
        }
    }
}

// The dynamic linker finds the relocations of an executable or a shared
// object through the dynamic segment (PT_DYNAMIC), and so do we, since
// the section headers are not needed at run time and could be stripped
// or garbled. The dynamic segment also references the packed
// relocations, i.e., Android's APS2 (DT_ANDROID_REL[A]) and RELR
// (DT_RELR, DT_ANDROID_RELR), which LLVM doesn't enumerate as the
// relocations of a section.

struct dynamic_relocation {
    uint64_t offset;
    uint64_t type;
    uint64_t symbol;
    int64_t addend;
    bool explicit_addend;
};

// the loadable segments and the dynamic tags of a file
template <typename T>
struct dynamic_image {
    const ELFFile<T> &elf;
    std::vector<typename ELFFile<T>::Elf_Phdr> segments;
    std::vector<std::pair<uint64_t, uint64_t>> tags;

    explicit dynamic_image(const ELFFile<T> &elf)
        : elf(elf), segments(prim::elf_program_headers(elf)) {}

    // the file offset [off] of the [size] bytes at the address [addr],
    // if they are stored in the file
    bool offset_of(uint64_t addr, uint64_t size, uint64_t &off) const {
        uint64_t length = elf.getBufSize();
        for (auto &seg : segments) {
            if (seg.p_type != ELF::PT_LOAD || addr < seg.p_vaddr)
                continue;
            uint64_t delta = addr - seg.p_vaddr;
            if (delta > seg.p_filesz || seg.p_filesz - delta < size)
                continue;
            off = seg.p_offset + delta;
            return off <= length && length - off >= size;
        }
        return false;
    }

    // the [size] bytes at the address [addr], if they are in the file
    const uint8_t *data(uint64_t addr, uint64_t size) const {
        uint64_t off;
        return offset_of(addr, size, off) ? elf.base() + off : nullptr;
    }

    bool tag(uint64_t name, uint64_t &value) const {
        for (auto &t : tags) {
            if (t.first == name) {
                value = t.second;
                return true;
            }
        }
        return false;
    }
};

// reads the entries of the dynamic segment, if there is one
template <typename T>
bool read_dynamic_tags(dynamic_image<T> &img) {
    typedef typename ELFFile<T>::Elf_Dyn dyn;
    uint64_t length = img.elf.getBufSize();
    for (auto &seg : img.segments) {
        if (seg.p_type != ELF::PT_DYNAMIC)
            continue;
        if (seg.p_offset > length || length - seg.p_offset < seg.p_filesz)
            return false;
        auto entries = reinterpret_cast<const dyn *>(img.elf.base() + seg.p_offset);
        for (uint64_t i = 0; i < seg.p_filesz / sizeof(dyn); ++i) {
            if (entries[i].getTag() == ELF::DT_NULL)
                break;
            img.tags.push_back(std::make_pair(uint64_t(entries[i].getTag()),
                                              uint64_t(entries[i].getVal())));
        }
        return true;
    }
    return false;
}

template <typename T>
void read_relocations(const dynamic_image<T> &img, uint64_t addr, uint64_t size,
                      bool rela, std::vector<dynamic_relocation> &relocs) {
    typedef typename ELFFile<T>::Elf_Rel rel_t;
    typedef typename ELFFile<T>::Elf_Rela rela_t;
    bool mips64el = img.elf.isMips64EL();
    auto data = img.data(addr, size);
    if (!data)
        return;
    if (rela) {
        auto rels = reinterpret_cast<const rela_t *>(data);
        for (uint64_t i = 0; i < size / sizeof(rela_t); ++i)
            relocs.push_back({uint64_t(rels[i].r_offset),
                              uint64_t(rels[i].getType(mips64el)),
                              uint64_t(rels[i].getSymbol(mips64el)),
                              int64_t(rels[i].r_addend), true});
    } else {
        auto rels = reinterpret_cast<const rel_t *>(data);
        for (uint64_t i = 0; i < size / sizeof(rel_t); ++i)
            relocs.push_back({uint64_t(rels[i].r_offset),
                              uint64_t(rels[i].getType(mips64el)),
                              uint64_t(rels[i].getSymbol(mips64el)),
                              0, false});
    }
}

// The packed relocations are trusted by the dynamic linker, we limit
// their number, since a group of them could take only a few bytes.
const uint64_t max_packed_relocations = 1 << 24;

// Decodes Android's packed relocations (APS2), as bionic's linker does
// (see linker_reloc_iterators.h). The table is the "APS2" magic and a
// sequence of SLEB128 numbers: the number of relocations, the initial
// offset, and the groups of relocations. A group starts with its size
// and flags, followed by the fields that are shared by the group, and
// then by the fields of each relocation. The offsets and the addends
// are deltas from the previous ones.
template <typename T>
void read_android_relocations(const dynamic_image<T> &img,
                              uint64_t addr, uint64_t size, bool rela,
                              std::vector<dynamic_relocation> &relocs) {
    auto data = img.data(addr, size);
    if (!data || size < 4 || std::memcmp(data, "APS2", 4) != 0)
        return;
    const uint8_t *cur = data + 4, *end = data + size;
    bool ok = true;
    auto sleb = [&]() -> uint64_t {
        uint64_t value = 0;
        unsigned shift = 0;
        uint8_t byte = 0;
        do {
            if (cur == end) {
                ok = false;
                return 0;
            }
            byte = *cur++;
            if (shift < 64)
                value |= uint64_t(byte & 0x7f) << shift;
            shift += 7;
        } while (byte & 0x80);
        if (shift < 64 && (byte & 0x40))
            value |= ~uint64_t(0) << shift;
        return value;
    };
    uint64_t count = sleb();
    uint64_t offset = sleb();
    uint64_t addend = 0;
    if (count > max_packed_relocations)
        return;
    while (ok && count > 0) {
        uint64_t group = sleb();
        uint64_t flags = sleb();
        if (!ok || group == 0 || group > count)
            return;
        bool by_info = flags & ELF::RELOCATION_GROUPED_BY_INFO_FLAG;
        bool by_offset = flags & ELF::RELOCATION_GROUPED_BY_OFFSET_DELTA_FLAG;
        bool by_addend = flags & ELF::RELOCATION_GROUPED_BY_ADDEND_FLAG;
        bool has_addend = flags & ELF::RELOCATION_GROUP_HAS_ADDEND_FLAG;
        uint64_t offset_delta = by_offset ? sleb() : 0;
        uint64_t info = by_info ? sleb() : 0;
        if (rela && by_addend && has_addend)
            addend += sleb();
        if (!has_addend)
            addend = 0;
        for (uint64_t i = 0; ok && i < group; ++i) {
            offset += by_offset ? offset_delta : sleb();
            uint64_t r_info = by_info ? info : sleb();
            if (rela && has_addend && !by_addend)
                addend += sleb();
            bool is64 = T::Is64Bits;
            relocs.push_back({offset,
                              is64 ? (r_info & 0xffffffff) : (r_info & 0xff),
                              is64 ? (r_info >> 32) : (r_info >> 8),
                              int64_t(addend), rela});
        }
        count -= group;
    }
}

// Decodes the RELR relative relocations. An even entry is the address
// of a relocated word, and an odd entry is a bitmap of the relocated
// words that follow the last relocated address, its bit i + 1 is set
// when the word i is relocated. The addends are stored in the words.
template <typename T>
void read_relr_relocations(const dynamic_image<T> &img, uint64_t addr, uint64_t size,
                           std::vector<dynamic_relocation> &relocs) {
    typedef typename ELFFile<T>::Elf_Addr word;
    const uint64_t wordsize = sizeof(word);
    auto data = img.data(addr, size);
    if (!data)
        return;
    auto entries = reinterpret_cast<const word *>(data);
    uint64_t relative = img.elf.getRelativeRelocationType();
    uint64_t base = 0;
    for (uint64_t i = 0; i < size / wordsize; ++i) {
        uint64_t entry = entries[i];
        if ((entry & 1) == 0) {
            relocs.push_back({entry, relative, 0, 0, false});
            base = entry + wordsize;
        } else {
            for (uint64_t j = 0; (entry >>= 1) != 0; ++j)
                if (entry & 1)
                    relocs.push_back({base + j * wordsize, relative, 0, 0, false});
            base += (8 * wordsize - 1) * wordsize;
        }
    }
}

// the relocations that store the address of a symbol
enum class symbol_relocation { none, absolute, slot };

// [kind_of_relocation machine type] is [absolute] for the relocations
// that store S + A, where the implicit addend A of a REL relocation is
// the contents of the place, and [slot] for the GOT and PLT entries,
// that store S (plus the explicit addend, if any).
inline symbol_relocation kind_of_relocation(uint64_t machine, uint64_t type, bool is64) {
    auto abs_if = [](bool c) {
        return c ? symbol_relocation::absolute : symbol_relocation::none;
    };
    auto slot_if = [](bool c) {
        return c ? symbol_relocation::slot : symbol_relocation::none;
    };
    switch (machine) {
    case ELF::EM_X86_64:
        if (type == ELF::R_X86_64_64) return symbol_relocation::absolute;
        return slot_if(type == ELF::R_X86_64_GLOB_DAT ||
                       type == ELF::R_X86_64_JUMP_SLOT);
    case ELF::EM_386:
        if (type == ELF::R_386_32) return symbol_relocation::absolute;
        return slot_if(type == ELF::R_386_GLOB_DAT ||
                       type == ELF::R_386_JUMP_SLOT);
    case ELF::EM_AARCH64:
        if (type == ELF::R_AARCH64_ABS64) return symbol_relocation::absolute;
        return slot_if(type == ELF::R_AARCH64_GLOB_DAT ||
                       type == ELF::R_AARCH64_JUMP_SLOT);
    case ELF::EM_ARM:
        if (type == ELF::R_ARM_ABS32) return symbol_relocation::absolute;
        return slot_if(type == ELF::R_ARM_GLOB_DAT ||
                       type == ELF::R_ARM_JUMP_SLOT);
    case ELF::EM_RISCV:
        if (type == ELF::R_RISCV_JUMP_SLOT) return symbol_relocation::slot;
        return abs_if(type == (is64 ? ELF::R_RISCV_64 : ELF::R_RISCV_32));
    case ELF::EM_PPC64:
        if (type == ELF::R_PPC64_ADDR64) return symbol_relocation::absolute;
        return slot_if(type == ELF::R_PPC64_GLOB_DAT ||
                       type == ELF::R_PPC64_JMP_SLOT);
    default:
        return symbol_relocation::none;
    }
}

// The number of the dynamic symbols, which the dynamic segment doesn't
// store, so it is derived from the symbol hash tables, as the dynamic
// linker does. The number of chains of the SysV hash table (DT_HASH) is
// the number of symbols. The GNU hash table (DT_GNU_HASH) has a chain
// for the symbols starting from symoffset, the last symbol is at the end
// of the chain of the last bucket (it has the lowest bit set).
template <typename T>
uint64_t dynamic_symbol_count(const dynamic_image<T> &img) {
    typedef typename ELFFile<T>::Elf_Word elf_word;
    const uint64_t w = sizeof(elf_word);
    uint64_t addr;
    if (img.tag(ELF::DT_HASH, addr)) {
        auto table = reinterpret_cast<const elf_word *>(img.data(addr, 2 * w));
        if (table) return table[1];
    }
    if (!img.tag(ELF::DT_GNU_HASH, addr))
        return 0;
    auto header = reinterpret_cast<const elf_word *>(img.data(addr, 4 * w));
    if (!header) return 0;
    uint64_t nbuckets = header[0], symoffset = header[1], blooms = header[2];
    uint64_t buckets_addr = addr + 4 * w + blooms * sizeof(typename ELFFile<T>::Elf_Addr);
    auto buckets = reinterpret_cast<const elf_word *>(img.data(buckets_addr, nbuckets * w));
    if (!buckets) return 0;
    uint64_t last = 0;
    for (uint64_t i = 0; i < nbuckets; ++i)
        last = std::max(last, uint64_t(buckets[i]));
    if (last < symoffset) return symoffset;
    uint64_t chains = buckets_addr + nbuckets * w;
    for (;; ++last) {
        auto chain = reinterpret_cast<const elf_word *>(
            img.data(chains + (last - symoffset) * w, w));
        if (!chain) return last;
        if (*chain & 1) return last + 1;
    }
}

// Emits the dynamic relocations, the same way as [emit_relocations]
// does, but with the addends. The value of a relative relocation is
// B + A, where B is the bias of the file, which is applied later, and
// the addend A of a REL or RELR relocation is stored in the place.
// The explicit addends of the RELA relocations, which the static linker
// doesn't have to store in the place, are emitted as the words that
// should be stored at their file offsets, but only if the place
// doesn't hold them already, and the addresses that the relative
// relocations store are emitted as their targets. The names of the
// needed libraries are emitted as well, and so are the function symbols
// of the dynamic symbol table, if LLVM didn't find it, because the
// section headers are missing. Returns false if the file has no dynamic
// segment.
template <typename T>
bool emit_dynamic_relocations(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto &elf = obj.getELFFile();
#else
    auto &elf = *obj.getELFFile();
#endif
    typedef typename ELFFile<T>::Elf_Sym sym_t;
    typedef typename ELFFile<T>::Elf_Addr word;
    dynamic_image<T> img(elf);
    if (!read_dynamic_tags(img))
        return false;

    uint64_t strtab = 0, strsz = 0, symtab = 0, syment = sizeof(sym_t);
    bool has_strtab = img.tag(ELF::DT_STRTAB, strtab) &&
                      img.tag(ELF::DT_STRSZ, strsz);
    bool has_symtab = img.tag(ELF::DT_SYMTAB, symtab);
    img.tag(ELF::DT_SYMENT, syment);
    auto strings = has_strtab ? img.data(strtab, strsz) : nullptr;
    auto string_at = [&](uint64_t off) {
        if (!strings || off >= strsz) return std::string();
        auto str = reinterpret_cast<const char *>(strings) + off;
        return std::string(str, strnlen(str, strsz - off));
    };
    auto symbol_at = [&](uint64_t index) -> const sym_t * {
        if (!has_symtab || syment < sizeof(sym_t)) return nullptr;
        return reinterpret_cast<const sym_t *>(
            img.data(symtab + index * syment, sizeof(sym_t)));
    };

    for (auto &t : img.tags)
        if (t.first == ELF::DT_NEEDED) {
            auto name = string_at(t.second);
            if (!name.empty()) s.entry("require") << name;
        }

    std::vector<dynamic_relocation> relocs;
    uint64_t addr, size;
    if (img.tag(ELF::DT_RELA, addr) && img.tag(ELF::DT_RELASZ, size))
        read_relocations(img, addr, size, true, relocs);
    if (img.tag(ELF::DT_REL, addr) && img.tag(ELF::DT_RELSZ, size))
        read_relocations(img, addr, size, false, relocs);
    if (img.tag(ELF::DT_JMPREL, addr) && img.tag(ELF::DT_PLTRELSZ, size)) {
        uint64_t pltrel;
        bool rela = img.tag(ELF::DT_PLTREL, pltrel)
            ? pltrel == ELF::DT_RELA
            : img.tag(ELF::DT_RELA, pltrel);
        read_relocations(img, addr, size, rela, relocs);
    }
    if (img.tag(ELF::DT_ANDROID_RELA, addr) && img.tag(ELF::DT_ANDROID_RELASZ, size))
        read_android_relocations(img, addr, size, true, relocs);
    if (img.tag(ELF::DT_ANDROID_REL, addr) && img.tag(ELF::DT_ANDROID_RELSZ, size))
        read_android_relocations(img, addr, size, false, relocs);
    if (img.tag(ELF::DT_RELR, addr) && img.tag(ELF::DT_RELRSZ, size))
        read_relr_relocations(img, addr, size, relocs);
    if (img.tag(ELF::DT_ANDROID_RELR, addr) && img.tag(ELF::DT_ANDROID_RELRSZ, size))
        read_relr_relocations(img, addr, size, relocs);

    uint64_t machine = elf_machine(elf);
    uint64_t relative = elf.getRelativeRelocationType();
    uint64_t irelative = irelative_relocation_type(machine);

    if (obj.dynamic_symbol_begin() == obj.dynamic_symbol_end()) {
        uint64_t count = dynamic_symbol_count(img);
        for (uint64_t i = 1; i < count; ++i) {
            auto sym = symbol_at(i);
            if (!sym) break;
            uint64_t off;
            if (sym->getType() != ELF::STT_FUNC ||
                sym->st_shndx == ELF::SHN_UNDEF || !sym->st_value)
                continue;
            uint64_t addr = sym->st_value;
            if (machine == ELF::EM_ARM)
                addr &= ~uint64_t(1);
            auto name = string_at(sym->st_name);
            if (name.empty() || !img.offset_of(addr, 0, off))
                continue;
            s.entry("llvm:symbol-entry") << name << addr << uint64_t(sym->st_size)
                                         << off << uint64_t(sym->st_value);
            s.entry("llvm:code-entry") << name << off << uint64_t(sym->st_size);
        }
    }

    // the contents of the word at the place, if it is in the file
    auto stored = [&](uint64_t place, uint64_t &off, uint64_t &value) {
        if (!img.offset_of(place, sizeof(word), off)) return false;
        value = *reinterpret_cast<const word *>(elf.base() + off);
        return true;
    };
    for (auto &rel : relocs) {
        uint64_t off = 0, value = 0;
        if (rel.symbol == 0) {
            bool in_file = stored(rel.offset, off, value);
            uint64_t addend = rel.explicit_addend ? uint64_t(rel.addend) : value;
            if (irelative && rel.type == irelative) {
                if (rel.explicit_addend || in_file)
                    s.entry("llvm:irelative-relocation") << rel.offset << addend;
                continue;
            }
            if (rel.type != relative) continue;
            s.entry("llvm:relative-relocation") << rel.offset;
            if (rel.explicit_addend || in_file)
                s.entry("llvm:relative-target") << addend;
            if (rel.explicit_addend && in_file && value != addend)
                s.entry("llvm:elf-relative-addend") << off << addend;
            continue;
        }
        auto sym = symbol_at(rel.symbol);
        if (!sym) continue;
        auto typ = sym->getType();
        // a slot of an indirect function defined in the file holds the
        // address that its resolver returns, as an IRELATIVE one does
        if (typ == ELF::STT_GNU_IFUNC && sym->st_shndx != ELF::SHN_UNDEF &&
            kind_of_relocation(machine, rel.type, T::Is64Bits) != symbol_relocation::none) {
            s.entry("llvm:irelative-relocation") << rel.offset << uint64_t(sym->st_value);
            continue;
        }
        if (typ != ELF::STT_NOTYPE && typ != ELF::STT_OBJECT &&
            typ != ELF::STT_FUNC && typ != ELF::STT_COMMON)
            continue;
        auto name = string_at(sym->st_name);
        if (!name.empty())
            s.entry("llvm:name-reference") << rel.offset << name;
        if (sym->st_shndx == ELF::SHN_UNDEF) continue;
        auto kind = kind_of_relocation(machine, rel.type, T::Is64Bits);
        if (kind == symbol_relocation::none) continue;
        uint64_t addend = uint64_t(rel.addend);
        if (!rel.explicit_addend)
            addend = (kind == symbol_relocation::absolute &&
                      stored(rel.offset, off, value)) ? value : 0;
        uint64_t target = sym->st_value;
        // the Thumb bit is cleared, as LLVM does for the symbol addresses
        if (machine == ELF::EM_ARM && typ == ELF::STT_FUNC)
            target &= ~uint64_t(1);
        s.entry("llvm:relocation") << rel.offset << target + addend;
    }

    // the global entries of the GOT of MIPS, which the dynamic linker
    // fills without relocations, are of the dynamic symbols from
    // DT_MIPS_GOTSYM on, after the DT_MIPS_LOCAL_GOTNO local entries;
    // those of the data objects, that the file imports, e.g., stdin, are
    // their references, as the slots of GLOB_DAT are on the other targets
    uint64_t pltgot, local_gotno, gotsym, symtabno;
    if (machine == ELF::EM_MIPS && img.tag(ELF::DT_PLTGOT, pltgot) &&
        img.tag(ELF::DT_MIPS_LOCAL_GOTNO, local_gotno) &&
        img.tag(ELF::DT_MIPS_GOTSYM, gotsym) &&
        img.tag(ELF::DT_MIPS_SYMTABNO, symtabno)) {
        for (uint64_t i = gotsym; i < symtabno; ++i) {
            auto sym = symbol_at(i);
            if (!sym) break;
            if (sym->st_shndx != ELF::SHN_UNDEF || sym->getType() != ELF::STT_OBJECT)
                continue;
            auto name = string_at(sym->st_name);
            if (!name.empty())
                s.entry("llvm:name-reference")
                    << pltgot + (local_gotno + i - gotsym) * sizeof(word) << name;
        }
    }
    return true;
}

// Emits the thread-local storage template (PT_TLS) and the address of
// the program headers in memory, which a loader passes to the program
// (AT_PHDR). The address is the one of PT_PHDR, or the address of the
// loadable segment that contains the headers in the file.
template <typename T>
void emit_runtime_layout(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto &elf = obj.getELFFile();
    auto hdr = &elf.getHeader();
#else
    auto &elf = *obj.getELFFile();
    auto hdr = elf.getHeader();
#endif
    dynamic_image<T> img(elf);
    bool has_phdrs = false;
    uint64_t phdrs = 0;
    for (auto &seg : img.segments) {
        if (seg.p_type == ELF::PT_TLS)
            s.entry("llvm:elf-tls") << uint64_t(seg.p_vaddr) << uint64_t(seg.p_memsz)
                                    << uint64_t(seg.p_filesz) << uint64_t(seg.p_align);
        if (seg.p_type == ELF::PT_PHDR) {
            has_phdrs = true;
            phdrs = seg.p_vaddr;
        }
    }
    uint64_t size = uint64_t(hdr->e_phentsize) * hdr->e_phnum;
    for (auto &seg : img.segments) {
        if (has_phdrs) break;
        if (seg.p_type == ELF::PT_LOAD && hdr->e_phoff >= seg.p_offset &&
            hdr->e_phoff - seg.p_offset <= seg.p_filesz &&
            seg.p_filesz - (hdr->e_phoff - seg.p_offset) >= size) {
            has_phdrs = true;
            phdrs = seg.p_vaddr + (hdr->e_phoff - seg.p_offset);
        }
    }
    if (has_phdrs && hdr->e_phnum)
        s.entry("llvm:elf-program-header-table") << phdrs << uint64_t(hdr->e_phentsize)
                                                 << uint64_t(hdr->e_phnum);
}

// Relocatable files have no layout, so instead of interpreting them
// we describe their sections, symbols, and relocations as they are
// and leave the linking to the OCaml side.

template <typename T>
bool is_relocatable(const ELFObjectFile<T> &obj) {
#if LLVM_VERSION_MAJOR >= 12
    auto hdr = &obj.getELFFile().getHeader();
#else
    auto hdr = obj.getELFFile()->getHeader();
#endif
    return hdr->e_type == ELF::ET_REL;
}

template <typename T>
void emit_elf_header(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto hdr = &obj.getELFFile().getHeader();
#else
    auto hdr = obj.getELFFile()->getHeader();
#endif
    s.entry("llvm:elf-header")
        << uint64_t(hdr->e_type)
        << uint64_t(hdr->e_machine)
        << uint64_t(hdr->e_flags);
}

template <typename T>
error_or<std::string> raw_section_name(const ELFFile<T> &elf,
                                       const typename ELFFile<T>::Elf_Shdr &sec) {
#if LLVM_VERSION_MAJOR >= 12
    auto name = elf.getSectionName(sec);
#else
    auto name = elf.getSectionName(&sec);
#endif
    if (!name) return failure(toString(name.takeError()));
    return success(name->str());
}

template <typename T>
void emit_raw_sections(const ELFFile<T> &elf, tables &s) {
    auto secs = prim::elf_sections(elf);
    for (std::size_t i = 0; i < secs.size(); ++i) {
        auto &sec = secs[i];
        auto name = raw_section_name(elf, sec);
        s.entry("llvm:elf-section")
            << uint64_t(i)
            << (name ? *name : std::string(""))
            << uint64_t(sec.sh_type)
            << uint64_t(sec.sh_flags)
            << uint64_t(sec.sh_offset)
            << uint64_t(sec.sh_size)
            << uint64_t(sec.sh_addralign);
    }
}

// the extended section indices of the symbols of the symbol table
// [symtab], stored in the SHT_SYMTAB_SHNDX section that is linked to it.
// They are used when there are too many sections and the index of a
// symbol's section doesn't fit into st_shndx, which is then SHN_XINDEX.
template <typename T>
std::vector<uint64_t> extended_indices(const ELFFile<T> &elf,
                                       uint64_t symtab) {
    std::vector<uint64_t> indices;
    for (auto &sec : prim::elf_sections(elf)) {
        if (sec.sh_type != ELF::SHT_SYMTAB_SHNDX || sec.sh_link != symtab)
            continue;
        typedef typename ELFFile<T>::Elf_Word word;
#if LLVM_VERSION_MAJOR >= 12
        auto table = elf.template getSectionContentsAsArray<word>(sec);
#else
        auto table = elf.template getSectionContentsAsArray<word>(&sec);
#endif
        if (!table) {
            consumeError(table.takeError());
            return indices;
        }
        for (auto &index : *table)
            indices.push_back(uint64_t(index));
        return indices;
    }
    return indices;
}

template <typename T>
void emit_raw_symbols(const ELFFile<T> &elf,
                      const typename ELFFile<T>::Elf_Shdr &symtab,
                      uint64_t symtab_index,
                      tables &s) {
    auto syms = elf.symbols(&symtab);
    if (!syms) {
        consumeError(syms.takeError());
        return;
    }
    auto strtab = elf.getStringTableForSymtab(symtab);
    if (!strtab) {
        consumeError(strtab.takeError());
        return;
    }
    auto xindices = extended_indices(elf, symtab_index);
    uint64_t index = 0;
    for (auto &sym : *syms) {
        std::string name;
        auto er_name = sym.getName(*strtab);
        if (er_name) name = er_name->str();
        else consumeError(er_name.takeError());
        uint64_t shndx = sym.st_shndx;
        bool extended =
            sym.st_shndx == ELF::SHN_XINDEX && index < xindices.size();
        if (extended)
            shndx = xindices[index];
        s.entry("llvm:elf-symbol")
            << index++
            << name
            << shndx
            << extended
            << uint64_t(sym.st_value)
            << uint64_t(sym.st_size)
            << uint64_t(sym.getType())
            << uint64_t(sym.getBinding());
    }
}

template <typename R>
void emit_raw_relocation(uint64_t &index, uint64_t section, const R &rel,
                         bool mips64el, int64_t addend, bool explicit_addend,
                         tables &s) {
    s.entry("llvm:elf-relocation")
        << index++
        << section
        << uint64_t(rel.r_offset)
        << uint64_t(rel.getType(mips64el))
        << uint64_t(rel.getSymbol(mips64el))
        << uint64_t(addend)
        << explicit_addend;
}

// emits the relocations of the relocation section [sec]. A relocatable
// file has only one symbol table, so the symbol indices are not
// qualified with the symbol table of the relocation section.
template <typename T>
void emit_raw_relocations(const ELFFile<T> &elf,
                          const std::vector<typename ELFFile<T>::Elf_Shdr> &sections,
                          const typename ELFFile<T>::Elf_Shdr &sec,
                          uint64_t &index,
                          tables &s) {
    bool mips64el = elf.isMips64EL();
    uint64_t target = sec.sh_info;
    if (sec.sh_type != ELF::SHT_RELA && sec.sh_type != ELF::SHT_REL)
        return;
    // the relocations of the sections that are not loaded into memory,
    // e.g., the debug information, are ignored by the linker
    if (target >= sections.size() ||
        !(sections[target].sh_flags & ELF::SHF_ALLOC))
        return;
    if (sec.sh_type == ELF::SHT_RELA) {
#if LLVM_VERSION_MAJOR >= 12
        auto rels = elf.relas(sec);
#else
        auto rels = elf.relas(&sec);
#endif
        if (!rels) {
            consumeError(rels.takeError());
            return;
        }
        for (auto &rel : *rels)
            emit_raw_relocation(index, target, rel, mips64el,
                                int64_t(rel.r_addend), true, s);
    } else if (sec.sh_type == ELF::SHT_REL) {
#if LLVM_VERSION_MAJOR >= 12
        auto rels = elf.rels(sec);
#else
        auto rels = elf.rels(&sec);
#endif
        if (!rels) {
            consumeError(rels.takeError());
            return;
        }
        for (auto &rel : *rels)
            emit_raw_relocation(index, target, rel, mips64el, 0, false, s);
    }
}

template <typename T>
void emit_relocatable(const ELFObjectFile<T> &obj, tables &s) {
#if LLVM_VERSION_MAJOR >= 12
    auto &elf = obj.getELFFile();
#else
    auto &elf = *obj.getELFFile();
#endif
    emit_raw_sections(elf, s);
    auto sections = prim::elf_sections(elf);
    uint64_t index = 0;
    for (std::size_t i = 0; i < sections.size(); ++i) {
        auto &sec = sections[i];
        if (sec.sh_type == ELF::SHT_SYMTAB)
            emit_raw_symbols(elf, sec, i, s);
        emit_raw_relocations(elf, sections, sec, index, s);
    }
}

} // namespace elf_loader

template <typename T>
error_or<std::string> load(tables &s, const llvm::object::ELFObjectFile<T> &obj) {
    using namespace elf_loader;
    s.entry("format") << "elf";
    s.entry("llvm:base-address") << base_address(obj);
    s.entry("is-executable") << is_executable(obj);
    emit_elf_header(obj, s);
    emit_entry_point(obj, s);
    emit_program_headers(obj, s);
    if (is_relocatable(obj)) {
        emit_relocatable(obj, s);
    } else {
        emit_section_headers(obj, s);
        emit_symbol_entries(obj, s);
        if (!emit_dynamic_relocations(obj, s))
            emit_relocations(obj, s);
        emit_runtime_layout(obj, s);
    }
    return s.str();
}

} // namespace loader

#endif // LLVM_ELF_LOADER_HPP
