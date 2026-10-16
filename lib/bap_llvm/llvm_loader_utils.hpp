#ifndef LLVM_LOADER_UTILS_HPP
#define LLVM_LOADER_UTILS_HPP

#include <cstdint>
#include <cstring>
#include <string>
#include <type_traits>
#include <unordered_map>
#include <vector>

#if LLVM_VERSION_MAJOR >= 17
#include <llvm/TargetParser/Triple.h>
#else
#include <llvm/ADT/Triple.h>
#endif

#include <llvm/ADT/StringRef.h>

#include "llvm_error_or.hpp"

namespace loader {

using namespace llvm;

// tables
// collects the facts discovered by a loader into named tables, which
// are passed to the OCaml side in a binary form, see Bap_llvm_tables.
// A fact is added as a row of the table with the given name:
// ...
// doc.entry("llvm:section-entry") << name << addr << size << off;
// ...
// The first row of a table defines the types of its fields (an
// integer, a boolean, or a string), and the following rows must have
// the same types, otherwise the document fails.
//
// An integer is stored as the 64-bit pattern of its unsigned value,
// e.g., an int -1 is 0xffffffff. Character-sized integers are
// rejected, since they are ambiguous, and should be converted to
// another type explicitly.
//
// The binary form is, all numbers are little endian:
//
// document ::= "BAPT" <version:u32> <ntables:u32> <table>* <pool>
// table    ::= <name:str> <nfields:u32> <type:u8>* <nrows:u32>
//              <size:u64> <row>*
// row      ::= <field>*, where a field is an integer (u64), a
//              boolean (u8), or a string (offset:u32, length:u32)
//              in the pool
// pool     ::= <size:u64> <byte>*
// str      ::= <length:u32> <byte>*
struct tables {
    enum type : uint8_t { Int = 0, Bool = 1, Str = 2 };

    static const uint32_t version = 1;

    explicit tables() : row_(nullptr), field_(0), failed_(false) {}

    void fail(const std::string &m) {
        if (!failed_) {
            failed_ = true;
            message_ = m;
        }
    }

    tables & entry(const std::string &name) {
        close();
        auto it = index_.find(name);
        if (it == index_.end()) {
            it = index_.emplace(name, tables_.size()).first;
            tables_.push_back(table(name));
        }
        row_ = &tables_[it->second];
        field_ = 0;
        return *this;
    }

    // only a bool is a boolean, the values of other types are never
    // converted to a boolean implicitly
    template <typename T>
    friend typename std::enable_if<std::is_same<T, bool>::value, tables &>::type
    operator<<(tables &d, const T &x) {
        if (d.field(Bool)) d.row_->data.push_back(x ? 1 : 0);
        return d;
    }

    template <typename T>
    friend typename std::enable_if<(std::is_integral<T>::value &&
                                    !std::is_same<T, bool>::value) ||
                                   std::is_enum<T>::value, tables &>::type
    operator<<(tables &d, const T &x) {
        return d.integer(x);
    }

    // an integer of a file, e.g., ELF's Elf_Addr, which is stored with
    // the endianness of the file and converts to its value_type
    template <typename T>
    friend typename std::enable_if<
        std::is_class<T>::value &&
        std::is_integral<typename T::value_type>::value, tables &>::type
    operator<<(tables &d, const T &x) {
        return d.integer(typename T::value_type(x));
    }

    friend tables & operator<<(tables &d, const std::string &x) {
        if (d.field(Str)) {
            put32(d.row_->data, uint32_t(d.pool_.size()));
            put32(d.row_->data, uint32_t(x.size()));
            d.pool_ += x;
        }
        return d;
    }

    friend tables & operator<<(tables &d, const char *x) {
        return d << std::string(x);
    }

    friend tables & operator<<(tables &d, const llvm::StringRef &x) {
        return d << x.str();
    }

    // a fixed-size name, e.g., the segment name of a Mach-O load
    // command, which is not terminated if it occupies the whole array
    template <std::size_t N>
    friend tables & operator<<(tables &d, const char (&x)[N]) {
        return d << std::string(x, strnlen(x, N));
    }

    error_or<std::string> str() {
        close();
        if (failed_) return failure(message_);
        std::string out("BAPT");
        put32(out, version);
        put32(out, uint32_t(tables_.size()));
        for (auto &t : tables_) {
            put32(out, uint32_t(t.name.size()));
            out += t.name;
            put32(out, uint32_t(t.types.size()));
            out.append(t.types.begin(), t.types.end());
            put32(out, t.rows);
            put64(out, t.data.size());
            out += t.data;
        }
        put64(out, pool_.size());
        out += pool_;
        return success(out);
    }

private:
    struct table {
        explicit table(const std::string &name) : name(name), rows(0) {}
        std::string name;
        std::vector<uint8_t> types;
        uint32_t rows;
        std::string data;
    };

    template <typename T>
    tables & integer(const T &x) {
        typedef typename std::conditional<std::is_enum<T>::value,
                                          std::underlying_type<T>,
                                          std::enable_if<true, T>>::type::type
            integral;
        static_assert(sizeof(integral) > 1,
                      "convert a character-sized integer explicitly");
        typedef typename std::make_unsigned<integral>::type unsigned_t;
        if (field(Int)) put64(row_->data, uint64_t(unsigned_t(x)));
        return *this;
    }

    // checks the type of the next field of the current row
    bool field(type t) {
        if (failed_) return false;
        if (!row_) {
            fail("a field is added before any entry");
            return false;
        }
        if (row_->rows == 0) {
            row_->types.push_back(t);
        } else if (field_ >= row_->types.size() || row_->types[field_] != t) {
            fail("the entry " + row_->name + " has a field " +
                 std::to_string(field_) + " of a wrong type");
            return false;
        }
        ++field_;
        return true;
    }

    void close() {
        if (!row_ || failed_) return;
        if (row_->rows > 0 && field_ != row_->types.size())
            fail("the entry " + row_->name + " has " + std::to_string(field_) +
                 " fields instead of " + std::to_string(row_->types.size()));
        ++row_->rows;
        row_ = nullptr;
    }

    static void put32(std::string &s, uint32_t x) {
        for (int i = 0; i < 4; ++i) s.push_back(char((x >> (8 * i)) & 0xff));
    }

    static void put64(std::string &s, uint64_t x) {
        for (int i = 0; i < 8; ++i) s.push_back(char((x >> (8 * i)) & 0xff));
    }

private:
    std::vector<table> tables_;
    std::unordered_map<std::string, std::size_t> index_;
    std::string pool_;
    table *row_;
    std::size_t field_;
    bool failed_;
    std::string message_;
};

} // namespace loader

#endif // LLVM_LOADER_UTILS_HPP
