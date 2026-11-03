#include <lean/lean.h>

#include <llvm/ExecutionEngine/Orc/AbsoluteSymbols.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/SwapByteOrder.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <limits>
#include <malloc.h>
#include <memory>
#include <new>
#include <mutex>
#include <string>
#include <vector>

#if defined(__linux__)
#include <sys/mman.h>
#include <unistd.h>
#endif

#include "paged_memory.h"

class CellMap {
  struct Slot {
    uint64_t address = 0;
    uint8_t value = 0;
    bool occupied = false;
  };

  std::vector<Slot> slots;
  size_t count = 0;

  static uint64_t hash(uint64_t value) {
    return (value * 0x9e3779b97f4a7c15ULL) ^ (value >> 29);
  }

  void rehash(size_t capacity) {
    size_t size = 16;
    while (size < capacity)
      size *= 2;
    std::vector<Slot> previous = std::move(slots);
    slots.clear();
    slots.resize(size);
    count = 0;
    for (const auto &slot : previous)
      if (slot.occupied)
        set(slot.address, slot.value);
  }

public:
  uint8_t get(uint64_t address) const {
    if (slots.empty())
      return 0;
    size_t index = hash(address) & (slots.size() - 1);
    while (slots[index].occupied) {
      if (slots[index].address == address)
        return slots[index].value;
      index = (index + 1) & (slots.size() - 1);
    }
    return 0;
  }

  void set(uint64_t address, uint8_t value) {
    if (slots.empty())
      rehash(16);
    if ((count + 1) * 10 >= slots.size() * 7)
      rehash(slots.size() * 2);
    size_t index = hash(address) & (slots.size() - 1);
    while (slots[index].occupied) {
      if (slots[index].address == address) {
        slots[index].value = value;
        return;
      }
      index = (index + 1) & (slots.size() - 1);
    }
    slots[index] = Slot{address, value, true};
    ++count;
  }

  void reserve(size_t capacity) {
    if (capacity * 2 > slots.size())
      rehash(capacity * 2);
  }

  size_t size() const { return count; }

  template <typename F> void forEach(F &&action) const {
    for (const auto &slot : slots)
      if (slot.occupied)
        action(slot.address, slot.value);
  }
};

struct BapCell {
  uint64_t address;
  uint8_t value;
};

// A store that a run made, to say at its end what it changed. Keeping these and not a table of bytes is what lets a store be one
// instruction and one call.
struct StoreRecord {
  uint64_t address;
  uint64_t value;
  uint8_t size;
  uint8_t bigEndian;
};

// Where a run last found the pages. A tag is one more than the number of a page, so that 0 is an entry that holds nothing. A run has
// its own, so that this needs no synchronization, and the code that a program is compiled to reads it.
struct BapPageEntry {
  uint64_t tag;
  uint8_t *page;
};
constexpr size_t pageEntryCount = 64;
static_assert(sizeof(BapPageEntry) == 16, "compiled code goes through these by index");

struct BapCells {
  BapCell *items;
  size_t size;
  size_t capacity;
  lean_object *observer;
  lean_object *error;
  PagedMemory *pages;
  std::vector<StoreRecord> *changes;
  lean_object *codeObserver;
  BapPageEntry pageEntries[pageEntryCount] = {};
};

// Once there is an error nothing takes effect, and with nothing here compiled code goes to `bap_jit_memory_page`, which says so.
static void failCells(BapCells *cells, lean_object *error) {
  cells->error = error;
  lean_inc_ref(error);
  std::memset(cells->pageEntries, 0, sizeof(cells->pageEntries));
}

extern "C" void bap_jit_memory_notify(BapCells *cells, uint8_t write,
                                      uint64_t address, uint64_t size,
                                      uint64_t value) {
  if (cells->observer == nullptr || cells->error != nullptr)
    return;
  lean_inc_ref(cells->observer);
  lean_object *action = lean_apply_1(cells->observer, lean_box(write));
  action = lean_apply_1(action, lean_uint64_to_nat(address));
  action = lean_apply_1(action, lean_uint64_to_nat(size));
  action = lean_apply_1(action, lean_uint64_to_nat(value));
  lean_object *result = lean_apply_1(action, lean_io_mk_world());
  if (lean_io_result_is_error(result))
    failCells(cells, lean_io_result_get_error(result));
  lean_dec_ref(result);
}

extern "C" uint64_t bap_jit_code_notify(BapCells *cells, uint64_t pc) {
  if (cells->codeObserver == nullptr || cells->error != nullptr)
    return cells->error == nullptr ? 0 : 1;
  lean_inc_ref(cells->codeObserver);
  lean_object *action = lean_apply_1(cells->codeObserver, lean_uint64_to_nat(pc));
  lean_object *result = lean_apply_1(action, lean_io_mk_world());
  uint64_t stop = 0;
  if (lean_io_result_is_error(result)) {
    failCells(cells, lean_io_result_get_error(result));
    stop = 1;
  } else {
    stop = lean_unbox(lean_io_result_get_value(result));
  }
  lean_dec_ref(result);
  return stop;
}

static uint8_t loadByte(BapCells *cells, uint64_t address) {
  for (size_t index = 0; index != cells->size; ++index)
    if (cells->items[index].address == address)
      return cells->items[index].value;
  return 0;
}

static void storeByte(BapCells *cells, uint64_t address, uint8_t value) {
  for (size_t index = 0; index != cells->size; ++index) {
    if (cells->items[index].address == address) {
      cells->items[index].value = value;
      return;
    }
  }
  if (cells->size < cells->capacity)
    cells->items[cells->size++] = BapCell{address, value};
}

// The way of what no instruction does: an access that isn't aligned or that has a size no instruction has, or one on a page that
// isn't there, or a run without pages.
extern "C" uint64_t bap_jit_memory_load_bytes(BapCells *cells, uint64_t address, uint64_t size, uint8_t bigEndian) {
  if (cells->error != nullptr)
    return 0;
  uint8_t bytes[8];
  if (cells->pages != nullptr)
    cells->pages->load(address, static_cast<size_t>(size), bytes);
  else
    for (uint64_t index = 0; index != size; ++index)
      bytes[index] = loadByte(cells, address + index);
  uint64_t result = 0;
  for (uint64_t index = 0; index != size; ++index)
    result |= static_cast<uint64_t>(bytes[index]) << ((bigEndian != 0 ? size - 1 - index : index) * 8);
  return result;
}

extern "C" void bap_jit_memory_note(BapCells *cells, uint64_t address, uint64_t size, uint8_t bigEndian, uint64_t value) {
  if (cells->changes != nullptr)
    cells->changes->push_back(StoreRecord{address, value, static_cast<uint8_t>(size), bigEndian});
}

extern "C" void bap_jit_memory_store_bytes(BapCells *cells, uint64_t address, uint64_t size, uint8_t bigEndian, uint64_t value) {
  if (cells->error != nullptr)
    return;
  uint8_t bytes[8];
  for (uint64_t index = 0; index != size; ++index)
    bytes[index] = static_cast<uint8_t>(value >> ((bigEndian != 0 ? size - 1 - index : index) * 8));
  if (cells->pages != nullptr)
    cells->pages->store(address, static_cast<size_t>(size), bytes);
  else
    for (uint64_t index = 0; index != size; ++index)
      storeByte(cells, address + index, bytes[index]);
  bap_jit_memory_note(cells, address, size, bigEndian, value);
}

// The page of an address for the code of a run, which remembers it, or nothing if it has to go the other way. Only a store makes a
// page: reading what was never written doesn't need one, and a program that reads a lot of nothing shouldn't come to hold a lot of it.
extern "C" uint8_t *bap_jit_memory_page(BapCells *cells, uint64_t address, uint8_t write) {
  if (cells->pages == nullptr || cells->error != nullptr)
    return nullptr;
  uint8_t *page = write != 0 ? cells->pages->ensure(address) : cells->pages->find(address);
  if (page == nullptr)
    return nullptr;
  uint64_t number = address >> PagedMemory::pageBits;
  cells->pageEntries[number & (pageEntryCount - 1)] = BapPageEntry{number + 1, page};
  return page;
}

namespace {

struct SharedJit {
  std::shared_ptr<llvm::orc::LLJIT> jit;
  std::mutex mutex;
};

struct Program {
  std::shared_ptr<SharedJit> shared;
  llvm::orc::ResourceTrackerSP resources;
  uint64_t (*function)(uint64_t *, BapCells *) = nullptr;
  size_t maxSlot = 0;
  size_t memoryStores = 0;

  ~Program() {
    if (shared == nullptr || resources == nullptr)
      return;
    std::lock_guard<std::mutex> lock(shared->mutex);
    if (llvm::Error error = resources->remove())
      llvm::consumeError(std::move(error));
  }
};

// One for each thread: code generation holds the mutex of its JIT, so that threads that shared one would compile one at a time,
// however many processors there are. A program keeps its JIT alive, and may run or be freed on any thread.
std::shared_ptr<SharedJit> sharedJit(bool optimized) {
  thread_local std::shared_ptr<SharedJit> fast;
  thread_local std::shared_ptr<SharedJit> full;
  std::shared_ptr<SharedJit> &shared = optimized ? full : fast;
  if (shared != nullptr)
    return shared;
  static std::mutex creation;
  std::lock_guard<std::mutex> lock(creation);
  auto machine = llvm::orc::JITTargetMachineBuilder::detectHost();
  if (!machine)
    throw std::runtime_error("LLVM ORC JIT host detection failed: " +
                             llvm::toString(machine.takeError()));
  // Most of a program runs few times, and what compiling takes is what that comes to: without optimizing it is a ninth. What
  // then runs a lot is compiled again with it.
  machine->setCodeGenOptLevel(optimized ? llvm::CodeGenOptLevel::Default : llvm::CodeGenOptLevel::None);
  auto jit = llvm::orc::LLJITBuilder().setJITTargetMachineBuilder(std::move(*machine)).create();
  if (!jit)
    throw std::runtime_error("LLVM ORC JIT creation failed: " +
                             llvm::toString(jit.takeError()));
  llvm::orc::SymbolMap runtimeSymbols;
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_load_bytes")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_load_bytes);
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_store_bytes")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_store_bytes);
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_note")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_note);
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_page")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_page);
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_notify")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_notify);
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_code_notify")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_code_notify);
  if (llvm::Error error = (*jit)->getMainJITDylib().define(
          llvm::orc::absoluteSymbols(std::move(runtimeSymbols))))
    throw std::runtime_error("LLVM ORC symbol definition failed: " +
                             llvm::toString(std::move(error)));
  shared = std::make_shared<SharedJit>();
  shared->jit = std::move(*jit);
  return shared;
}

lean_obj_res ioError(const std::string &message) {
  return lean_io_result_mk_error(
      lean_mk_io_error_other_error(0, lean_mk_string(message.c_str())));
}

void finalizeProgram(void *data) { delete static_cast<Program *>(data); }

void foreachProgram(void *, b_lean_obj_arg) {}

lean_external_class *programClass() {
  static lean_external_class *cls =
      lean_register_external_class(finalizeProgram, foreachProgram);
  return cls;
}

bool initialize(std::string &error) {
  static std::once_flag flag;
  static bool initialized = false;
  std::call_once(flag, [&] {
    if (llvm::InitializeNativeTarget()) {
      error = "LLVM has no native JIT target";
      return;
    }
    if (llvm::InitializeNativeTargetAsmPrinter()) {
      error = "LLVM has no native assembly printer";
      return;
    }
    if (llvm::InitializeNativeTargetAsmParser()) {
      error = "LLVM has no native assembly parser";
      return;
    }
    initialized = true;
  });
  return initialized;
}

bool getSlot(lean_obj_arg value, size_t &slot) {
  if (!lean_is_scalar(value))
    return false;
  uint64_t raw = lean_unbox(value);
  if (raw > static_cast<uint64_t>(std::numeric_limits<int32_t>::max() /
                                  sizeof(uint64_t)))
    return false;
  slot = static_cast<size_t>(raw);
  return true;
}

} // namespace

// With ENTRIES, a list of labels, the program starts at the label that the slot ENTRY_SLOT says, as one more than it, and where
// it would otherwise when that holds zero.
static lean_obj_res compileOps(lean_obj_arg ops, bool optimized, lean_obj_arg entries = nullptr, size_t entrySlot = 0) {
  try {
    std::string initializationError;
    if (!initialize(initializationError))
      return ioError(initializationError);

    static std::atomic<uint64_t> nextProgramId{1};
    const uint64_t programId = nextProgramId.fetch_add(1);
    const std::string functionName = "bap_block_" + std::to_string(programId);
    auto context = std::make_unique<llvm::LLVMContext>();
    auto module = std::make_unique<llvm::Module>("bap_jit_" + std::to_string(programId), *context);
    llvm::Type *word = llvm::Type::getInt64Ty(*context);
    llvm::Type *pointer = llvm::PointerType::get(*context, 0);
    llvm::FunctionType *type =
        llvm::FunctionType::get(word, {pointer, pointer}, false);
    llvm::Function *function = llvm::Function::Create(
        type, llvm::Function::ExternalLinkage, functionName, *module);
    llvm::BasicBlock *entry =
        llvm::BasicBlock::Create(*context, "entry", function);
    llvm::IRBuilder<> builder(entry);
    llvm::Value *state = function->getArg(0);
    llvm::Value *memory = function->getArg(1);
    llvm::Value *zero = llvm::ConstantInt::get(word, 0);
    llvm::Type *byte = llvm::Type::getInt8Ty(*context);
    llvm::Type *voidType = llvm::Type::getVoidTy(*context);
    llvm::FunctionCallee loadBytes = module->getOrInsertFunction(
        "bap_jit_memory_load_bytes", llvm::FunctionType::get(word, {pointer, word, word, byte}, false));
    llvm::FunctionCallee storeBytes = module->getOrInsertFunction(
        "bap_jit_memory_store_bytes", llvm::FunctionType::get(voidType, {pointer, word, word, byte, word}, false));
    llvm::FunctionCallee noteStore = module->getOrInsertFunction(
        "bap_jit_memory_note", llvm::FunctionType::get(voidType, {pointer, word, word, byte, word}, false));
    llvm::FunctionCallee pageOf = module->getOrInsertFunction(
        "bap_jit_memory_page", llvm::FunctionType::get(pointer, {pointer, word, byte}, false));
    llvm::FunctionCallee notifyMemory = module->getOrInsertFunction(
        "bap_jit_memory_notify",
        llvm::FunctionType::get(llvm::Type::getVoidTy(*context),
                                {pointer, byte, word, word, word}, false));
    llvm::FunctionCallee notifyCode = module->getOrInsertFunction(
        "bap_jit_code_notify",
        llvm::FunctionType::get(word, {pointer, word}, false));

    auto pointerTo = [&](size_t slot) {
      return builder.CreateConstGEP1_64(word, state, slot);
    };
    // Whether a size is that of an instruction of the host, which is atomic at an address that is a multiple of it.
    auto hasInstruction = [](size_t size) { return size == 1 || size == 2 || size == 4 || size == 8; };
    // The page of an access that an instruction can do, if the page can be had: ends with the insertion point where the access
    // is, with the page in hand, and `slow` where it isn't.
    auto pageForAccess = [&](llvm::Value *base, size_t size, bool write, llvm::BasicBlock *slow) -> llvm::Value * {
      llvm::Value *aligned = builder.CreateICmpEQ(
          builder.CreateAnd(base, llvm::ConstantInt::get(word, size - 1)), zero);
      llvm::Value *number = builder.CreateLShr(base, PagedMemory::pageBits);
      llvm::Value *index = builder.CreateAnd(number, llvm::ConstantInt::get(word, pageEntryCount - 1));
      llvm::Value *entryAddress = builder.CreateGEP(byte, memory, builder.CreateAdd(
          llvm::ConstantInt::get(word, offsetof(BapCells, pageEntries)),
          builder.CreateMul(index, llvm::ConstantInt::get(word, sizeof(BapPageEntry)))));
      llvm::Value *tag = builder.CreateLoad(word, entryAddress);
      llvm::Value *known = builder.CreateICmpEQ(tag, builder.CreateAdd(number, llvm::ConstantInt::get(word, 1)));
      llvm::BasicBlock *hit = llvm::BasicBlock::Create(*context, "page_known", function);
      llvm::BasicBlock *check = llvm::BasicBlock::Create(*context, "page_check", function);
      llvm::BasicBlock *miss = llvm::BasicBlock::Create(*context, "page_miss", function);
      llvm::BasicBlock *access = llvm::BasicBlock::Create(*context, "page_access", function);
      builder.CreateCondBr(builder.CreateAnd(aligned, known), hit, check);
      builder.SetInsertPoint(check);
      builder.CreateCondBr(aligned, miss, slow);
      builder.SetInsertPoint(hit);
      llvm::Value *knownPage = builder.CreateLoad(pointer, builder.CreateConstGEP1_64(byte, entryAddress, offsetof(BapPageEntry, page)));
      builder.CreateBr(access);
      builder.SetInsertPoint(miss);
      llvm::Value *foundPage = builder.CreateCall(pageOf, {memory, base, llvm::ConstantInt::get(byte, write ? 1 : 0)});
      builder.CreateCondBr(builder.CreateIsNull(foundPage), slow, access);
      builder.SetInsertPoint(access);
      llvm::PHINode *page = builder.CreatePHI(pointer, 2);
      page->addIncoming(knownPage, hit);
      page->addIncoming(foundPage, miss);
      return builder.CreateGEP(byte, page, builder.CreateAnd(base, llvm::ConstantInt::get(word, PagedMemory::pageSize - 1)));
    };
    auto swapped = [&](llvm::Value *value, size_t size, bool bigEndian) -> llvm::Value * {
      if (size == 1 || bigEndian == llvm::sys::IsBigEndianHost)
        return value;
      return builder.CreateUnaryIntrinsic(llvm::Intrinsic::bswap, value);
    };
    auto load = [&](size_t slot) {
      return builder.CreateLoad(word, pointerTo(slot));
    };
    auto store = [&](size_t slot, llvm::Value *value) {
      builder.CreateStore(value, pointerTo(slot));
    };

    size_t maxSlot = 0;
    size_t memoryStores = 0;
    bool hasSlots = false;
    auto noteSlot = [&](size_t slot) {
      maxSlot = hasSlots ? std::max(maxSlot, slot) : slot;
      hasSlots = true;
    };
    std::unordered_map<size_t, llvm::BasicBlock *> labels;
    for (lean_obj_arg rest = ops; !lean_is_scalar(rest);
         rest = lean_ctor_get(rest, 1)) {
      lean_obj_arg op = lean_ctor_get(rest, 0);
      if (lean_ptr_tag(op) == 12) {
        size_t id;
        if (!getSlot(lean_ctor_get(op, 0), id))
          return ioError("invalid JIT label");
        if (!labels.emplace(id, llvm::BasicBlock::Create(*context, "label", function)).second)
          return ioError("duplicate JIT label");
      }
    }
    auto findLabel = [&](size_t id) -> llvm::BasicBlock * {
      auto found = labels.find(id);
      return found == labels.end() ? nullptr : found->second;
    };

    size_t count = 0;
    for (lean_obj_arg rest = ops; !lean_is_scalar(rest);
         rest = lean_ctor_get(rest, 1), ++count) {
      lean_obj_arg op = lean_ctor_get(rest, 0);
      if (lean_ptr_tag(op) != 12 && builder.GetInsertBlock()->hasTerminator())
        return ioError("JIT operation follows a terminator");
      switch (lean_ptr_tag(op)) {
      case 0: {
        size_t dst;
        if (!getSlot(lean_ctor_get(op, 0), dst))
          return ioError("JIT destination slot is too large");
        store(dst, llvm::ConstantInt::get(
                       word, lean_ctor_get_uint64(op, sizeof(void *))));
        noteSlot(dst);
        break;
      }
      case 1: {
        size_t dst, src;
        if (!getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), src))
          return ioError("JIT move slot is too large");
        store(dst, load(src));
        noteSlot(dst);
        noteSlot(src);
        break;
      }
      case 2: {
        size_t dst, src;
        if (!getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), src))
          return ioError("JIT addition slot is too large");
        llvm::Value *immediate = llvm::ConstantInt::get(
            word, lean_ctor_get_uint64(op, 2 * sizeof(void *)));
        store(dst, builder.CreateAdd(load(src), immediate));
        noteSlot(dst);
        noteSlot(src);
        break;
      }
      case 3:
        builder.CreateRet(llvm::ConstantInt::get(
            word, lean_ctor_get_uint64(op, 0)));
        break;
      case 4: {
        size_t src;
        if (!getSlot(lean_ctor_get(op, 0), src))
          return ioError("JIT jump slot is too large");
        builder.CreateRet(load(src));
        noteSlot(src);
        break;
      }
      case 5: {
        size_t dst, leftSlot, rightSlot;
        unsigned binary = lean_ctor_get_uint8(op, 3 * sizeof(void *));
        if (binary > 21 ||
            !getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), leftSlot) ||
            !getSlot(lean_ctor_get(op, 2), rightSlot))
          return ioError("invalid JIT binary operation");
        llvm::Value *left = load(leftSlot);
        llvm::Value *right = load(rightSlot);
        llvm::Value *one = llvm::ConstantInt::get(word, 1);
        llvm::Value *ones = llvm::ConstantInt::get(word, UINT64_MAX);
        llvm::Value *result = nullptr;
        switch (binary) {
        case 0: result = builder.CreateAdd(left, right); break;
        case 1: result = builder.CreateSub(left, right); break;
        case 2: result = builder.CreateMul(left, right); break;
        case 3: result = builder.CreateAnd(left, right); break;
        case 4: result = builder.CreateOr(left, right); break;
        case 5: result = builder.CreateXor(left, right); break;
        case 6:
        case 7: {
          llvm::Value *large = builder.CreateICmpUGE(
              right, llvm::ConstantInt::get(word, 64));
          llvm::Value *amount = builder.CreateSelect(large, zero, right);
          llvm::Value *shifted = binary == 6 ? builder.CreateShl(left, amount)
                                             : builder.CreateLShr(left, amount);
          result = builder.CreateSelect(large, zero, shifted);
          break;
        }
        case 8:
        case 9:
        case 10:
        case 11:
        case 12:
        case 13:
        case 18:
        case 19:
        case 20:
        case 21: {
          llvm::CmpInst::Predicate predicate =
              binary == 8 ? llvm::CmpInst::ICMP_EQ
              : binary == 9 ? llvm::CmpInst::ICMP_NE
              : binary == 10 ? llvm::CmpInst::ICMP_ULT
              : binary == 11 ? llvm::CmpInst::ICMP_ULE
              : binary == 12 ? llvm::CmpInst::ICMP_UGT
              : binary == 13 ? llvm::CmpInst::ICMP_UGE
              : binary == 18 ? llvm::CmpInst::ICMP_SLT
              : binary == 19 ? llvm::CmpInst::ICMP_SLE
              : binary == 20 ? llvm::CmpInst::ICMP_SGT
                            : llvm::CmpInst::ICMP_SGE;
          result = builder.CreateZExt(builder.CreateICmp(predicate, left, right), word);
          break;
        }
        case 14:
        case 15: {
          llvm::Value *isZero = builder.CreateICmpEQ(right, zero);
          llvm::Value *divisor = builder.CreateSelect(isZero, one, right);
          llvm::Value *quotient = binary == 14 ? builder.CreateUDiv(left, divisor)
                                               : builder.CreateURem(left, divisor);
          result = builder.CreateSelect(isZero, binary == 14 ? ones : left, quotient);
          break;
        }
        case 16:
        case 17: {
          llvm::Value *isZero = builder.CreateICmpEQ(right, zero);
          llvm::Value *minimum = llvm::ConstantInt::get(word, uint64_t{1} << 63);
          llvm::Value *overflow = builder.CreateAnd(
              builder.CreateICmpEQ(left, minimum), builder.CreateICmpEQ(right, ones));
          llvm::Value *divisor = builder.CreateSelect(isZero, one, right);
          divisor = builder.CreateSelect(overflow, one, divisor);
          llvm::Value *quotient = binary == 16 ? builder.CreateSDiv(left, divisor)
                                               : builder.CreateSRem(left, divisor);
          result = builder.CreateSelect(overflow, binary == 16 ? left : zero, quotient);
          llvm::Value *byZero = builder.CreateSelect(builder.CreateICmpSLT(left, zero), one, ones);
          result = builder.CreateSelect(isZero, binary == 16 ? byZero : left, result);
          break;
        }
        }
        store(dst, result);
        noteSlot(dst);
        noteSlot(leftSlot);
        noteSlot(rightSlot);
        break;
      }
      case 6: {
        size_t dst, src;
        if (!getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), src))
          return ioError("JIT mask slot is too large");
        llvm::Value *immediate = llvm::ConstantInt::get(
            word, lean_ctor_get_uint64(op, 2 * sizeof(void *)));
        store(dst, builder.CreateAnd(load(src), immediate));
        noteSlot(dst);
        noteSlot(src);
        break;
      }
      case 7: {
        size_t width, dst, src;
        if (!getSlot(lean_ctor_get(op, 0), width) || width == 0 || width > 64 ||
            !getSlot(lean_ctor_get(op, 1), dst) ||
            !getSlot(lean_ctor_get(op, 2), src))
          return ioError("invalid JIT sign extension");
        llvm::Value *value = load(src);
        if (width < 64) {
          uint64_t shift = 64 - width;
          value = builder.CreateShl(value, shift);
          value = builder.CreateAShr(value, shift);
        }
        store(dst, value);
        noteSlot(dst);
        noteSlot(src);
        break;
      }
      case 8: {
        size_t dst, condition, yes, no;
        if (!getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), condition) ||
            !getSlot(lean_ctor_get(op, 2), yes) ||
            !getSlot(lean_ctor_get(op, 3), no))
          return ioError("invalid JIT select");
        store(dst, builder.CreateSelect(builder.CreateICmpNE(load(condition), zero),
                                        load(yes), load(no)));
        noteSlot(dst);
        noteSlot(condition);
        noteSlot(yes);
        noteSlot(no);
        break;
      }
      case 9:
      case 10: {
        size_t dst, src;
        if (!getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), src))
          return ioError("invalid JIT unary operation");
        llvm::Value *value = load(src);
        store(dst, lean_ptr_tag(op) == 9 ? builder.CreateNeg(value)
                                         : builder.CreateNot(value));
        noteSlot(dst);
        noteSlot(src);
        break;
      }
      case 11: {
        size_t width, dst, leftSlot, rightSlot;
        if (!getSlot(lean_ctor_get(op, 0), width) || width == 0 || width > 64 ||
            !getSlot(lean_ctor_get(op, 1), dst) ||
            !getSlot(lean_ctor_get(op, 2), leftSlot) ||
            !getSlot(lean_ctor_get(op, 3), rightSlot))
          return ioError("invalid JIT arithmetic shift");
        llvm::Value *right = load(rightSlot);
        llvm::Value *large = builder.CreateICmpUGE(
            right, llvm::ConstantInt::get(word, width));
        llvm::Value *amount = builder.CreateSelect(
            large, llvm::ConstantInt::get(word, width - 1), right);
        store(dst, builder.CreateAShr(load(leftSlot), amount));
        noteSlot(dst);
        noteSlot(leftSlot);
        noteSlot(rightSlot);
        break;
      }
      case 12: {
        size_t id;
        if (!getSlot(lean_ctor_get(op, 0), id))
          return ioError("invalid JIT label");
        llvm::BasicBlock *block = findLabel(id);
        if (!block)
          return ioError("missing JIT label");
        builder.SetInsertPoint(block);
        break;
      }
      case 13: {
        size_t id;
        if (!getSlot(lean_ctor_get(op, 0), id))
          return ioError("invalid JIT goto");
        llvm::BasicBlock *target = findLabel(id);
        if (!target)
          return ioError("missing JIT goto target");
        builder.CreateBr(target);
        break;
      }
      case 14: {
        size_t condition, yes, no;
        if (!getSlot(lean_ctor_get(op, 0), condition) ||
            !getSlot(lean_ctor_get(op, 1), yes) ||
            !getSlot(lean_ctor_get(op, 2), no))
          return ioError("invalid JIT branch");
        llvm::BasicBlock *yesBlock = findLabel(yes);
        llvm::BasicBlock *noBlock = findLabel(no);
        if (!yesBlock || !noBlock)
          return ioError("missing JIT branch target");
        builder.CreateCondBr(builder.CreateICmpNE(load(condition), zero), yesBlock, noBlock);
        noteSlot(condition);
        break;
      }
      case 15: {
        size_t dst, address, size;
        if (!getSlot(lean_ctor_get(op, 0), dst) ||
            !getSlot(lean_ctor_get(op, 1), address) ||
            !getSlot(lean_ctor_get(op, 2), size) || size == 0 || size > 8)
          return ioError("invalid JIT memory load");
        bool bigEndian = lean_ctor_get_uint8(op, 3 * sizeof(void *)) != 0;
        llvm::Value *base = load(address);
        builder.CreateCall(notifyMemory,
            {memory, llvm::ConstantInt::get(byte, 0), base,
             llvm::ConstantInt::get(word, size), zero});
        llvm::Value *endianness = llvm::ConstantInt::get(byte, bigEndian ? 1 : 0);
        llvm::Value *result;
        if (hasInstruction(size)) {
          llvm::BasicBlock *slow = llvm::BasicBlock::Create(*context, "load_slow", function);
          llvm::BasicBlock *done = llvm::BasicBlock::Create(*context, "load_done", function);
          llvm::Value *cell = pageForAccess(base, size, false, slow);
          llvm::IntegerType *width = llvm::IntegerType::get(*context, size * 8);
          llvm::LoadInst *loaded = builder.CreateAlignedLoad(width, cell, llvm::Align(size));
          loaded->setAtomic(llvm::AtomicOrdering::Acquire);
          llvm::Value *fast = builder.CreateZExt(swapped(loaded, size, bigEndian), word);
          llvm::BasicBlock *fastEnd = builder.GetInsertBlock();
          builder.CreateBr(done);
          builder.SetInsertPoint(slow);
          llvm::Value *bytes = builder.CreateCall(loadBytes, {memory, base, llvm::ConstantInt::get(word, size), endianness});
          builder.CreateBr(done);
          builder.SetInsertPoint(done);
          llvm::PHINode *merged = builder.CreatePHI(word, 2);
          merged->addIncoming(fast, fastEnd);
          merged->addIncoming(bytes, slow);
          result = merged;
        } else {
          result = builder.CreateCall(loadBytes, {memory, base, llvm::ConstantInt::get(word, size), endianness});
        }
        store(dst, result);
        noteSlot(dst);
        noteSlot(address);
        break;
      }
      case 16: {
        size_t address, value, size;
        if (!getSlot(lean_ctor_get(op, 0), address) ||
            !getSlot(lean_ctor_get(op, 1), value) ||
            !getSlot(lean_ctor_get(op, 2), size) || size == 0 || size > 8)
          return ioError("invalid JIT memory store");
        bool bigEndian = lean_ctor_get_uint8(op, 3 * sizeof(void *)) != 0;
        llvm::Value *base = load(address);
        llvm::Value *stored = load(value);
        builder.CreateCall(notifyMemory,
            {memory, llvm::ConstantInt::get(byte, 1), base,
             llvm::ConstantInt::get(word, size), stored});
        llvm::Value *endianness = llvm::ConstantInt::get(byte, bigEndian ? 1 : 0);
        llvm::Value *sizeValue = llvm::ConstantInt::get(word, size);
        if (hasInstruction(size)) {
          llvm::BasicBlock *slow = llvm::BasicBlock::Create(*context, "store_slow", function);
          llvm::BasicBlock *done = llvm::BasicBlock::Create(*context, "store_done", function);
          llvm::Value *cell = pageForAccess(base, size, true, slow);
          llvm::IntegerType *width = llvm::IntegerType::get(*context, size * 8);
          llvm::StoreInst *written = builder.CreateAlignedStore(
              swapped(builder.CreateTrunc(stored, width), size, bigEndian), cell, llvm::Align(size));
          written->setAtomic(llvm::AtomicOrdering::Release);
          builder.CreateCall(noteStore, {memory, base, sizeValue, endianness, stored});
          builder.CreateBr(done);
          builder.SetInsertPoint(slow);
          builder.CreateCall(storeBytes, {memory, base, sizeValue, endianness, stored});
          builder.CreateBr(done);
          builder.SetInsertPoint(done);
        } else {
          builder.CreateCall(storeBytes, {memory, base, sizeValue, endianness, stored});
        }
        memoryStores += size;
        noteSlot(address);
        noteSlot(value);
        break;
      }
      case 17: {
        size_t effectSlot;
        if (!getSlot(lean_ctor_get(op, 0), effectSlot))
          return ioError("invalid JIT code effect slot");
        uint64_t pc = lean_ctor_get_uint64(op, sizeof(void *));
        llvm::BasicBlock *stopBlock = llvm::BasicBlock::Create(*context, "code_stop", function);
        llvm::BasicBlock *continueBlock = llvm::BasicBlock::Create(*context, "code_continue", function);
        builder.CreateCondBr(
            builder.CreateICmpNE(
                builder.CreateCall(notifyCode, {memory, llvm::ConstantInt::get(word, pc)}), zero),
            stopBlock, continueBlock);
        builder.SetInsertPoint(stopBlock);
        store(effectSlot, llvm::ConstantInt::get(word, 3));
        builder.CreateRet(llvm::ConstantInt::get(word, pc));
        builder.SetInsertPoint(continueBlock);
        noteSlot(effectSlot);
        break;
      }
      default:
        return ioError("invalid JIT operation");
      }
    }
    if (count == 0)
      return ioError("a JIT program must not be empty");
    for (const llvm::BasicBlock &block : *function)
      if (!block.hasTerminator())
        return ioError("a JIT basic block has no terminator: " +
                       block.getName().str());

    if (entries != nullptr) {
      // Before all that there is, so that a run that goes somewhere else has done nothing of it. Nothing is held in a register
      // from one operation to the next, so that it can start at any label.
      llvm::BasicBlock *dispatch = llvm::BasicBlock::Create(*context, "dispatch", function, entry);
      builder.SetInsertPoint(dispatch);
      llvm::Value *selected = builder.CreateLoad(word, builder.CreateConstGEP1_64(word, state, entrySlot));
      llvm::SwitchInst *choice = builder.CreateSwitch(selected, entry);
      for (lean_obj_arg rest = entries; !lean_is_scalar(rest); rest = lean_ctor_get(rest, 1)) {
        size_t id;
        if (!getSlot(lean_ctor_get(rest, 0), id))
          return ioError("invalid JIT entry");
        llvm::BasicBlock *target = findLabel(id);
        if (target == nullptr)
          return ioError("a JIT entry with no label");
        choice->addCase(llvm::ConstantInt::get(llvm::cast<llvm::IntegerType>(word), id + 1), target);
      }
    }

    std::string verificationErrors;
    llvm::raw_string_ostream verificationStream(verificationErrors);
    if (llvm::verifyModule(*module, &verificationStream))
      return ioError("invalid LLVM JIT module: " + verificationErrors);

    auto shared = sharedJit(optimized);
    std::lock_guard<std::mutex> lock(shared->mutex);
    auto resources = shared->jit->getMainJITDylib().createResourceTracker();
    if (llvm::Error error = shared->jit->addIRModule(
            resources, llvm::orc::ThreadSafeModule(std::move(module), std::move(context))))
      return ioError("LLVM ORC module submission failed: " +
                     llvm::toString(std::move(error)));
    auto address = shared->jit->lookup(functionName);
    if (!address) {
      std::string message = llvm::toString(address.takeError());
      if (llvm::Error error = resources->remove())
        llvm::consumeError(std::move(error));
      return ioError("LLVM ORC lookup failed: " + message);
    }

    auto program = std::make_unique<Program>();
    program->function =
        address->toPtr<uint64_t(uint64_t *, BapCells *)>();
    program->shared = shared;
    program->resources = resources;
    program->maxSlot = entries != nullptr ? std::max(hasSlots ? maxSlot + 1 : 0, entrySlot + 1) : (hasSlots ? maxSlot + 1 : 0);
    program->memoryStores = memoryStores;
    return lean_io_result_mk_ok(
        lean_alloc_external(programClass(), program.release()));
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT compilation failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_compile(lean_obj_arg ops, lean_obj_arg) { return compileOps(ops, false); }

extern "C" lean_obj_res bap_jit_compile_optimized(lean_obj_arg ops, lean_obj_arg) { return compileOps(ops, true); }

extern "C" lean_obj_res bap_jit_compile_entries(lean_obj_arg ops, lean_obj_arg entries, lean_obj_arg slot, uint8_t optimized, lean_obj_arg) {
  size_t entrySlot;
  if (!getSlot(slot, entrySlot))
    return ioError("invalid JIT entry slot");
  return compileOps(ops, optimized != 0, entries, entrySlot);
}

extern "C" lean_obj_res bap_jit_run(lean_obj_arg programObject,
                                    lean_obj_arg stateObject, lean_obj_arg) {
  try {
    auto *program = static_cast<Program *>(lean_get_external_data(programObject));
    const size_t size = lean_array_size(stateObject);
    if (size < program->maxSlot)
      return ioError("JIT state has fewer slots than its program requires");
    std::vector<uint64_t> state(size);
    for (size_t index = 0; index != size; ++index)
      state[index] = lean_unbox_uint64(lean_array_get_core(stateObject, index));
    BapCells memory{nullptr, 0, 0, nullptr, nullptr, nullptr, nullptr, nullptr};
    uint64_t next = program->function(state.data(), &memory);
    lean_obj_res resultState = lean_alloc_array(size, size);
    for (size_t index = 0; index != size; ++index)
      lean_array_set_core(resultState, index, lean_box_uint64(state[index]));
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_uint64_to_nat(next));
    lean_ctor_set(result, 1, resultState);
    return lean_io_result_mk_ok(result);
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT execution failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_run_memory_code(lean_obj_arg programObject,
                                                  lean_obj_arg stateObject,
                                                  lean_obj_arg addressesObject,
                                                  lean_obj_arg valuesObject,
                                                  lean_obj_arg observerObject,
                                                  lean_obj_arg codeObserverObject,
                                                  lean_obj_arg) {
  try {
    auto *program = static_cast<Program *>(lean_get_external_data(programObject));
    const size_t stateSize = lean_array_size(stateObject);
    if (stateSize < program->maxSlot)
      return ioError("JIT state has fewer slots than its program requires");
    const size_t addressCount = lean_array_size(addressesObject);
    const size_t valueCount = lean_array_size(valuesObject);
    if (addressCount != valueCount)
      return ioError("JIT memory addresses and values have different lengths");
    std::vector<uint64_t> state(stateSize);
    for (size_t index = 0; index != stateSize; ++index)
      state[index] = lean_unbox_uint64(lean_array_get_core(stateObject, index));
    std::vector<BapCell> cells;
    cells.reserve(addressCount + program->memoryStores);
    for (size_t index = 0; index != addressCount; ++index) {
      cells.push_back(BapCell{
          lean_unbox_uint64(lean_array_get_core(addressesObject, index)),
          static_cast<uint8_t>(lean_unbox(lean_array_get_core(valuesObject, index)))});
    }
    lean_object *observer = lean_is_scalar(observerObject)
        ? nullptr : lean_ctor_get(observerObject, 0);
    lean_object *codeObserver = lean_is_scalar(codeObserverObject)
        ? nullptr : lean_ctor_get(codeObserverObject, 0);
    BapCells memory{cells.data(), addressCount, cells.capacity(), observer, nullptr, nullptr, nullptr, codeObserver};
    uint64_t next = program->function(state.data(), &memory);
    if (memory.error != nullptr)
      return lean_io_result_mk_error(memory.error);

    lean_obj_res resultState = lean_alloc_array(stateSize, stateSize);
    for (size_t index = 0; index != stateSize; ++index)
      lean_array_set_core(resultState, index, lean_box_uint64(state[index]));
    lean_obj_res resultAddresses = lean_alloc_array(memory.size, memory.size);
    lean_obj_res resultValues = lean_alloc_array(memory.size, memory.size);
    for (size_t index = 0; index != memory.size; ++index) {
      lean_array_set_core(resultAddresses, index,
                          lean_box_uint64(memory.items[index].address));
      lean_array_set_core(resultValues, index,
                          lean_box(memory.items[index].value));
    }
    lean_obj_res memoryResult = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(memoryResult, 0, resultAddresses);
    lean_ctor_set(memoryResult, 1, resultValues);
    lean_obj_res stateResult = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(stateResult, 0, resultState);
    lean_ctor_set(stateResult, 1, memoryResult);
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_uint64_to_nat(next));
    lean_ctor_set(result, 1, stateResult);
    return lean_io_result_mk_ok(result);
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT memory execution failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_run_memory(lean_obj_arg programObject,
                                             lean_obj_arg stateObject,
                                             lean_obj_arg addressesObject,
                                             lean_obj_arg valuesObject,
                                             lean_obj_arg observerObject,
                                             lean_obj_arg world) {
  return bap_jit_run_memory_code(programObject, stateObject, addressesObject,
                                 valuesObject, observerObject, lean_box(0), world);
}

namespace {
void finalizeMemory(void *data) { delete static_cast<PagedMemory *>(data); }
void foreachMemory(void *, b_lean_obj_arg) {}

lean_external_class *memoryClass() {
  static lean_external_class *cls =
      lean_register_external_class(finalizeMemory, foreachMemory);
  return cls;
}
}

extern "C" lean_obj_res bap_jit_memory_create(lean_obj_arg addressesObject,
                                                lean_obj_arg valuesObject,
                                                lean_obj_arg) {
  try {
    const size_t addressCount = lean_array_size(addressesObject);
    const size_t valueCount = lean_array_size(valuesObject);
    if (addressCount != valueCount)
      return ioError("JIT memory addresses and values have different lengths");
    auto *memory = new PagedMemory;
    std::vector<uint64_t> addresses(addressCount);
    std::vector<uint8_t> values(addressCount);
    for (size_t index = 0; index != addressCount; ++index) {
      addresses[index] = lean_unbox_uint64(lean_array_get_core(addressesObject, index));
      values[index] = static_cast<uint8_t>(lean_unbox(lean_array_get_core(valuesObject, index)));
    }
    memory->writeAll(addresses.data(), values.data(), addressCount);
    return lean_io_result_mk_ok(lean_alloc_external(memoryClass(), memory));
  } catch (const std::exception &error) {
    return ioError(std::string("JIT memory creation failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_memory_create_chunks(lean_obj_arg basesObject, lean_obj_arg chunksObject, lean_obj_arg) {
  try {
    const size_t count = lean_array_size(basesObject);
    if (count != lean_array_size(chunksObject))
      return ioError("JIT memory bases and chunks have different lengths");
    auto *memory = new PagedMemory;
    for (size_t index = 0; index != count; ++index) {
      lean_object *chunk = lean_array_get_core(chunksObject, index);
      memory->fill(lean_unbox_uint64(lean_array_get_core(basesObject, index)), lean_sarray_cptr(chunk), lean_sarray_size(chunk));
    }
    return lean_io_result_mk_ok(lean_alloc_external(memoryClass(), memory));
  } catch (const std::exception &error) {
    return ioError(std::string("JIT memory creation failed: ") + error.what());
  }
}

// Bytes of zeros that take memory of the host only where they are written: those from where a page of the host starts to where the last
// one ends are given back to it, which gives pages of zeros again as they are touched. Few are, of what a program maps and never uses.
static const size_t lazyFrom = 65536;

static lean_obj_res lazyZeros(size_t size) {
  lean_obj_res result = lean_alloc_sarray(1, size, size);
  uint8_t *data = lean_sarray_cptr(result);
#if defined(__linux__)
  if (size >= lazyFrom) {
    const uintptr_t page = static_cast<uintptr_t>(sysconf(_SC_PAGESIZE));
    const uintptr_t start = reinterpret_cast<uintptr_t>(data);
    const uintptr_t end = start + size;
    const uintptr_t first = (start + page - 1) / page * page;
    const uintptr_t last = end / page * page;
    if (first < last) {
      std::memset(data, 0, first - start);
      std::memset(reinterpret_cast<void *>(last), 0, end - last);
      if (madvise(reinterpret_cast<void *>(first), last - first, MADV_DONTNEED) != 0)
        std::memset(reinterpret_cast<void *>(first), 0, last - first);
      return result;
    }
  }
#endif
  std::memset(data, 0, size);
  return result;
}

static bool allZero(const uint8_t *bytes, size_t count) {
  return count == 0 || (bytes[0] == 0 && std::memcmp(bytes, bytes + 1, count - 1) == 0);
}

extern "C" lean_obj_res bap_zero_bytes(b_lean_obj_arg sizeObject) {
  return lazyZeros(lean_usize_of_nat(sizeObject));
}

// `ByteArray.extract`, which for what is big copies only what isn't zeros into zeros that take no memory yet.
static lean_obj_res sliceBytes(b_lean_obj_arg dataObject, b_lean_obj_arg startObject, b_lean_obj_arg stopObject) {
  const size_t total = lean_sarray_size(dataObject);
  const size_t stop = lean_is_scalar(stopObject) ? std::min(lean_usize_of_nat(stopObject), total) : total;
  const size_t start = lean_is_scalar(startObject) ? lean_usize_of_nat(startObject) : total;
  const size_t size = start < stop ? stop - start : 0;
  const uint8_t *from = lean_sarray_cptr(dataObject) + (size == 0 ? 0 : start);
  if (size < lazyFrom) {
    lean_obj_res result = lean_alloc_sarray(1, size, size);
    if (size != 0)
      std::memcpy(lean_sarray_cptr(result), from, size);
    return result;
  }
  lean_obj_res result = lazyZeros(size);
  uint8_t *to = lean_sarray_cptr(result);
  for (size_t done = 0; done < size; done += 4096) {
    const size_t count = std::min<size_t>(4096, size - done);
    if (!allZero(from + done, count))
      std::memcpy(to + done, from + done, count);
  }
  return result;
}

extern "C" lean_obj_res bap_bytes_slice(lean_obj_arg dataObject, lean_obj_arg startObject, lean_obj_arg stopObject) {
  lean_obj_res result = sliceBytes(dataObject, startObject, stopObject);
  lean_dec(dataObject);
  lean_dec(startObject);
  lean_dec(stopObject);
  return result;
}

// `Jit.pieces`: each piece of 4096 bytes from the start that isn't all zeros, with where it starts, in order.
extern "C" lean_obj_res bap_bytes_pieces(lean_obj_arg dataObject) {
  const size_t size = lean_sarray_size(dataObject);
  const uint8_t *data = lean_sarray_cptr(dataObject);
  std::vector<size_t> starts;
  for (size_t start = 0; start < size; start += 4096)
    if (!allZero(data + start, std::min<size_t>(4096, size - start)))
      starts.push_back(start);
  lean_obj_res list = lean_box(0);
  for (auto at = starts.rbegin(); at != starts.rend(); ++at) {
    const size_t count = std::min<size_t>(4096, size - *at);
    lean_obj_res bytes = lean_alloc_sarray(1, count, count);
    std::memcpy(lean_sarray_cptr(bytes), data + *at, count);
    lean_obj_res piece = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(piece, 0, lean_usize_to_nat(*at));
    lean_ctor_set(piece, 1, bytes);
    lean_obj_res cell = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(cell, 0, piece);
    lean_ctor_set(cell, 1, list);
    list = cell;
  }
  lean_dec(dataObject);
  return list;
}

// `Jit.fill`: zeros that take no memory yet, with each piece in them where it starts, the first of those that have a byte giving it.
extern "C" lean_obj_res bap_bytes_fill(lean_obj_arg sizeObject, lean_obj_arg piecesObject) {
  const size_t size = lean_usize_of_nat(sizeObject);
  lean_obj_res result = lazyZeros(size);
  uint8_t *to = lean_sarray_cptr(result);
  std::vector<b_lean_obj_arg> pieces;
  for (b_lean_obj_arg cell = piecesObject; !lean_is_scalar(cell); cell = lean_ctor_get(cell, 1))
    pieces.push_back(lean_ctor_get(cell, 0));
  for (auto at = pieces.rbegin(); at != pieces.rend(); ++at) {
    b_lean_obj_arg startObject = lean_ctor_get(*at, 0);
    b_lean_obj_arg bytes = lean_ctor_get(*at, 1);
    if (!lean_is_scalar(startObject))
      continue;
    const size_t start = lean_unbox(startObject);
    if (start >= size)
      continue;
    const size_t count = std::min(lean_sarray_size(bytes), size - start);
    if (count != 0)
      std::memcpy(to + start, lean_sarray_cptr(bytes), count);
  }
  lean_dec(sizeObject);
  lean_dec(piecesObject);
  return result;
}

// The bytes of a range of a memory, which takes memory of the host for the pages that it has and not for the rest.
extern "C" lean_obj_res bap_jit_memory_region_bytes(lean_obj_arg memoryObject, uint64_t address, b_lean_obj_arg sizeObject, lean_obj_arg) {
  auto *memory = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  const size_t size = lean_usize_of_nat(sizeObject);
  lean_obj_res result = lazyZeros(size);
  uint8_t *to = lean_sarray_cptr(result);
  size_t done = 0;
  while (done < size) {
    const uint64_t at = address + done;
    const size_t offset = at & (PagedMemory::pageSize - 1);
    const size_t count = std::min<size_t>(PagedMemory::pageSize - offset, size - done);
    if (const uint8_t *page = memory->find(at))
      if (!allZero(page + offset, count))
        std::memcpy(to + done, page + offset, count);
    done += count;
  }
  return lean_io_result_mk_ok(result);
}

extern "C" lean_obj_res bap_jit_memory_zero(lean_obj_arg memoryObject, uint64_t first, uint64_t last, lean_obj_arg) {
  static_cast<PagedMemory *>(lean_get_external_data(memoryObject))->zeroRange(first, last);
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res bap_jit_memory_write(lean_obj_arg memoryObject,
                                               lean_obj_arg addressesObject,
                                               lean_obj_arg valuesObject, lean_obj_arg) {
  try {
    auto *persistent = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
    const size_t addressCount = lean_array_size(addressesObject);
    const size_t valueCount = lean_array_size(valuesObject);
    if (addressCount != valueCount)
      return ioError("JIT memory addresses and values have different lengths");
    std::vector<uint64_t> addresses(addressCount);
    std::vector<uint8_t> values(addressCount);
    for (size_t index = 0; index != addressCount; ++index) {
      addresses[index] = lean_unbox_uint64(lean_array_get_core(addressesObject, index));
      values[index] = static_cast<uint8_t>(lean_unbox(lean_array_get_core(valuesObject, index)));
    }
    persistent->writeAll(addresses.data(), values.data(), addressCount);
return lean_io_result_mk_ok(lean_box(0));
  } catch (const std::exception &error) {
    return ioError(std::string("JIT persistent memory write failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_memory_clone(lean_obj_arg memoryObject, lean_obj_arg) {
  auto *persistent = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  auto *copy = new PagedMemory;
  copy->copyFrom(*persistent);
  return lean_io_result_mk_ok(lean_alloc_external(memoryClass(), copy));
}

extern "C" lean_obj_res bap_jit_run_memory_object_code(
    lean_obj_arg programObject, lean_obj_arg stateObject,
    lean_obj_arg memoryObject, lean_obj_arg observerObject,
    lean_obj_arg codeObserverObject, lean_obj_arg) {
  try {
    auto *program = static_cast<Program *>(lean_get_external_data(programObject));
    auto *persistent = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
    const size_t stateSize = lean_array_size(stateObject);
    if (stateSize < program->maxSlot)
      return ioError("JIT state has fewer slots than its program requires");
    std::vector<uint64_t> state(stateSize);
    for (size_t index = 0; index != stateSize; ++index)
      state[index] = lean_unbox_uint64(lean_array_get_core(stateObject, index));
    lean_object *observer = lean_is_scalar(observerObject)
        ? nullptr : lean_ctor_get(observerObject, 0);
    lean_object *codeObserver = lean_is_scalar(codeObserverObject)
        ? nullptr : lean_ctor_get(codeObserverObject, 0);
    std::vector<StoreRecord> records;
    BapCells memory{nullptr, 0, 0, observer, nullptr, persistent, &records, codeObserver};
    uint64_t next = program->function(state.data(), &memory);
    // Before anything else, as this is what a run that failed leaves to be taken back.
    if (persistent->stepActive())
      for (const StoreRecord &record : records)
        persistent->noteStep(record.address, record.size);
    if (memory.error != nullptr)
      return lean_io_result_mk_error(memory.error);
    // What the stores came to, each byte once, the last that was written to it.
    CellMap changes;
    changes.reserve(records.size());
    for (const StoreRecord &record : records)
      for (uint64_t index = 0; index != record.size; ++index) {
        uint64_t shift = (record.bigEndian != 0 ? record.size - 1 - index : index) * 8;
        changes.set(record.address + index, static_cast<uint8_t>(record.value >> shift));
      }
    lean_obj_res resultState = lean_alloc_array(stateSize, stateSize);
    for (size_t index = 0; index != stateSize; ++index)
      lean_array_set_core(resultState, index, lean_box_uint64(state[index]));
    lean_obj_res resultAddresses = lean_alloc_array(changes.size(), changes.size());
    lean_obj_res resultValues = lean_alloc_array(changes.size(), changes.size());
    size_t index = 0;
    changes.forEach([&](uint64_t address, uint8_t value) {
      lean_array_set_core(resultAddresses, index, lean_box_uint64(address));
      lean_array_set_core(resultValues, index, lean_box(value));
      ++index;
    });
    lean_obj_res memoryResult = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(memoryResult, 0, resultAddresses);
    lean_ctor_set(memoryResult, 1, resultValues);
    lean_obj_res stateResult = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(stateResult, 0, resultState);
    lean_ctor_set(stateResult, 1, memoryResult);
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_uint64_to_nat(next));
    lean_ctor_set(result, 1, stateResult);
    return lean_io_result_mk_ok(result);
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT persistent memory execution failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_run_memory_object(
    lean_obj_arg programObject, lean_obj_arg stateObject,
    lean_obj_arg memoryObject, lean_obj_arg observerObject, lean_obj_arg world) {
  return bap_jit_run_memory_object_code(programObject, stateObject, memoryObject,
                                        observerObject, lean_box(0), world);
}

extern "C" lean_obj_res bap_jit_memory_dump(lean_obj_arg memoryObject, lean_obj_arg) {
  auto *memory = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  std::vector<std::pair<uint64_t, uint8_t>> cells;
  memory->forEachPage([&](uint64_t address, const uint8_t *page) {
    // By the word, so that a word that a thread is storing to is one that it stored.
    for (size_t offset = 0; offset != PagedMemory::pageSize; offset += sizeof(uint64_t)) {
      uint64_t word = __atomic_load_n(reinterpret_cast<const uint64_t *>(page + offset), __ATOMIC_ACQUIRE);
      if (word == 0)
        continue;
      uint8_t bytes[sizeof(uint64_t)];
      std::memcpy(bytes, &word, sizeof(uint64_t));
      for (size_t index = 0; index != sizeof(uint64_t); ++index)
        if (bytes[index] != 0)
          cells.emplace_back(address + offset + index, bytes[index]);
    }
  });
  lean_obj_res addresses = lean_alloc_array(cells.size(), cells.size());
  lean_obj_res values = lean_alloc_array(cells.size(), cells.size());
  size_t index = 0;
  for (const auto &cell : cells) {
    lean_array_set_core(addresses, index, lean_box_uint64(cell.first));
    lean_array_set_core(values, index, lean_box(cell.second));
    ++index;
  }
  lean_obj_res result = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(result, 0, addresses);
  lean_ctor_set(result, 1, values);
  return lean_io_result_mk_ok(result);
}

extern "C" lean_obj_res bap_jit_memory_read(lean_obj_arg memoryObject, uint64_t address, lean_obj_arg) {
  auto *memory = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  return lean_io_result_mk_ok(lean_uint64_to_nat(memory->read(address)));
}

extern "C" lean_obj_res bap_jit_memory_read_range(lean_obj_arg memoryObject, uint64_t address, lean_obj_arg sizeObject, lean_obj_arg) {
  if (!lean_is_scalar(sizeObject))
    return ioError("JIT memory read too large");
  auto *memory = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  size_t size = lean_unbox(sizeObject);
  lean_obj_res result = lean_alloc_sarray(1, size, size);
  memory->readRange(address, size, lean_sarray_cptr(result));
  return lean_io_result_mk_ok(result);
}

extern "C" lean_obj_res bap_jit_memory_step_begin(lean_obj_arg memoryObject, lean_obj_arg) {
  static_cast<PagedMemory *>(lean_get_external_data(memoryObject))->beginStep();
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res bap_jit_memory_step_end(lean_obj_arg memoryObject, lean_obj_arg) {
  static_cast<PagedMemory *>(lean_get_external_data(memoryObject))->endStep();
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res bap_jit_memory_step_writes(lean_obj_arg memoryObject, lean_obj_arg) {
  std::vector<uint64_t> addresses;
  if (!static_cast<PagedMemory *>(lean_get_external_data(memoryObject))->stepAddresses(addresses))
    return lean_io_result_mk_ok(lean_box(0));
  lean_obj_res array = lean_alloc_array(addresses.size(), addresses.size());
  for (size_t index = 0; index != addresses.size(); ++index)
    lean_array_set_core(array, index, lean_box_uint64(addresses[index]));
  lean_obj_res some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, array);
  return lean_io_result_mk_ok(some);
}

extern "C" lean_obj_res bap_jit_memory_trim(lean_obj_arg memoryObject, uint64_t first, uint64_t last, lean_obj_arg) {
  static_cast<PagedMemory *>(lean_get_external_data(memoryObject))->trim(first, last);
  return lean_io_result_mk_ok(lean_box(0));
}

extern "C" lean_obj_res bap_jit_memory_size(lean_obj_arg memoryObject, lean_obj_arg) {
  auto *memory = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  size_t total = 0;
  memory->forEachPage([&](uint64_t, const uint8_t *page) {
    for (size_t offset = 0; offset != PagedMemory::pageSize; ++offset)
      if (__atomic_load_n(page + offset, __ATOMIC_RELAXED) != 0)
        ++total;
  });
  return lean_io_result_mk_ok(lean_uint64_to_nat(total));
}
