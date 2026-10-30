#include <lean/lean.h>

#include <llvm/ExecutionEngine/Orc/AbsoluteSymbols.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/Support/raw_ostream.h>

#include <algorithm>
#include <array>
#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <limits>
#include <malloc.h>
#include <memory>
#include <mutex>
#include <string>
#include <vector>

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

struct BapCells {
  BapCell *items;
  size_t size;
  size_t capacity;
  lean_object *observer;
  lean_object *error;
  std::array<CellMap, 64> *tables;
  CellMap *changes;
  lean_object *codeObserver;
  std::array<std::mutex, 64> *memoryMutexes;
};

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
  if (lean_io_result_is_error(result)) {
    cells->error = lean_io_result_get_error(result);
    lean_inc_ref(cells->error);
  }
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
    cells->error = lean_io_result_get_error(result);
    lean_inc_ref(cells->error);
    stop = 1;
  } else {
    stop = lean_unbox(lean_io_result_get_value(result));
  }
  lean_dec_ref(result);
  return stop;
}

extern "C" uint8_t bap_jit_memory_load(BapCells *cells, uint64_t address) {
  if (cells->error != nullptr)
    return 0;
  if (cells->tables != nullptr) {
    size_t shard = (address >> 8) & 63;
    std::lock_guard<std::mutex> lock((*cells->memoryMutexes)[shard]);
    return (*cells->tables)[shard].get(address);
  }
  for (size_t index = 0; index != cells->size; ++index)
    if (cells->items[index].address == address)
      return cells->items[index].value;
  return 0;
}

extern "C" void bap_jit_memory_store(BapCells *cells, uint64_t address,
                                     uint8_t value) {
  if (cells->error != nullptr)
    return;
  if (cells->tables != nullptr) {
    size_t shard = (address >> 8) & 63;
    std::lock_guard<std::mutex> lock((*cells->memoryMutexes)[shard]);
    (*cells->tables)[shard].set(address, value);
    if (cells->changes != nullptr)
      cells->changes->set(address, value);
    return;
  }
  for (size_t index = 0; index != cells->size; ++index) {
    if (cells->items[index].address == address) {
      cells->items[index].value = value;
      return;
    }
  }
  if (cells->size != cells->capacity)
    cells->items[cells->size++] = BapCell{address, value};
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

std::shared_ptr<SharedJit> sharedJit() {
  static std::mutex mutex;
  static std::shared_ptr<SharedJit> shared;
  std::lock_guard<std::mutex> lock(mutex);
  if (shared != nullptr)
    return shared;
  auto jit = llvm::orc::LLJITBuilder().create();
  if (!jit)
    throw std::runtime_error("LLVM ORC JIT creation failed: " +
                             llvm::toString(jit.takeError()));
  llvm::orc::SymbolMap runtimeSymbols;
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_load")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_load);
  runtimeSymbols[(*jit)->mangleAndIntern("bap_jit_memory_store")] =
      llvm::orc::ExecutorSymbolDef::fromPtr(&bap_jit_memory_store);
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

extern "C" lean_obj_res bap_jit_compile(lean_obj_arg ops, lean_obj_arg) {
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
    llvm::FunctionCallee loadMemory = module->getOrInsertFunction(
        "bap_jit_memory_load", llvm::FunctionType::get(byte, {pointer, word}, false));
    llvm::FunctionCallee storeMemory = module->getOrInsertFunction(
        "bap_jit_memory_store",
        llvm::FunctionType::get(llvm::Type::getVoidTy(*context),
                                {pointer, word, byte}, false));
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
          result = builder.CreateSelect(isZero, binary == 16 ? ones : left, result);
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
        llvm::Value *result = zero;
        for (size_t index = 0; index != size; ++index) {
          llvm::Value *current = builder.CreateAdd(
              base, llvm::ConstantInt::get(word, index));
          llvm::Value *value = builder.CreateCall(loadMemory, {memory, current});
          size_t shift = (bigEndian ? size - 1 - index : index) * 8;
          result = builder.CreateOr(
              result, builder.CreateShl(builder.CreateZExt(value, word), shift));
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
        for (size_t index = 0; index != size; ++index) {
          llvm::Value *current = builder.CreateAdd(
              base, llvm::ConstantInt::get(word, index));
          size_t shift = (bigEndian ? size - 1 - index : index) * 8;
          llvm::Value *byteValue = builder.CreateTrunc(
              builder.CreateLShr(stored, shift), byte);
          builder.CreateCall(storeMemory, {memory, current, byteValue});
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

    std::string verificationErrors;
    llvm::raw_string_ostream verificationStream(verificationErrors);
    if (llvm::verifyModule(*module, &verificationStream))
      return ioError("invalid LLVM JIT module: " + verificationErrors);

    auto shared = sharedJit();
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
    program->maxSlot = hasSlots ? maxSlot + 1 : 0;
    program->memoryStores = memoryStores;
    return lean_io_result_mk_ok(
        lean_alloc_external(programClass(), program.release()));
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT compilation failed: ") + error.what());
  }
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
    BapCells memory{nullptr, 0, 0, nullptr, nullptr, nullptr, nullptr, nullptr, nullptr};
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
    BapCells memory{cells.data(), addressCount, cells.capacity(), observer, nullptr, nullptr, nullptr, codeObserver, nullptr};
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
struct PersistentMemory {
  std::array<CellMap, 64> cells;
  std::array<std::mutex, 64> mutexes;

  size_t size() const {
    size_t total = 0;
    for (const auto &cell : cells)
      total += cell.size();
    return total;
  }

  template <typename F> void forEach(F &&action) const {
    for (const auto &cell : cells)
      cell.forEach(action);
  }

  std::vector<std::unique_lock<std::mutex>> lockAll() {
    std::vector<std::unique_lock<std::mutex>> locks;
    locks.reserve(mutexes.size());
    for (auto &mutex : mutexes)
      locks.emplace_back(mutex);
    return locks;
  }
};

void finalizeMemory(void *data) { delete static_cast<PersistentMemory *>(data); }
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
    auto *memory = new PersistentMemory;
    for (auto &cell : memory->cells)
      cell.reserve(addressCount / memory->cells.size() + 1);
    for (size_t index = 0; index != addressCount; ++index) {
      uint64_t address = lean_unbox_uint64(lean_array_get_core(addressesObject, index));
      memory->cells[(address >> 8) & 63].set(
          address, static_cast<uint8_t>(lean_unbox(lean_array_get_core(valuesObject, index))));
    }
    return lean_io_result_mk_ok(lean_alloc_external(memoryClass(), memory));
  } catch (const std::exception &error) {
    return ioError(std::string("JIT memory creation failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_memory_write(lean_obj_arg memoryObject,
                                               lean_obj_arg addressesObject,
                                               lean_obj_arg valuesObject, lean_obj_arg) {
  try {
    auto *persistent = static_cast<PersistentMemory *>(lean_get_external_data(memoryObject));
    const size_t addressCount = lean_array_size(addressesObject);
    const size_t valueCount = lean_array_size(valuesObject);
    if (addressCount != valueCount)
      return ioError("JIT memory addresses and values have different lengths");
    auto locks = persistent->lockAll();
    for (size_t index = 0; index != addressCount; ++index) {
      uint64_t address = lean_unbox_uint64(lean_array_get_core(addressesObject, index));
      persistent->cells[(address >> 8) & 63].set(
          address, static_cast<uint8_t>(lean_unbox(lean_array_get_core(valuesObject, index))));
    }
    return lean_io_result_mk_ok(lean_box(0));
  } catch (const std::exception &error) {
    return ioError(std::string("JIT persistent memory write failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_memory_clone(lean_obj_arg memoryObject, lean_obj_arg) {
  auto *persistent = static_cast<PersistentMemory *>(lean_get_external_data(memoryObject));
  auto locks = persistent->lockAll();
  auto *copy = new PersistentMemory;
  copy->cells = persistent->cells;
  return lean_io_result_mk_ok(lean_alloc_external(memoryClass(), copy));
}

extern "C" lean_obj_res bap_jit_run_memory_object_code(
    lean_obj_arg programObject, lean_obj_arg stateObject,
    lean_obj_arg memoryObject, lean_obj_arg observerObject,
    lean_obj_arg codeObserverObject, lean_obj_arg) {
  try {
    auto *program = static_cast<Program *>(lean_get_external_data(programObject));
    auto *persistent = static_cast<PersistentMemory *>(lean_get_external_data(memoryObject));
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
    CellMap changes;
    BapCells memory{nullptr, 0, 0, observer, nullptr, &persistent->cells, &changes, codeObserver, &persistent->mutexes};
    uint64_t next = program->function(state.data(), &memory);
    if (memory.error != nullptr)
      return lean_io_result_mk_error(memory.error);
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
  auto *memory = static_cast<PersistentMemory *>(lean_get_external_data(memoryObject));
  auto locks = memory->lockAll();
  std::vector<std::pair<uint64_t, uint8_t>> cells;
  cells.reserve(memory->size());
  memory->forEach([&](uint64_t address, uint8_t value) {
    cells.emplace_back(address, value);
  });
  std::sort(cells.begin(), cells.end());
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
  auto *memory = static_cast<PersistentMemory *>(lean_get_external_data(memoryObject));
  std::lock_guard<std::mutex> lock(memory->mutexes[(address >> 8) & 63]);
  uint8_t value = memory->cells[(address >> 8) & 63].get(address);
  return lean_io_result_mk_ok(lean_uint64_to_nat(value));
}

extern "C" lean_obj_res bap_jit_memory_size(lean_obj_arg memoryObject, lean_obj_arg) {
  auto *memory = static_cast<PersistentMemory *>(lean_get_external_data(memoryObject));
  auto locks = memory->lockAll();
  return lean_io_result_mk_ok(lean_uint64_to_nat(memory->size()));
}
