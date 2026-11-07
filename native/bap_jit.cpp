#include <lean/lean.h>

#include <llvm/ExecutionEngine/Orc/AbsoluteSymbols.h>
#include <llvm/ExecutionEngine/Orc/LLJIT.h>
#include <llvm/ExecutionEngine/Orc/ThreadSafeModule.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/DeadStoreElimination.h>
#include <llvm/Transforms/Scalar/EarlyCSE.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Scalar/Sink.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/MDBuilder.h>
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
#include <map>
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

struct BapCell {
  uint64_t address;
  uint8_t value;
};

// The bytes that the stores of a run wrote, each once with the last value written to it, by the page of 4096: a store marks its bytes
// in the page that the last one was on, most often, and what a run changed costs what it changed and not how many stores it made.
class StoreLog {
  struct Page {
    uint64_t written[64] = {};
    uint8_t values[4096];
  };
  std::unordered_map<uint64_t, std::unique_ptr<Page>> pages;
  uint64_t lastNumber = ~uint64_t{0};
  Page *last = nullptr;
  size_t count = 0;

  Page *pageOf(uint64_t number) {
    if (number == lastNumber)
      return last;
    std::unique_ptr<Page> &slot = pages[number];
    if (!slot)
      slot = std::make_unique<Page>();
    lastNumber = number;
    last = slot.get();
    return last;
  }

public:
  void note(uint64_t address, uint64_t size, bool bigEndian, uint64_t value) {
    // An access as an instruction makes it, aligned to its size, is in one word of the bitmap and one page: one mask and one copy.
    if ((size == 1 || size == 2 || size == 4 || size == 8) && (address & (size - 1)) == 0) {
      Page *page = pageOf(address >> 12);
      size_t offset = static_cast<size_t>(address & 4095);
      // A bit for each byte of it.
      uint64_t mask = ((uint64_t{1} << size) - 1) << (offset & 63);
      uint64_t &word = page->written[offset >> 6];
      count += static_cast<size_t>(__builtin_popcountll(mask & ~word));
      word |= mask;
      uint8_t bytes[8];
      for (uint64_t index = 0; index != size; ++index)
        bytes[index] = static_cast<uint8_t>(value >> ((bigEndian ? size - 1 - index : index) * 8));
      std::memcpy(page->values + offset, bytes, size);
      return;
    }
    for (uint64_t index = 0; index != size; ++index) {
      uint64_t at = address + index;
      Page *page = pageOf(at >> 12);
      size_t offset = static_cast<size_t>(at & 4095);
      uint64_t bit = uint64_t{1} << (offset & 63);
      if ((page->written[offset >> 6] & bit) == 0) {
        page->written[offset >> 6] |= bit;
        ++count;
      }
      page->values[offset] = static_cast<uint8_t>(value >> ((bigEndian ? size - 1 - index : index) * 8));
    }
  }

  size_t size() const { return count; }

  // Each byte written, with its value, in no particular order.
  template <typename F> void forEach(F &&action) const {
    for (const auto &entry : pages)
      for (size_t word = 0; word != 64; ++word)
        for (uint64_t bits = entry.second->written[word]; bits != 0; bits &= bits - 1) {
          size_t offset = word * 64 + static_cast<size_t>(__builtin_ctzll(bits));
          action((entry.first << 12) + offset, entry.second->values[offset]);
        }
  }
};

// Where a run last found the pages. A tag is one more than the number of a page, so that 0 is an entry that holds nothing. A run has
// its own, so that this needs no synchronization, and the code that a program is compiled to reads it.
struct BapPageEntry {
  uint64_t tag;
  uint8_t *page;
  // The tag again for a read, and for a write, where the memory observer would do nothing with any access of that kind to the
  // page, so that an access there is one check of the page.
  uint64_t quiet[2];
};
constexpr size_t pageEntryCount = 64;
static_assert(sizeof(BapPageEntry) == 32, "compiled code goes through these by index");

// The ranges of addresses where the memory observer would do nothing, by its first address, none overlapping: an access that lies
// within one of them, of the kind it lets through, needs no call of the observer, which is what costs most of an access otherwise.
struct MemoryFilter {
  struct Range {
    uint64_t first;
    uint64_t last;
    bool readQuiet;
    bool writeQuiet;
  };
  // By the first address, so that what a mapping changes is changed where it is, without making all of it again.
  std::map<uint64_t, Range> ranges;

  // The range that an access lies within, of the kind it lets through, if there is one.
  const Range *quietRange(uint64_t address, uint64_t size, bool write) const {
    if (size == 0)
      return nullptr;
    uint64_t last = address + size - 1;
    if (last < address)
      return nullptr;
    auto after = ranges.upper_bound(address);
    if (after == ranges.begin())
      return nullptr;
    const Range &range = std::prev(after)->second;
    return last <= range.last && (write ? range.writeQuiet : range.readQuiet) ? &range : nullptr;
  }

  // Whether a range goes in apart from those there, which it does if so.
  bool insert(const Range &range) {
    if (range.last < range.first)
      return false;
    auto after = ranges.upper_bound(range.first);
    if (after != ranges.end() && after->second.first <= range.last)
      return false;
    if (after != ranges.begin() && std::prev(after)->second.last >= range.first)
      return false;
    ranges.emplace(range.first, range);
    return true;
  }
};

struct BapCells {
  BapCell *items;
  size_t size;
  size_t capacity;
  lean_object *observer;
  lean_object *error;
  PagedMemory *pages;
  StoreLog *changes;
  lean_object *codeObserver;
  const MemoryFilter *filter = nullptr;
  // The variables of a chain, by their numbers, which what is optimized with numbers for its variables reads and writes in place of
  // their slots, so that going from range to range copies nothing: none for a run of its own (obligation 17).
  uint64_t *registers = nullptr;
  // A run whose code sites would only set the pc, as nothing observes it and no Lean code has run in it: the site of the last block
  // waits here, for the memory observer to be called, as it reads the pc (obligation 16).
  bool quietSites = false;
  bool leanRan = false;
  bool pendingSite = false;
  uint64_t pendingPc = 0;
  // The last range that the filter let a read, and a write, through in, which compiled code looks at before it calls the observer, so
  // that an access there costs no call: none, the first above the last, until the filter finds one, and again once Lean code has run,
  // which may change what is quiet, or there is an error.
  uint64_t quietFirst[2] = {1, 1};
  uint64_t quietLast[2] = {0, 0};
  // The slots of the run, which a code site that calls Lean code leaves as they are there, so that what it runs can read them: none
  // for a run whose slots aren't one array, as of a chain.
  uint64_t *slots = nullptr;
  size_t slotCount = 0;
  // Where `items` are, of a run that keeps them, for a store to an address that they haven't yet to add one to, rather than being
  // dropped once there are as many as were set aside, as a loop that stores to as many addresses as it goes round makes.
  std::vector<BapCell> *growable = nullptr;
  // Which run these are of, for what was last said of its slots.
  uint64_t serial = nextCellsSerial();
  // Whether the slots are always as the run has them, as those of code that isn't optimized are, and else the pc of the site that
  // last left them so before it called Lean code, which code that is optimized does at the sites that it was told of.
  bool slotsLive = false;
  uint64_t flushedPc = ~uint64_t{0};
  BapPageEntry pageEntries[pageEntryCount] = {};

  static uint64_t nextCellsSerial() {
    static std::atomic<uint64_t> serials{0};
    return ++serials;
  }
};

// The cells of the run whose code site the Lean code that runs now was called from, if it was.
static thread_local BapCells *siteCells = nullptr;

// What was last said of the slots of a run, by `bap_jit_live_changes`, of the run of `serial`.
struct SiteReport {
  uint64_t serial = 0;
  std::vector<uint64_t> values;
  std::vector<uint8_t> known;
};
static thread_local SiteReport siteReport;

static void forgetQuiet(BapCells *cells) {
  cells->quietFirst[0] = cells->quietFirst[1] = 1;
  cells->quietLast[0] = cells->quietLast[1] = 0;
  for (BapPageEntry &entry : cells->pageEntries)
    entry.quiet[0] = entry.quiet[1] = 0;
}

// Once there is an error nothing takes effect, and with nothing here compiled code goes to `bap_jit_memory_page`, which says so.
static void failCells(BapCells *cells, lean_object *error) {
  cells->error = error;
  lean_inc_ref(error);
  std::memset(cells->pageEntries, 0, sizeof(cells->pageEntries));
  forgetQuiet(cells);
}

static uint64_t callCodeObserver(BapCells *cells, uint64_t pc) {
  forgetQuiet(cells);
  lean_inc_ref(cells->codeObserver);
  lean_object *action = lean_apply_1(cells->codeObserver, lean_uint64_to_nat(pc));
  BapCells *outer = siteCells;
  siteCells = cells;
  lean_object *result = lean_apply_1(action, lean_io_mk_world());
  siteCells = outer;
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

extern "C" void bap_jit_memory_notify(BapCells *cells, uint8_t write,
                                      uint64_t address, uint64_t size,
                                      uint64_t value) {
  if (cells->observer == nullptr || cells->error != nullptr)
    return;
  if (cells->filter != nullptr) {
    if (const MemoryFilter::Range *range = cells->filter->quietRange(address, size, write != 0)) {
      cells->quietFirst[write != 0] = range->first;
      cells->quietLast[write != 0] = range->last;
      return;
    }
  }
  // The site that waited is the observer's first, now that Lean code is to run. Had it stopped the run, the run fails, to be run
  // again a step at a time. What doesn't check its budget leaves one where nothing observes code too, which is then nothing's.
  if (cells->pendingSite && cells->codeObserver != nullptr) {
    cells->pendingSite = false;
    cells->leanRan = true;
    if (callCodeObserver(cells, cells->pendingPc) != 0) {
      if (cells->error == nullptr) {
        lean_object *error = lean_mk_io_user_error(lean_mk_string("a code site that waited stops the run"));
        failCells(cells, error);
        lean_dec_ref(error);
      }
      return;
    }
  }
  cells->leanRan = true;
  forgetQuiet(cells);
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

static void putWord(uint8_t *out, uint64_t value) {
  for (size_t byte = 0; byte != 8; ++byte)
    out[byte] = static_cast<uint8_t>(value >> (8 * byte));
}

static uint64_t getWord(const uint8_t *in) {
  uint64_t value = 0;
  for (size_t byte = 0; byte != 8; ++byte)
    value |= static_cast<uint64_t>(in[byte]) << (8 * byte);
  return value;
}

// Of the outputs of a code site, each as its slot and its flag's slot and 1 or 0 for none, eight bytes each, the least significant
// first: those that the run has reached at the site that the Lean code that runs now was called from, and whose slots aren't what was
// last said of them in this run, or weren't said, each as its place among them and its value, which are said of them from now on.
// All of them are new to it after `reset`. Nothing outside of a site, of a run whose slots aren't one array, or at a site, `pc`, of
// optimized code that wasn't made to leave its slots there.
// `Jit.word`: the `index`th word of eight bytes of `bytes`, the least significant first, or 0 past its end.
extern "C" uint64_t bap_jit_word(b_lean_obj_arg bytes, b_lean_obj_arg index) {
  if (!lean_is_scalar(index))
    return 0;
  size_t at = lean_unbox(index);
  if (at >= lean_sarray_size(bytes) / 8)
    return 0;
  return getWord(lean_sarray_cptr(bytes) + 8 * at);
}

extern "C" lean_obj_res bap_jit_live_changes(b_lean_obj_arg outputs, uint64_t pc, uint8_t reset, lean_obj_arg) {
  BapCells *cells = siteCells;
  if (cells == nullptr || cells->slots == nullptr || !(cells->slotsLive || cells->flushedPc == pc))
    return lean_io_result_mk_ok(lean_box(0));
  SiteReport &report = siteReport;
  if (report.serial != cells->serial || reset != 0) {
    report.serial = cells->serial;
    report.values.assign(cells->slotCount, 0);
    report.known.assign(cells->slotCount, 0);
  }
  const uint8_t *in = lean_sarray_cptr(outputs);
  const size_t count = lean_sarray_size(outputs) / 16;
  std::vector<uint64_t> changes;
  for (size_t index = 0; index != count; ++index) {
    uint64_t slot = getWord(in + index * 16);
    uint64_t flag = getWord(in + index * 16 + 8);
    if (slot >= cells->slotCount || (flag != 0 && (flag - 1 >= cells->slotCount || cells->slots[flag - 1] == 0)))
      continue;
    uint64_t value = cells->slots[slot];
    if (report.known[slot] && report.values[slot] == value)
      continue;
    report.known[slot] = 1;
    report.values[slot] = value;
    changes.push_back(index);
    changes.push_back(value);
  }
  lean_obj_res bytes = lean_alloc_sarray(1, changes.size() * 8, changes.size() * 8);
  for (size_t index = 0; index != changes.size(); ++index)
    putWord(lean_sarray_cptr(bytes) + index * 8, changes[index]);
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, bytes);
  return lean_io_result_mk_ok(some);
}

extern "C" uint64_t bap_jit_code_notify(BapCells *cells, uint64_t pc) {
  if (cells->codeObserver == nullptr || cells->error != nullptr)
    return cells->error == nullptr ? 0 : 1;
  if (cells->quietSites && !cells->leanRan) {
    cells->pendingSite = true;
    cells->pendingPc = pc;
    return 0;
  }
  return callCodeObserver(cells, pc);
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
  if (cells->growable != nullptr) {
    cells->growable->push_back(BapCell{address, value});
    cells->items = cells->growable->data();
    cells->size = cells->growable->size();
    cells->capacity = cells->growable->capacity();
  } else if (cells->size < cells->capacity)
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
    cells->changes->note(address, size, bigEndian != 0, value);
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
  // Quiet as the observer would be at any access of the kind there: as it is with no observer, or where the filter lets all of the
  // page through, until Lean code runs, which may change what it lets through.
  auto quiet = [&](bool write) -> uint64_t {
    bool all = cells->observer == nullptr ||
        (!cells->leanRan && cells->filter != nullptr &&
         cells->filter->quietRange(number << PagedMemory::pageBits, PagedMemory::pageSize, write) != nullptr);
    return all ? number + 1 : 0;
  };
  cells->pageEntries[number & (pageEntryCount - 1)] = BapPageEntry{number + 1, page, {quiet(false), quiet(true)}};
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
  // Whether its variables are the chain's registers when it has them.
  bool direct = false;
  // Whether it keeps its slots in registers of the host between its code sites, as what is optimized does.
  bool optimized = false;
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
  // then runs a lot is compiled again with it, by the passes of LLVM and then a code generator a level below the default, which
  // makes about the same of what the passes leave in less than two thirds of the time.
  machine->setCodeGenOptLevel(optimized ? llvm::CodeGenOptLevel::Less : llvm::CodeGenOptLevel::None);
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
// `kept`, for what is optimized, is the slots that what runs it reads afterwards, as obligation 1 says: only those are left in the
// state, so that the rest, the temporaries of expressions, live as long as they are used and not to the end of the run.
// `variables`, for what is optimized, is pairs of a slot of a variable and the variable's number among the registers of a chain.
static lean_obj_res compileOps(lean_obj_arg ops, bool optimized, lean_obj_arg entries = nullptr, size_t entrySlot = 0,
                               lean_obj_arg kept = nullptr, uint64_t budgetSlot = ~uint64_t{0},
                               lean_obj_arg variables = nullptr, b_lean_obj_arg flushSites = nullptr) {
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
    // Of each code site, its branch on whether it has anything to do and its pc; and of each access to memory, the block that it
    // starts, and the branch on whether the memory observer is called for it: the copy that doesn't check its budget has them
    // otherwise, below.
    std::vector<std::pair<llvm::Instruction *, uint64_t>> siteBranches;
    std::vector<std::pair<llvm::Instruction *, llvm::BasicBlock *>> observerBranches;
    // An access starts a block, which the copy can go to in this, as the operation reads all it reads from the slots there.
    auto startAccess = [&]() {
      llvm::BasicBlock *start = llvm::BasicBlock::Create(*context, "access", function);
      builder.CreateBr(start);
      builder.SetInsertPoint(start);
      return start;
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
    // The cell of an access that an instruction can do, on a page that is known with the observer quiet there for accesses of its
    // kind, which then needs no other check: ends with the insertion point where the access is, and `checked` where it isn't.
    auto quietCell = [&](llvm::Value *base, size_t size, bool write, llvm::BasicBlock *checked) -> llvm::Value * {
      llvm::Value *aligned = builder.CreateICmpEQ(
          builder.CreateAnd(base, llvm::ConstantInt::get(word, size - 1)), zero);
      llvm::Value *number = builder.CreateLShr(base, PagedMemory::pageBits);
      llvm::Value *index = builder.CreateAnd(number, llvm::ConstantInt::get(word, pageEntryCount - 1));
      llvm::Value *entryAddress = builder.CreateGEP(byte, memory, builder.CreateAdd(
          llvm::ConstantInt::get(word, offsetof(BapCells, pageEntries)),
          builder.CreateMul(index, llvm::ConstantInt::get(word, sizeof(BapPageEntry)))));
      llvm::Value *tag = builder.CreateLoad(
          word, builder.CreateConstGEP1_64(byte, entryAddress, offsetof(BapPageEntry, quiet) + (write ? 8 : 0)));
      llvm::Value *known = builder.CreateICmpEQ(tag, builder.CreateAdd(number, llvm::ConstantInt::get(word, 1)));
      llvm::BasicBlock *quick = llvm::BasicBlock::Create(*context, "access_quick", function);
      builder.CreateCondBr(builder.CreateAnd(aligned, known), quick, checked);
      builder.SetInsertPoint(quick);
      llvm::Value *page = builder.CreateLoad(pointer, builder.CreateConstGEP1_64(byte, entryAddress, offsetof(BapPageEntry, page)));
      return builder.CreateGEP(byte, page, builder.CreateAnd(base, llvm::ConstantInt::get(word, PagedMemory::pageSize - 1)));
    };
    // The observer of an access, unless it lies within the last range that the filter let one of its kind through in.
    auto notifyAccess = [&](llvm::BasicBlock *start, bool write, llvm::Value *base, size_t size, llvm::Value *value) {
      auto field = [&](size_t offset) {
        return builder.CreateLoad(word, builder.CreateGEP(byte, memory, llvm::ConstantInt::get(word, offset + (write ? 8 : 0))));
      };
      llvm::Value *first = field(offsetof(BapCells, quietFirst));
      llvm::Value *last = field(offsetof(BapCells, quietLast));
      llvm::Value *end = builder.CreateAdd(base, llvm::ConstantInt::get(word, size - 1));
      llvm::Value *quiet = builder.CreateAnd(
          builder.CreateAnd(builder.CreateICmpUGE(base, first), builder.CreateICmpULE(end, last)),
          builder.CreateICmpUGE(end, base));
      llvm::BasicBlock *call = llvm::BasicBlock::Create(*context, "notify_access", function);
      llvm::BasicBlock *after = llvm::BasicBlock::Create(*context, "notify_done", function);
      observerBranches.push_back({builder.CreateCondBr(quiet, after, call), start});
      builder.SetInsertPoint(call);
      builder.CreateCall(notifyMemory,
          {memory, llvm::ConstantInt::get(byte, write ? 1 : 0), base, llvm::ConstantInt::get(word, size), value});
      builder.CreateBr(after);
      builder.SetInsertPoint(after);
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
        llvm::BasicBlock *start = startAccess();
        llvm::Value *base = load(address);
        llvm::Value *endianness = llvm::ConstantInt::get(byte, bigEndian ? 1 : 0);
        llvm::Value *result;
        if (hasInstruction(size)) {
          llvm::BasicBlock *checked = llvm::BasicBlock::Create(*context, "load_checked", function);
          llvm::BasicBlock *slow = llvm::BasicBlock::Create(*context, "load_slow", function);
          llvm::BasicBlock *done = llvm::BasicBlock::Create(*context, "load_done", function);
          llvm::BasicBlock *access = llvm::BasicBlock::Create(*context, "load_cell", function);
          llvm::Value *quick = quietCell(base, size, false, checked);
          llvm::BasicBlock *quickEnd = builder.GetInsertBlock();
          builder.CreateBr(access);
          builder.SetInsertPoint(checked);
          notifyAccess(start, false, base, size, zero);
          llvm::Value *paged = pageForAccess(base, size, false, slow);
          llvm::BasicBlock *pagedEnd = builder.GetInsertBlock();
          builder.CreateBr(access);
          builder.SetInsertPoint(access);
          llvm::PHINode *cell = builder.CreatePHI(pointer, 2);
          cell->addIncoming(quick, quickEnd);
          cell->addIncoming(paged, pagedEnd);
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
          notifyAccess(start, false, base, size, zero);
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
        llvm::BasicBlock *start = startAccess();
        llvm::Value *base = load(address);
        llvm::Value *stored = load(value);
        llvm::Value *endianness = llvm::ConstantInt::get(byte, bigEndian ? 1 : 0);
        llvm::Value *sizeValue = llvm::ConstantInt::get(word, size);
        if (hasInstruction(size)) {
          llvm::BasicBlock *checked = llvm::BasicBlock::Create(*context, "store_checked", function);
          llvm::BasicBlock *slow = llvm::BasicBlock::Create(*context, "store_slow", function);
          llvm::BasicBlock *done = llvm::BasicBlock::Create(*context, "store_done", function);
          llvm::BasicBlock *access = llvm::BasicBlock::Create(*context, "store_cell", function);
          llvm::Value *quick = quietCell(base, size, true, checked);
          llvm::BasicBlock *quickEnd = builder.GetInsertBlock();
          builder.CreateBr(access);
          builder.SetInsertPoint(checked);
          notifyAccess(start, true, base, size, stored);
          llvm::Value *paged = pageForAccess(base, size, true, slow);
          llvm::BasicBlock *pagedEnd = builder.GetInsertBlock();
          builder.CreateBr(access);
          builder.SetInsertPoint(access);
          llvm::PHINode *cell = builder.CreatePHI(pointer, 2);
          cell->addIncoming(quick, quickEnd);
          cell->addIncoming(paged, pagedEnd);
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
          notifyAccess(start, true, base, size, stored);
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
        // What `bap_jit_code_notify` does without running Lean code is done here, without a call, which would keep what is in the
        // registers of the host from staying there across it: nothing where nothing observes code, and where a site would only set
        // the pc, it waits as the pending one. Anything else is the call's.
        auto cellsField = [&](llvm::Type *type, size_t offset) {
          return builder.CreateLoad(type, builder.CreateGEP(byte, memory, llvm::ConstantInt::get(word, offset)));
        };
        llvm::Value *observed = builder.CreateIsNotNull(cellsField(pointer, offsetof(BapCells, codeObserver)));
        llvm::Value *fine = builder.CreateIsNull(cellsField(pointer, offsetof(BapCells, error)));
        llvm::Value *waits = builder.CreateAnd(
            builder.CreateICmpNE(cellsField(byte, offsetof(BapCells, quietSites)), llvm::ConstantInt::get(byte, 0)),
            builder.CreateICmpEQ(cellsField(byte, offsetof(BapCells, leanRan)), llvm::ConstantInt::get(byte, 0)));
        llvm::BasicBlock *pendBlock = llvm::BasicBlock::Create(*context, "code_pend", function);
        llvm::BasicBlock *decideBlock = llvm::BasicBlock::Create(*context, "code_decide", function);
        llvm::BasicBlock *callBlock = llvm::BasicBlock::Create(*context, "code_call", function);
        siteBranches.push_back({builder.CreateCondBr(builder.CreateAnd(fine, builder.CreateNot(observed)), continueBlock, decideBlock), pc});
        builder.SetInsertPoint(decideBlock);
        builder.CreateCondBr(builder.CreateAnd(fine, waits), pendBlock, callBlock);
        builder.SetInsertPoint(pendBlock);
        builder.CreateStore(llvm::ConstantInt::get(byte, 1),
                            builder.CreateGEP(byte, memory, llvm::ConstantInt::get(word, offsetof(BapCells, pendingSite))));
        builder.CreateStore(llvm::ConstantInt::get(word, pc),
                            builder.CreateGEP(byte, memory, llvm::ConstantInt::get(word, offsetof(BapCells, pendingPc))));
        builder.CreateBr(continueBlock);
        builder.SetInsertPoint(callBlock);
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

    // A copy of what is optimized that doesn't leave at each block for its budget, as QEMU counts instructions once a translation: as
    // a run enters each block at most once between targets of jumps back, which every way round a loop goes through, the budget is
    // checked against all the blocks there are at the start and at each of those, and while it is enough the copy goes on, and
    // otherwise this, which checks at each block. It does what this does, as each check here would have gone on, and what is only
    // there for a block to leave with, such as the flags that the next instruction sets again, is then for nothing and goes.
    // Nor does it run Lean code, and so it is only for where a code site would only wait as the pending one, as Lean code hasn't run
    // and nothing observes code but the observer of a range, or where nothing does at all: a site waits there, which is two stores
    // and no way out, which would keep what a later instruction overwrites. An access that the memory observer is to hear of goes
    // on in this, from the start of the access, which calls it, and this goes on from there by the checks at the targets of its
    // jumps back as before, which come back to the copy if Lean code didn't run. What waits in the copy is a variable of the
    // function's, which LLVM keeps in a register, and is left in the cells where it goes on in this: the copy runs no Lean code to
    // read it there, and a store to them at each site would be most of what it does.
    llvm::AllocaInst *pending = nullptr;
    if (optimized && entries == nullptr && budgetSlot != ~uint64_t{0} && hasSlots && budgetSlot <= maxSlot) {
      auto budgetBranch = [&](llvm::Instruction *terminator) -> llvm::CondBrInst * {
        auto *branch = llvm::dyn_cast<llvm::CondBrInst>(terminator);
        if (branch == nullptr)
          return nullptr;
        auto *compare = llvm::dyn_cast<llvm::ICmpInst>(branch->getCondition());
        if (compare == nullptr || compare->getPredicate() != llvm::ICmpInst::ICMP_NE)
          return nullptr;
        auto *zeroValue = llvm::dyn_cast<llvm::ConstantInt>(compare->getOperand(1));
        auto *loaded = llvm::dyn_cast<llvm::LoadInst>(compare->getOperand(0));
        if (zeroValue == nullptr || !zeroValue->isZero() || loaded == nullptr)
          return nullptr;
        auto *address = llvm::dyn_cast<llvm::GetElementPtrInst>(loaded->getPointerOperand());
        if (address == nullptr || address->getPointerOperand() != state || address->getNumOperands() != 2)
          return nullptr;
        auto *index = llvm::dyn_cast<llvm::ConstantInt>(address->getOperand(1));
        return index != nullptr && index->getZExtValue() == budgetSlot ? branch : nullptr;
      };
      std::vector<llvm::BasicBlock *> original;
      for (llvm::BasicBlock &block : *function)
        original.push_back(&block);
      uint64_t checks = 0;
      for (llvm::BasicBlock *block : original)
        if (budgetBranch(block->getTerminator()) != nullptr)
          ++checks;
      if (checks != 0) {
        // A copy of each block and instruction, with what they use of each other the copy's.
        std::unordered_map<llvm::Value *, llvm::Value *> map;
        std::vector<llvm::BasicBlock *> copies;
        for (llvm::BasicBlock *block : original) {
          llvm::BasicBlock *copy = llvm::BasicBlock::Create(*context, block->getName() + ".fast", function);
          map[block] = copy;
          copies.push_back(copy);
        }
        for (size_t at = 0; at != original.size(); ++at)
          for (llvm::Instruction &instruction : *original[at]) {
            llvm::Instruction *copy = instruction.clone();
            copy->insertInto(copies[at], copies[at]->end());
            map[&instruction] = copy;
          }
        for (llvm::BasicBlock *copy : copies)
          for (llvm::Instruction &instruction : *copy) {
            for (unsigned index = 0; index != instruction.getNumOperands(); ++index) {
              auto found = map.find(instruction.getOperand(index));
              if (found != map.end())
                instruction.setOperand(index, found->second);
            }
            if (auto *phi = llvm::dyn_cast<llvm::PHINode>(&instruction))
              for (unsigned index = 0; index != phi->getNumIncomingValues(); ++index)
                phi->setIncomingBlock(index, llvm::cast<llvm::BasicBlock>(map[phi->getIncomingBlock(index)]));
          }
        for (llvm::BasicBlock *copy : copies)
          if (llvm::CondBrInst *branch = budgetBranch(copy->getTerminator())) {
            llvm::BasicBlock *go = branch->getSuccessor(0);
            branch->eraseFromParent();
            builder.SetInsertPoint(copy);
            builder.CreateBr(go);
          }
        builder.SetInsertPoint(original.front(), original.front()->getFirstInsertionPt());
        pending = builder.CreateAlloca(word, nullptr, "pending");
        for (auto &[site, pc] : siteBranches) {
          auto *branch = llvm::cast<llvm::Instruction>(map[site]);
          llvm::BasicBlock *block = branch->getParent();
          llvm::BasicBlock *go = branch->getSuccessor(0);
          branch->eraseFromParent();
          builder.SetInsertPoint(block);
          builder.CreateStore(llvm::ConstantInt::get(word, pc + 1), pending);
          builder.CreateBr(go);
        }
        // From the copy to this: what waits, as the cells have it, the pc and one more, or nothing.
        std::vector<llvm::BasicBlock *> edges;
        auto toThis = [&](llvm::BasicBlock *target) {
          llvm::BasicBlock *edge = llvm::BasicBlock::Create(*context, "to_checked", function);
          edges.push_back(edge);
          builder.SetInsertPoint(edge);
          llvm::Value *waiting = builder.CreateLoad(word, pending);
          builder.CreateStore(builder.CreateZExt(builder.CreateICmpNE(waiting, zero), byte),
                              builder.CreateConstGEP1_64(byte, memory, offsetof(BapCells, pendingSite)));
          builder.CreateStore(builder.CreateSub(waiting, llvm::ConstantInt::get(word, 1)),
                              builder.CreateConstGEP1_64(byte, memory, offsetof(BapCells, pendingPc)));
          builder.CreateBr(target);
          return edge;
        };
        for (auto &[observed, start] : observerBranches)
          llvm::cast<llvm::Instruction>(map[observed])->setSuccessor(1, toThis(start));
        // The targets of the jumps back of the copy, by a search in depth from its start, which stays in the copy: an access goes on in
        // this.
        std::unordered_map<llvm::BasicBlock *, int> visit;
        std::vector<llvm::BasicBlock *> targets;
        std::vector<std::pair<llvm::BasicBlock *, unsigned>> stack{{copies.front(), 0}};
        visit[copies.front()] = 1;
        while (!stack.empty()) {
          auto &[block, at] = stack.back();
          llvm::Instruction *terminator = block->getTerminator();
          if (at < terminator->getNumSuccessors()) {
            llvm::BasicBlock *successor = terminator->getSuccessor(at++);
            if (map.count(successor) != 0)
              continue;
            int &mark = visit[successor];
            if (mark == 1)
              targets.push_back(successor);
            else if (mark == 0) {
              mark = 1;
              stack.push_back({successor, 0});
            }
          } else {
            visit[block] = 2;
            stack.pop_back();
          }
        }
        bool plain = true;
        for (llvm::BasicBlock *target : targets)
          plain = plain && !llvm::isa<llvm::PHINode>(target->front());
        std::unordered_map<llvm::BasicBlock *, llvm::BasicBlock *> originalOf;
        for (size_t at = 0; at != original.size(); ++at)
          originalOf[copies[at]] = original[at];
        // From the copy, only its budget: nothing in it runs Lean code, which is what could change the rest.
        auto checked = [&](llvm::BasicBlock *fast, llvm::BasicBlock *slow, const char *name, bool fromCopy) {
          llvm::BasicBlock *check = llvm::BasicBlock::Create(*context, name, function, fast);
          builder.SetInsertPoint(check);
          llvm::Value *budget = builder.CreateLoad(word, builder.CreateConstGEP1_64(word, state, budgetSlot));
          llvm::Value *enough = builder.CreateICmpUGE(budget, llvm::ConstantInt::get(word, checks));
          // The copy is the way that a run goes, for where LLVM puts its loops.
          llvm::MDNode *likely = llvm::MDBuilder(*context).createLikelyBranchWeights();
          if (fromCopy) {
            llvm::BasicBlock *edge = toThis(slow);
            builder.SetInsertPoint(check);
            builder.CreateCondBr(enough, fast, edge, likely);
            return check;
          }
          llvm::Value *waits = builder.CreateICmpNE(
              builder.CreateLoad(byte, builder.CreateConstGEP1_64(byte, memory, offsetof(BapCells, pendingSite))),
              llvm::ConstantInt::get(byte, 0));
          llvm::Value *waitingPc = builder.CreateLoad(word, builder.CreateConstGEP1_64(byte, memory, offsetof(BapCells, pendingPc)));
          builder.CreateStore(builder.CreateSelect(waits, builder.CreateAdd(waitingPc, llvm::ConstantInt::get(word, 1)), zero), pending);
          auto field = [&](llvm::Type *type, size_t offset) {
            return builder.CreateLoad(type, builder.CreateConstGEP1_64(byte, memory, offset));
          };
          llvm::Value *sitesWait = builder.CreateAnd(
              builder.CreateIsNull(field(pointer, offsetof(BapCells, error))),
              builder.CreateOr(builder.CreateIsNull(field(pointer, offsetof(BapCells, codeObserver))), builder.CreateAnd(
                  builder.CreateICmpNE(field(byte, offsetof(BapCells, quietSites)), llvm::ConstantInt::get(byte, 0)),
                  builder.CreateICmpEQ(field(byte, offsetof(BapCells, leanRan)), llvm::ConstantInt::get(byte, 0)))));
          builder.CreateCondBr(builder.CreateAnd(enough, sitesWait), fast, slow, likely);
          return check;
        };
        if (plain) {
          std::sort(targets.begin(), targets.end());
          targets.erase(std::unique(targets.begin(), targets.end()), targets.end());
          auto usersOf = [](llvm::BasicBlock *block) {
            std::vector<llvm::Instruction *> users;
            for (llvm::User *user : block->users())
              if (auto *instruction = llvm::dyn_cast<llvm::Instruction>(user))
                users.push_back(instruction);
            return users;
          };
          for (llvm::BasicBlock *target : targets) {
            // This comes back to the copy there too, as an access that went on in this did.
            llvm::BasicBlock *original = originalOf[target];
            std::vector<llvm::Instruction *> users = usersOf(target);
            std::vector<llvm::Instruction *> originalUsers = usersOf(original);
            llvm::BasicBlock *check = checked(target, original, "budget_check", true);
            for (llvm::Instruction *user : users)
              user->replaceUsesOfWith(target, check);
            llvm::BasicBlock *back = checked(target, original, "budget_back", false);
            for (llvm::Instruction *user : originalUsers)
              user->replaceUsesOfWith(original, back);
          }
          llvm::BasicBlock *start = original.front();
          llvm::BasicBlock *choose = checked(llvm::cast<llvm::BasicBlock>(map[start]), start, "budget_start", false);
          choose->moveBefore(start);
        } else {
          for (llvm::BasicBlock *copy : copies)
            copy->eraseFromParent();
          for (llvm::BasicBlock *edge : edges)
            edge->eraseFromParent();
        }
      }
    }

    // What is optimized works on a copy of the slots on the stack, which LLVM keeps in registers, and leaves those it wrote in the
    // state at each return, as obligation 1 says: then a value isn't stored and loaded again for each operation, and what is
    // overwritten before anything reads it, such as most flags, isn't worked out at all.
    if (optimized && hasSlots) {
      const size_t slotCount = entries != nullptr ? std::max(maxSlot + 1, entrySlot + 1) : maxSlot + 1;
      llvm::BasicBlock *first = &function->getEntryBlock();
      llvm::BasicBlock *promote = llvm::BasicBlock::Create(*context, "promote", function, first);
      builder.SetInsertPoint(promote);
      std::vector<llvm::AllocaInst *> copies(slotCount);
      for (size_t index = 0; index != slotCount; ++index)
        copies[index] = builder.CreateAlloca(word);
      if (pending != nullptr)
        pending->moveBefore(*promote, promote->end());
      std::vector<bool> written(slotCount, false);
      std::vector<llvm::GetElementPtrInst *> addresses;
      for (llvm::User *user : state->users())
        if (auto *address = llvm::dyn_cast<llvm::GetElementPtrInst>(user))
          addresses.push_back(address);
      for (llvm::GetElementPtrInst *address : addresses) {
        auto *index = llvm::dyn_cast<llvm::ConstantInt>(address->getOperand(1));
        if (address->getNumOperands() != 2 || index == nullptr || index->getZExtValue() >= slotCount)
          return ioError("a JIT slot address that isn't a constant slot");
        size_t slot = static_cast<size_t>(index->getZExtValue());
        for (llvm::User *user : address->users())
          if (auto *store = llvm::dyn_cast<llvm::StoreInst>(user))
            if (store->getPointerOperand() == address)
              written[slot] = true;
        address->replaceAllUsesWith(copies[slot]);
        address->eraseFromParent();
      }
      // Where each slot is between runs: a variable's is the chain's register of it when there are registers, and the state's
      // otherwise, as for every other slot.
      std::vector<llvm::Value *> homes(slotCount);
      llvm::Value *registers = builder.CreateLoad(pointer, builder.CreateConstGEP1_64(byte, memory, offsetof(BapCells, registers)));
      llvm::Value *chained = builder.CreateIsNotNull(registers);
      for (size_t index = 0; index != slotCount; ++index)
        homes[index] = builder.CreateConstGEP1_64(word, state, index);
      if (variables != nullptr)
        for (size_t at = 0; at + 1 < lean_array_size(variables); at += 2) {
          uint64_t slot = lean_unbox_uint64(lean_array_get_core(variables, at));
          uint64_t number = lean_unbox_uint64(lean_array_get_core(variables, at + 1));
          if (slot < slotCount)
            homes[slot] = builder.CreateSelect(chained, builder.CreateConstGEP1_64(word, registers, number), homes[slot]);
        }
      for (size_t index = 0; index != slotCount; ++index)
        builder.CreateStore(builder.CreateLoad(word, homes[index]), copies[index]);
      builder.CreateBr(first);
      // A code site that calls Lean code leaves what it wrote in the slots first, where what that runs reads them, and says so: only
      // at the sites that it was told of, which have hooks to read them, where it calls, and only those that are read after a run,
      // the outputs, checkpoints and flags. Elsewhere what a site would leave would have to be worked out at each, where a later
      // instruction overwrites it, as most flags are, and the rest are temporaries that nothing reads.
      std::vector<uint64_t> flushPcs;
      if (flushSites != nullptr)
        for (size_t index = 0; index != lean_array_size(flushSites); ++index)
          flushPcs.push_back(lean_unbox_uint64(lean_array_get_core(flushSites, index)));
      std::vector<bool> readAfter(slotCount, kept == nullptr);
      if (kept != nullptr)
        for (size_t index = 0; index != lean_array_size(kept); ++index) {
          uint64_t slot = lean_unbox_uint64(lean_array_get_core(kept, index));
          if (slot < slotCount)
            readAfter[slot] = true;
        }
      std::vector<llvm::CallInst *> sites;
      for (llvm::BasicBlock &block : *function)
        for (llvm::Instruction &instruction : block)
          if (auto *call = llvm::dyn_cast<llvm::CallInst>(&instruction))
            if (call->getCalledFunction() != nullptr && call->getCalledFunction()->getName() == "bap_jit_code_notify")
              sites.push_back(call);
      for (llvm::CallInst *call : sites) {
        auto *pc = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (pc == nullptr || std::find(flushPcs.begin(), flushPcs.end(), pc->getZExtValue()) == flushPcs.end())
          continue;
        builder.SetInsertPoint(call);
        for (size_t index = 0; index != slotCount; ++index)
          if (written[index] && readAfter[index])
            builder.CreateStore(builder.CreateLoad(word, copies[index]), homes[index]);
        builder.CreateStore(pc, builder.CreateGEP(byte, memory, llvm::ConstantInt::get(word, offsetof(BapCells, flushedPc))));
      }
      // One way out, which leaves the slots in the state once, rather than at each return.
      std::vector<llvm::ReturnInst *> returns;
      for (llvm::BasicBlock &block : *function)
        if (auto *ret = llvm::dyn_cast<llvm::ReturnInst>(block.getTerminator()))
          returns.push_back(ret);
      llvm::BasicBlock *leave = llvm::BasicBlock::Create(*context, "leave", function);
      builder.SetInsertPoint(leave);
      llvm::PHINode *result = builder.CreatePHI(word, static_cast<unsigned>(returns.size()));
      if (kept != nullptr) {
        std::vector<bool> keep(slotCount, false);
        for (size_t index = 0; index != lean_array_size(kept); ++index) {
          uint64_t slot = lean_unbox_uint64(lean_array_get_core(kept, index));
          if (slot < slotCount)
            keep[slot] = true;
        }
        for (size_t index = 0; index != slotCount; ++index)
          written[index] = written[index] && keep[index];
      }
      for (size_t index = 0; index != slotCount; ++index)
        if (written[index])
          builder.CreateStore(builder.CreateLoad(word, copies[index]), homes[index]);
      builder.CreateRet(result);
      for (llvm::ReturnInst *ret : returns) {
        llvm::BasicBlock *block = ret->getParent();
        result->addIncoming(ret->getReturnValue(), block);
        ret->eraseFromParent();
        builder.SetInsertPoint(block);
        builder.CreateBr(leave);
      }
      llvm::LoopAnalysisManager loops;
      llvm::FunctionAnalysisManager functions;
      llvm::CGSCCAnalysisManager calls;
      llvm::ModuleAnalysisManager modules;
      llvm::PassBuilder passes;
      passes.registerModuleAnalyses(modules);
      passes.registerCGSCCAnalyses(calls);
      passes.registerFunctionAnalyses(functions);
      passes.registerLoopAnalyses(loops);
      passes.crossRegisterProxies(loops, functions, calls, modules);
      // What makes the slots registers and drops what nothing reads, which is most of what any pipeline of LLVM does for this code,
      // for less than its O1 takes to compile.
      llvm::FunctionPassManager pipeline;
      pipeline.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      pipeline.addPass(llvm::EarlyCSEPass(true));
      pipeline.addPass(llvm::InstCombinePass());
      pipeline.addPass(llvm::SimplifyCFGPass());
      // Again, for the selects that SimplifyCFG makes of what waits in the copy that doesn't check its budget, one at each site
      // that a slot of the run guards, which fold into one rather than going round the loop one after another.
      pipeline.addPass(llvm::InstCombinePass());
      pipeline.addPass(llvm::DSEPass());
      // What only a code site that calls Lean code writes back goes where it does, rather than being worked out at every site.
      pipeline.addPass(llvm::SinkingPass());
      pipeline.addPass(llvm::ADCEPass());
      pipeline.run(*function, functions);
      if (llvm::verifyModule(*module, &verificationStream))
        return ioError("invalid optimized LLVM JIT module: " + verificationErrors);
    }

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
    program->direct = optimized && variables != nullptr && hasSlots;
    program->optimized = optimized && hasSlots;
    program->maxSlot = entries != nullptr ? std::max(hasSlots ? maxSlot + 1 : 0, entrySlot + 1) : (hasSlots ? maxSlot + 1 : 0);
    program->memoryStores = memoryStores;
    return lean_io_result_mk_ok(
        lean_alloc_external(programClass(), program.release()));
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT compilation failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_compile(lean_obj_arg ops, lean_obj_arg) { return compileOps(ops, false); }

extern "C" lean_obj_res bap_jit_compile_optimized(lean_obj_arg ops, lean_obj_arg kept, uint64_t budgetSlot, lean_obj_arg variables,
                                                   b_lean_obj_arg flushSites, lean_obj_arg) {
  return compileOps(ops, true, nullptr, 0, kept, budgetSlot, variables, flushSites);
}

extern "C" lean_obj_res bap_jit_compile_entries(lean_obj_arg ops, lean_obj_arg entries, lean_obj_arg slot, uint8_t optimized,
                                                 lean_obj_arg kept, lean_obj_arg variables, b_lean_obj_arg flushSites,
                                                 lean_obj_arg) {
  size_t entrySlot;
  if (!getSlot(slot, entrySlot))
    return ioError("invalid JIT entry slot");
  return compileOps(ops, optimized != 0, entries, entrySlot, optimized != 0 ? kept : nullptr, ~uint64_t{0},
                    optimized != 0 ? variables : nullptr, optimized != 0 ? flushSites : nullptr);
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
    memory.slots = state.data();
    memory.slotCount = size;
    memory.slotsLive = !program->optimized;
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
    memory.growable = &cells;
    memory.slots = state.data();
    memory.slotCount = stateSize;
    memory.slotsLive = !program->optimized;
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

// `Jit.resident`: the bytes of the pieces of `Jit.pieces`, counted without making them.
extern "C" lean_obj_res bap_bytes_resident(lean_obj_arg dataObject) {
  const size_t size = lean_sarray_size(dataObject);
  const uint8_t *data = lean_sarray_cptr(dataObject);
  size_t total = 0;
  for (size_t start = 0; start < size; start += 4096) {
    const size_t count = std::min<size_t>(4096, size - start);
    if (!allZero(data + start, count)) total += count;
  }
  lean_dec(dataObject);
  return lean_usize_to_nat(total);
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

namespace {
void finalizeFilter(void *data) { delete static_cast<MemoryFilter *>(data); }
void foreachFilter(void *, b_lean_obj_arg) {}

lean_external_class *filterClass() {
  static lean_external_class *cls = lean_register_external_class(finalizeFilter, foreachFilter);
  return cls;
}
}

extern "C" lean_obj_res bap_jit_memory_filter_create(lean_obj_arg firstsObject, lean_obj_arg lastsObject,
                                                       lean_obj_arg quietObject, lean_obj_arg) {
  try {
    const size_t count = lean_array_size(firstsObject);
    if (lean_array_size(lastsObject) != count || lean_array_size(quietObject) != count)
      return ioError("JIT memory filter ranges have different lengths");
    auto *filter = new MemoryFilter;
    for (size_t index = 0; index != count; ++index) {
      uint64_t first = lean_unbox_uint64(lean_array_get_core(firstsObject, index));
      uint64_t last = lean_unbox_uint64(lean_array_get_core(lastsObject, index));
      uint8_t quiet = static_cast<uint8_t>(lean_unbox(lean_array_get_core(quietObject, index)));
      if (!filter->insert(MemoryFilter::Range{first, last, (quiet & 1) != 0, (quiet & 2) != 0})) {
        delete filter;
        return ioError("JIT memory filter ranges are not apart");
      }
    }
    return lean_io_result_mk_ok(lean_alloc_external(filterClass(), filter));
  } catch (const std::exception &error) {
    return ioError(std::string("JIT memory filter creation failed: ") + error.what());
  }
}

// Takes out the ranges that start at `removed`, then puts in those given: true if they are all apart, and false, with the filter as
// it may then be, otherwise, which is not to be used again.
extern "C" lean_obj_res bap_jit_memory_filter_update(lean_obj_arg filterObject, lean_obj_arg removedObject,
                                                       lean_obj_arg firstsObject, lean_obj_arg lastsObject,
                                                       lean_obj_arg quietObject, lean_obj_arg) {
  auto *filter = static_cast<MemoryFilter *>(lean_get_external_data(filterObject));
  for (size_t index = 0; index != lean_array_size(removedObject); ++index)
    filter->ranges.erase(lean_unbox_uint64(lean_array_get_core(removedObject, index)));
  const size_t count = lean_array_size(firstsObject);
  if (lean_array_size(lastsObject) != count || lean_array_size(quietObject) != count)
    return lean_io_result_mk_ok(lean_box(0));
  for (size_t index = 0; index != count; ++index) {
    uint64_t first = lean_unbox_uint64(lean_array_get_core(firstsObject, index));
    uint64_t last = lean_unbox_uint64(lean_array_get_core(lastsObject, index));
    uint8_t quiet = static_cast<uint8_t>(lean_unbox(lean_array_get_core(quietObject, index)));
    if (!filter->insert(MemoryFilter::Range{first, last, (quiet & 1) != 0, (quiet & 2) != 0}))
      return lean_io_result_mk_ok(lean_box(0));
  }
  return lean_io_result_mk_ok(lean_box(1));
}

static lean_obj_res runMemoryObject(lean_obj_arg programObject, lean_obj_arg stateObject, lean_obj_arg memoryObject,
                                    const MemoryFilter *filter, bool quietSites, lean_obj_arg observerObject,
                                    lean_obj_arg codeObserverObject) {
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
    StoreLog changes;
    BapCells memory{nullptr, 0, 0, observer, nullptr, persistent, &changes, codeObserver};
    memory.filter = filter;
    memory.quietSites = quietSites;
    memory.slots = state.data();
    memory.slotCount = stateSize;
    memory.slotsLive = !program->optimized;
    uint64_t next = program->function(state.data(), &memory);
    // Before anything else, as this is what a run that failed leaves to be taken back.
    if (persistent->stepActive())
      changes.forEach([&](uint64_t address, uint8_t) { persistent->noteStep(address, 1); });
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

// What a run goes on with in native code from one range to the next, as Lean would between them (obligation 17): the ranges by where
// they start, what each has of the variables in its slots, and the variables as they are between ranges, by their numbers.
struct ChainEntry {
  lean_object *program = nullptr;
  uint64_t id = 0;
  size_t slotCount = 0;
  static constexpr uint64_t none = ~uint64_t{0};
  uint64_t effectSlot = none, budgetSlot = none, observedSlot = none;
  // How many times what it starts at ran, as Lean counts them, and how many make it worth optimizing, none if it is: a run that gets
  // there goes back to Lean, which compiles it again.
  uint64_t executions = 0, optimizeAt = none;
  std::vector<std::pair<uint64_t, uint64_t>> layout;   // variable, slot
  std::vector<uint64_t> required;                      // what has to be bound
  // The slots that a run reads before it writes, and that aren't of the layout or for control: the effect, the flags of outputs, and
  // where a run with entries starts, which are 0 at its start. The rest are temporaries that it writes before it reads them.
  std::vector<uint64_t> zeroed;
  // An output with the slot of its flag, none if it is always written.
  struct Output { uint64_t variable, slot, width, flag = none; };
  std::vector<Output> outputs;
  // Those of them with a flag, which have to be looked at each time, where the others only once a run.
  std::vector<Output> flagged;
  std::vector<std::pair<uint64_t, uint64_t>> flags;    // slot of an output, slot that says it was written
  std::unordered_map<uint64_t, std::vector<Output>> checkpoints;
  // Where it went last and what is there, so that a jump that goes where it went needs no search, as QEMU patches its jumps.
  uint64_t lastNext = none;
  ChainEntry *lastTarget = nullptr;
  // Whether its program reads and writes its variables in the registers of the chain.
  bool direct = false;
  // The run of the chain in which its outputs that are always written were said to be, and in which what it needs was found bound,
  // which, as what is bound stays so in a run, holds for the rest of it.
  uint64_t outputsSaid = 0, readyIn = 0;
  // What a run of the chain did of it, to say at its end.
  bool touched = false;
  uint64_t runs = 0, executed = 0;
};

struct Chain {
  std::unordered_map<uint64_t, ChainEntry> entries;
  // Which run of it this is, from 1.
  uint64_t run = 0;
  ~Chain() { clear(); }
  void clear() {
    for (auto &entry : entries)
      lean_dec_ref(entry.second.program);
    entries.clear();
  }
};

namespace {
void finalizeChain(void *data) { delete static_cast<Chain *>(data); }
void foreachChain(void *, b_lean_obj_arg) {}
lean_external_class *chainClass() {
  static lean_external_class *cls = lean_register_external_class(finalizeChain, foreachChain);
  return cls;
}
}

extern "C" lean_obj_res bap_jit_chain_create(lean_obj_arg) {
  return lean_io_result_mk_ok(lean_alloc_external(chainClass(), new Chain));
}

extern "C" lean_obj_res bap_jit_chain_clear(lean_obj_arg chainObject, lean_obj_arg) {
  static_cast<Chain *>(lean_get_external_data(chainObject))->clear();
  return lean_io_result_mk_ok(lean_box(0));
}

// Whether the range of a chain at `pc` is `program`, which it isn't once Lean has put another there, such as one optimized.
extern "C" uint8_t bap_jit_chain_holds(lean_obj_arg chainObject, uint64_t pc, lean_obj_arg programObject) {
  auto *chain = static_cast<Chain *>(lean_get_external_data(chainObject));
  auto found = chain->entries.find(pc);
  return found != chain->entries.end() && found->second.program == programObject;
}

// That the range of a chain at `pc` is being optimized: it is gone on to for `executions` more, and then comes back to Lean to see if
// what was compiled is there.
extern "C" lean_obj_res bap_jit_chain_optimizing(lean_obj_arg chainObject, uint64_t pc, uint64_t executions, lean_obj_arg) {
  auto *chain = static_cast<Chain *>(lean_get_external_data(chainObject));
  auto found = chain->entries.find(pc);
  if (found != chain->entries.end())
    found->second.optimizeAt = found->second.executions + executions;
  return lean_io_result_mk_ok(lean_box(0));
}

// What a range is, in one array: the number of slots, the effect, budget and observed slots (all ones for none), the layout as its
// length and pairs, the variables that have to be bound, the outputs as triples, the flags as pairs, and the checkpoints, each a pc
// and its outputs.
extern "C" lean_obj_res bap_jit_chain_add(lean_obj_arg chainObject, uint64_t pc, uint64_t id, lean_obj_arg programObject,
                                            lean_obj_arg dataObject, lean_obj_arg) {
  auto *chain = static_cast<Chain *>(lean_get_external_data(chainObject));
  const size_t size = lean_array_size(dataObject);
  size_t at = 0;
  bool bad = false;
  auto next = [&]() -> uint64_t {
    if (at >= size) { bad = true; return 0; }
    return lean_unbox_uint64(lean_array_get_core(dataObject, at++));
  };
  ChainEntry entry;
  entry.id = id;
  entry.slotCount = static_cast<size_t>(next());
  entry.effectSlot = next();
  entry.budgetSlot = next();
  entry.observedSlot = next();
  entry.executions = next();
  entry.optimizeAt = next();
  for (uint64_t count = next(); count != 0 && !bad; --count) entry.zeroed.push_back(next());
  for (uint64_t count = next(); count != 0 && !bad; --count) { uint64_t v = next(); entry.layout.push_back({v, next()}); }
  for (uint64_t count = next(); count != 0 && !bad; --count) entry.required.push_back(next());
  auto outputs = [&](std::vector<ChainEntry::Output> &into) {
    for (uint64_t count = next(); count != 0 && !bad; --count) {
      uint64_t v = next(); uint64_t slot = next(); into.push_back({v, slot, next()});
    }
  };
  outputs(entry.outputs);
  for (uint64_t count = next(); count != 0 && !bad; --count) { uint64_t o = next(); entry.flags.push_back({o, next()}); }
  for (uint64_t count = next(); count != 0 && !bad; --count) {
    uint64_t checkpoint = next();
    outputs(entry.checkpoints[checkpoint]);
  }
  auto *program = static_cast<Program *>(lean_get_external_data(programObject));
  auto fits = [&](uint64_t slot) { return slot == ChainEntry::none || slot < entry.slotCount; };
  bad = bad || at != size || entry.slotCount < program->maxSlot || !fits(entry.effectSlot) || !fits(entry.budgetSlot) ||
        !fits(entry.observedSlot);
  for (auto &binding : entry.layout) bad = bad || binding.second >= entry.slotCount;
  for (auto &output : entry.outputs) bad = bad || output.slot >= entry.slotCount || output.width == 0 || output.width > 64;
  for (auto &flag : entry.flags) bad = bad || flag.second >= entry.slotCount;
  for (uint64_t slot : entry.zeroed) bad = bad || slot >= entry.slotCount;
  for (auto &checkpoint : entry.checkpoints)
    for (auto &output : checkpoint.second) bad = bad || output.slot >= entry.slotCount || output.width == 0 || output.width > 64;
  if (bad)
    return ioError("invalid JIT chain entry");
  auto flagOf = [&](ChainEntry::Output &output) {
    for (const auto &flag : entry.flags)
      if (flag.first == output.slot) { output.flag = flag.second; return; }
  };
  for (auto &output : entry.outputs) {
    flagOf(output);
    if (output.flag != ChainEntry::none) entry.flagged.push_back(output);
  }
  for (auto &checkpoint : entry.checkpoints)
    for (auto &output : checkpoint.second) flagOf(output);
  auto found = chain->entries.find(pc);
  if (found != chain->entries.end()) {
    // What went to the one that goes is to look again.
    for (auto &other : chain->entries) other.second.lastTarget = nullptr;
    lean_dec_ref(found->second.program);
    chain->entries.erase(found);
  }
  lean_inc_ref(programObject);
  entry.program = programObject;
  entry.direct = program->direct;
  chain->entries.emplace(pc, std::move(entry));
  return lean_io_result_mk_ok(lean_box(0));
}

// A run of the range of `firstId` and of those that it goes on to, as a run of each in turn with what Lean would have made of the
// state in between (obligation 17). It stops at what Lean has to see: no range where it goes, a variable that isn't bound, the end of
// the budget, an observer that ran Lean code, or an end that isn't a jump. What it gives back is what the run of the last range gives,
// and, before that, the variables that the others wrote, the blocks entered after the first of all, and how many times each ran.
extern "C" lean_obj_res bap_jit_run_chain(lean_obj_arg programObject, lean_obj_arg stateObject, lean_obj_arg memoryObject,
                                            lean_obj_arg filterObject, uint8_t quietSites, lean_obj_arg observerObject,
                                            lean_obj_arg codeObserverObject, lean_obj_arg chainObject, uint64_t firstId,
                                            uint64_t firstPc, uint64_t firstBudget, lean_obj_arg variablesObject,
                                            lean_obj_arg valuesObject, uint64_t variableCount, lean_obj_arg) {
  try {
    auto *chain = static_cast<Chain *>(lean_get_external_data(chainObject));
    auto *persistent = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
    auto *filter = static_cast<MemoryFilter *>(lean_get_external_data(filterObject));
    lean_object *observer = lean_is_scalar(observerObject) ? nullptr : lean_ctor_get(observerObject, 0);
    lean_object *codeObserver = lean_is_scalar(codeObserverObject) ? nullptr : lean_ctor_get(codeObserverObject, 0);
    // The variables between ranges.
    std::vector<uint64_t> registers;
    std::vector<uint8_t> bound;
    std::vector<uint64_t> dirty;
    auto ensure = [&](uint64_t variable) {
      if (variable >= registers.size()) { registers.resize(variable + 1, 0); bound.resize(variable + 1, 0); }
    };
    // All the numbers there are, so that the registers stay where they are while a program has them.
    if (variableCount != 0) ensure(variableCount - 1);
    for (size_t index = 0; index != lean_array_size(variablesObject); ++index) {
      uint64_t variable = lean_unbox_uint64(lean_array_get_core(variablesObject, index));
      ensure(variable);
      registers[variable] = lean_unbox_uint64(lean_array_get_core(valuesObject, index));
      bound[variable] = 1;
    }
    ChainEntry *current = nullptr;
    bool first = true;
    std::vector<ChainEntry *> touched;
    {
      auto found = chain->entries.find(firstPc);
      if (found == chain->entries.end() || found->second.id != firstId || found->second.program != programObject)
        return ioError("JIT chain does not start at a range of the chain");
      current = &found->second;
    }
    const size_t firstSize = lean_array_size(stateObject);
    if (firstSize < current->slotCount)
      return ioError("JIT state has fewer slots than its program requires");
    std::vector<uint64_t> state(firstSize);
    for (size_t index = 0; index != firstSize; ++index)
      state[index] = lean_unbox_uint64(lean_array_get_core(stateObject, index));
    std::vector<uint64_t> spare;
    uint64_t budget = firstBudget;
    uint64_t chained = 0;
    StoreLog changes;
    uint64_t next = 0;
    lean_object *error = nullptr;
    // One for the whole run, whose pages stay known from one range to the next.
    BapCells memory{nullptr, 0, 0, observer, nullptr, persistent, &changes, codeObserver};
    memory.filter = filter;
    memory.quietSites = quietSites != 0;
    const uint64_t run = ++chain->run;
    // That a run left these variables written, which those with registers did there in place of their slots. What a range always
    // writes, of its outputs rather than of a checkpoint's, it has said once this run as it has written there.
    auto written = [&](ChainEntry *entry, const std::vector<ChainEntry::Output> &all, bool copy) {
      const std::vector<ChainEntry::Output> *outputs = &all;
      if (!copy && &all == &entry->outputs) {
        if (entry->outputsSaid == run) outputs = &entry->flagged;
        entry->outputsSaid = run;
      }
      for (const auto &output : *outputs) {
        if (output.flag != ChainEntry::none && state[output.flag] == 0)
          continue;
        ensure(output.variable);
        if (copy) {
          uint64_t value = state[output.slot];
          if (output.width < 64) value &= (uint64_t{1} << output.width) - 1;
          registers[output.variable] = value;
        }
        if (bound[output.variable] != 2) dirty.push_back(output.variable);
        bound[output.variable] = 2;
      }
    };
    auto outputsAt = [&](const ChainEntry *entry, uint64_t pc) -> const std::vector<ChainEntry::Output> & {
      auto checkpoint = entry->checkpoints.empty() ? entry->checkpoints.end() : entry->checkpoints.find(pc);
      return checkpoint != entry->checkpoints.end() ? checkpoint->second : entry->outputs;
    };
    for (;;) {
      auto *program = static_cast<Program *>(lean_get_external_data(current->program));
      memory.pendingSite = false;
      memory.registers = current->direct ? registers.data() : nullptr;
      next = program->function(state.data(), &memory);
      if (memory.error != nullptr) { error = memory.error; break; }
      if (current->direct)
        written(current, outputsAt(current, next), false);
      uint64_t effect = current->effectSlot == ChainEntry::none ? 0 : state[current->effectSlot];
      uint64_t left = current->budgetSlot == ChainEntry::none ? budget : state[current->budgetSlot];
      uint64_t ranChained = budget >= left ? budget - left : 0;
      // Lean counted the entry of the first already.
      uint64_t executed = (first ? 0 : 1) + ranChained;
      current->executions += executed;
      if (!current->touched) { current->touched = true; touched.push_back(current); }
      current->runs += 1;
      current->executed += executed;
      first = false;
      if (effect != 1 || memory.leanRan || current->budgetSlot == ChainEntry::none || budget - ranChained < 1)
        break;
      ChainEntry *target = current->lastNext == next ? current->lastTarget : nullptr;
      if (target == nullptr) {
        auto found = chain->entries.find(next);
        if (found == chain->entries.end())
          break;
        target = &found->second;
        current->lastNext = next;
        current->lastTarget = target;
      }
      if (target->optimizeAt != ChainEntry::none && target->executions + 1 >= target->optimizeAt)
        break;
      // What the run wrote, as Lean takes it: the outputs of the checkpoint where it went if it is one, each if its flag says so. If
      // the next can't run after all, Lean takes them again from the last run, the same.
      if (!current->direct)
        written(current, outputsAt(current, next), true);
      if (target->readyIn != run) {
        bool ready = true;
        for (uint64_t variable : target->required)
          if (variable >= bound.size() || bound[variable] == 0) { ready = false; break; }
        if (!ready)
          break;
        target->readyIn = run;
      }
      uint64_t remaining = budget - ranChained;
      chained += ranChained + 1;
      budget = remaining - 1;
      // What isn't optimized yet comes back by when it has run enough to be, as `runBlockUnprofiled` has it.
      if (target->optimizeAt != ChainEntry::none)
        budget = std::min(budget, target->optimizeAt - (target->executions + 1));
      // What isn't written before it is read, and the rest as the last range left them, which nothing reads.
      spare.resize(target->slotCount);
      for (uint64_t slot : target->zeroed) spare[slot] = 0;
      if (!target->direct)
        for (const auto &binding : target->layout)
          if (binding.first < bound.size() && bound[binding.first] != 0)
            spare[binding.second] = registers[binding.first];
      if (target->budgetSlot != ChainEntry::none) spare[target->budgetSlot] = budget;
      if (target->observedSlot != ChainEntry::none) spare[target->observedSlot] = 0;
      std::swap(state, spare);
      current = target;
    }
    if (persistent->stepActive())
      changes.forEach([&](uint64_t address, uint8_t) { persistent->noteStep(address, 1); });
    if (error != nullptr) {
      // A run that failed is taken back, and what it counted with it.
      for (ChainEntry *entry : touched) {
        entry->executions -= std::min(entry->executions, entry->executed);
        entry->touched = false;
        entry->runs = 0;
        entry->executed = 0;
      }
      return lean_io_result_mk_error(error);
    }
    if (current->budgetSlot != ChainEntry::none && budget >= state[current->budgetSlot])
      chained += budget - state[current->budgetSlot];
    const size_t stateSize = state.size();
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
    // The last range, the blocks entered after the first of all, whether the last range's variables are with the others rather than in
    // its slots, the variables written before it (and by it, if so), and the runs of each.
    std::vector<uint64_t> info{current->id, chained, current->direct ? 1u : 0u, dirty.size()};
    for (uint64_t variable : dirty) { info.push_back(variable); info.push_back(registers[variable]); }
    info.push_back(touched.size());
    for (ChainEntry *entry : touched) {
      info.push_back(entry->id);
      info.push_back(entry->runs);
      info.push_back(entry->executed);
      entry->touched = false;
      entry->runs = 0;
      entry->executed = 0;
    }
    lean_obj_res resultInfo = lean_alloc_array(info.size(), info.size());
    for (size_t at = 0; at != info.size(); ++at)
      lean_array_set_core(resultInfo, at, lean_box_uint64(info[at]));
    lean_obj_res memoryResult = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(memoryResult, 0, resultAddresses);
    lean_ctor_set(memoryResult, 1, lean_alloc_ctor(0, 2, 0));
    lean_ctor_set(lean_ctor_get(memoryResult, 1), 0, resultValues);
    lean_ctor_set(lean_ctor_get(memoryResult, 1), 1, resultInfo);
    lean_obj_res stateResult = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(stateResult, 0, resultState);
    lean_ctor_set(stateResult, 1, memoryResult);
    lean_obj_res result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_uint64_to_nat(next));
    lean_ctor_set(result, 1, stateResult);
    return lean_io_result_mk_ok(result);
  } catch (const std::exception &error) {
    return ioError(std::string("LLVM JIT chain execution failed: ") + error.what());
  }
}

extern "C" lean_obj_res bap_jit_run_memory_object_code(
    lean_obj_arg programObject, lean_obj_arg stateObject,
    lean_obj_arg memoryObject, lean_obj_arg observerObject,
    lean_obj_arg codeObserverObject, lean_obj_arg) {
  return runMemoryObject(programObject, stateObject, memoryObject, nullptr, false, observerObject, codeObserverObject);
}

extern "C" lean_obj_res bap_jit_run_memory_object_filtered_code(
    lean_obj_arg programObject, lean_obj_arg stateObject, lean_obj_arg memoryObject, lean_obj_arg filterObject,
    uint8_t quietSites, lean_obj_arg observerObject, lean_obj_arg codeObserverObject, lean_obj_arg) {
  auto *filter = static_cast<MemoryFilter *>(lean_get_external_data(filterObject));
  return runMemoryObject(programObject, stateObject, memoryObject, filter, quietSites != 0, observerObject,
                         codeObserverObject);
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

// Whether the bytes from an address are these, without making an array of them: what a trace asks of each instruction that it keeps.
extern "C" lean_obj_res bap_jit_memory_matches(lean_obj_arg memoryObject, uint64_t address, lean_obj_arg bytesObject, lean_obj_arg) {
  auto *memory = static_cast<PagedMemory *>(lean_get_external_data(memoryObject));
  size_t size = lean_sarray_size(bytesObject);
  uint8_t small[64];
  std::vector<uint8_t> large;
  uint8_t *read = small;
  if (size > sizeof small) {
    large.resize(size);
    read = large.data();
  }
  memory->readRange(address, size, read);
  return lean_io_result_mk_ok(lean_box(std::memcmp(read, lean_sarray_cptr(bytesObject), size) == 0));
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
