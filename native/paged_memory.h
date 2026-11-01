#pragma once

// A guest address space: real pages of the host, found through a table that nothing locks. A page, once there, stays until the
// memory goes, so that a pointer to one stays good and whoever reads the table needs no more than to see it whole. All 64 bits of an
// address are kept, which a mapping of the address space itself couldn't do, as the host has fewer, and each process has its own.
//
// An access within one word of 8 bytes is atomic, with acquire and release, whatever its size and alignment, as a word is what is
// loaded or exchanged for it. Across words, each is atomic and the whole isn't, which is what most machines do too.
//
// This is on its own for `paged_memory_stress.cpp`, which runs it under ThreadSanitizer.

#include <atomic>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <algorithm>
#include <mutex>
#include <new>
#include <utility>
#include <vector>

#if defined(_WIN32)
#include <malloc.h>
#else
#include <sys/mman.h>
#endif

class PagedMemory {
public:
  static constexpr size_t pageBits = 12;
  static constexpr size_t pageSize = size_t{1} << pageBits;

private:
  static constexpr size_t wordSize = sizeof(uint64_t);
  static constexpr size_t levelBits = 13;
  static constexpr size_t levels = 4;
  static constexpr size_t fanout = size_t{1} << levelBits;
  static constexpr size_t chunkPages = 256;
  static_assert(pageBits + levels * levelBits == 64, "the table has to hold every address");

  struct Node {
    std::atomic<void *> entries[fanout];
    Node() {
      for (auto &entry : entries)
        entry.store(nullptr, std::memory_order_relaxed);
    }
  };

  Node root;
  // Pages come out of chunks, as a call to the system for each would cost more than the page, and go when the memory goes.
  std::mutex chunkLock;
  std::vector<uint8_t *> chunks;
  std::vector<uint8_t *> unused;
  size_t chunkUsed = chunkPages;
  // What has been written since a step began, to take it back if the step fails.
  static constexpr size_t stepLimit = size_t{1} << 22;
  std::atomic<bool> stepOpen{false};
  std::mutex stepLock;
  std::vector<std::pair<uint64_t, uint8_t>> stepWrites;
  bool stepOverflowed = false;

  static size_t indexAt(uint64_t address, size_t level) {
    return (address >> (pageBits + (levels - 1 - level) * levelBits)) & (fanout - 1);
  }

  static uint8_t *newChunk() {
#if defined(_WIN32)
    auto *chunk = static_cast<uint8_t *>(_aligned_malloc(chunkPages * pageSize, pageSize));
    if (chunk == nullptr)
      throw std::bad_alloc();
    std::memset(chunk, 0, chunkPages * pageSize);
    return chunk;
#else
    void *chunk = mmap(nullptr, chunkPages * pageSize, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (chunk == MAP_FAILED)
      throw std::bad_alloc();
    return static_cast<uint8_t *>(chunk);
#endif
  }

  static void freeChunk(uint8_t *chunk) {
#if defined(_WIN32)
    _aligned_free(chunk);
#else
    munmap(chunk, chunkPages * pageSize);
#endif
  }

  uint8_t *newPage() {
    std::lock_guard<std::mutex> lock(chunkLock);
    if (!unused.empty()) {
      uint8_t *page = unused.back();
      unused.pop_back();
      return page;
    }
    if (chunkUsed == chunkPages) {
      chunks.push_back(newChunk());
      chunkUsed = 0;
    }
    return chunks.back() + pageSize * chunkUsed++;
  }

  // A page that lost a race has never been seen by anyone, and is still all zeros.
  void unusedPage(uint8_t *page) {
    std::lock_guard<std::mutex> lock(chunkLock);
    unused.push_back(page);
  }

  static void clear(Node *node, size_t level) {
    if (level + 1 == levels)
      return;
    for (auto &entry : node->entries) {
      void *child = entry.load(std::memory_order_relaxed);
      if (child != nullptr) {
        clear(static_cast<Node *>(child), level + 1);
        delete static_cast<Node *>(child);
      }
    }
  }

  template <typename F>
  static void visit(const Node *node, size_t level, uint64_t prefix, F &action) {
    for (size_t index = 0; index != fanout; ++index) {
      void *child = node->entries[index].load(std::memory_order_acquire);
      if (child == nullptr)
        continue;
      uint64_t next = prefix | (static_cast<uint64_t>(index) << (pageBits + (levels - 1 - level) * levelBits));
      if (level + 1 == levels)
        action(next, static_cast<uint8_t *>(child));
      else
        visit(static_cast<const Node *>(child), level + 1, next, action);
    }
  }

  static uint64_t *wordAt(uint8_t *page, uint64_t address) {
    return reinterpret_cast<uint64_t *>(page + (address & (pageSize - wordSize)));
  }

  // What is in the word of `address`, as bytes in memory order: of the place, if the page isn't there, is zeros.
  void loadWord(uint64_t address, uint8_t *bytes) const {
    const uint8_t *page = find(address);
    uint64_t word = page == nullptr ? 0 : __atomic_load_n(wordAt(const_cast<uint8_t *>(page), address), __ATOMIC_ACQUIRE);
    std::memcpy(bytes, &word, wordSize);
  }

  // `size` bytes into the word of `address`, all at once, with the other bytes of the word as they are.
  void storeInWord(uint64_t address, size_t size, const uint8_t *bytes) {
    bool zero = true;
    for (size_t index = 0; index != size; ++index)
      zero = zero && bytes[index] == 0;
    // What was never written is 0 already, and doesn't need a page to say so.
    uint8_t *page = zero ? find(address) : ensure(address);
    if (page == nullptr)
      return;
    uint64_t *word = wordAt(page, address);
    size_t offset = address & (wordSize - 1);
    if (size == wordSize) {
      uint64_t value;
      std::memcpy(&value, bytes, wordSize);
      __atomic_store_n(word, value, __ATOMIC_RELEASE);
      return;
    }
    uint64_t expected = __atomic_load_n(word, __ATOMIC_RELAXED);
    uint64_t desired;
    do {
      desired = expected;
      std::memcpy(reinterpret_cast<uint8_t *>(&desired) + offset, bytes, size);
    } while (!__atomic_compare_exchange_n(word, &expected, desired, true, __ATOMIC_RELEASE, __ATOMIC_RELAXED));
  }

public:
  PagedMemory() = default;
  PagedMemory(const PagedMemory &) = delete;
  PagedMemory &operator=(const PagedMemory &) = delete;
  ~PagedMemory() {
    clear(&root, 0);
    for (uint8_t *chunk : chunks)
      freeChunk(chunk);
  }

  // The page of an address, if anything was ever written to it.
  uint8_t *find(uint64_t address) const {
    const Node *node = &root;
    for (size_t level = 0; level + 1 != levels; ++level) {
      node = static_cast<const Node *>(node->entries[indexAt(address, level)].load(std::memory_order_acquire));
      if (node == nullptr)
        return nullptr;
    }
    return static_cast<uint8_t *>(node->entries[indexAt(address, levels - 1)].load(std::memory_order_acquire));
  }

  // The page of an address, made if it isn't there. Of two threads that make one, the one that comes second uses that of the first.
  uint8_t *ensure(uint64_t address) {
    Node *node = &root;
    for (size_t level = 0; level + 1 != levels; ++level) {
      auto &entry = node->entries[indexAt(address, level)];
      void *child = entry.load(std::memory_order_acquire);
      if (child == nullptr) {
        auto *made = new Node;
        if (entry.compare_exchange_strong(child, made, std::memory_order_acq_rel, std::memory_order_acquire))
          child = made;
        else
          delete made;
      }
      node = static_cast<Node *>(child);
    }
    auto &entry = node->entries[indexAt(address, levels - 1)];
    void *page = entry.load(std::memory_order_acquire);
    if (page == nullptr) {
      uint8_t *made = newPage();
      if (entry.compare_exchange_strong(page, made, std::memory_order_acq_rel, std::memory_order_acquire))
        page = made;
      else
        unusedPage(made);
    }
    return static_cast<uint8_t *>(page);
  }

  // `size` bytes, a word at a time. Addresses go on in 64 bits, and don't wrap in a way that anything relies on.
  void load(uint64_t address, size_t size, uint8_t *bytes) const {
    size_t done = 0;
    while (done != size) {
      uint64_t at = address + done;
      size_t offset = at & (wordSize - 1);
      size_t count = wordSize - offset < size - done ? wordSize - offset : size - done;
      uint8_t word[wordSize];
      loadWord(at, word);
      std::memcpy(bytes + done, word + offset, count);
      done += count;
    }
  }

  void store(uint64_t address, size_t size, const uint8_t *bytes) {
    size_t done = 0;
    while (done != size) {
      uint64_t at = address + done;
      size_t offset = at & (wordSize - 1);
      size_t count = wordSize - offset < size - done ? wordSize - offset : size - done;
      storeInWord(at, count, bytes + done);
      done += count;
    }
  }

  uint8_t read(uint64_t address) const {
    uint8_t value;
    load(address, 1, &value);
    return value;
  }

  void readRange(uint64_t address, size_t size, uint8_t *bytes) const { load(address, size, bytes); }

  // Pairs in order, with those that go on from each other written together, so that what is written as a whole word is seen as one.
  void writeAll(const uint64_t *addresses, const uint8_t *values, size_t count) {
    size_t index = 0;
    while (index != count) {
      uint64_t at = addresses[index];
      size_t room = wordSize - (at & (wordSize - 1));
      size_t run = 1;
      while (run != room && index + run != count && addresses[index + run] == at + run)
        ++run;
      storeInWord(at, run, values + index);
      noteStep(at, run);
      index += run;
    }
  }

  // A step begins: from here on what is written is remembered, by where it is and not what it was, as who takes it back has the bytes.
  void beginStep() {
    std::lock_guard<std::mutex> lock(stepLock);
    stepWrites.clear();
    stepOverflowed = false;
    stepOpen.store(true, std::memory_order_release);
  }

  void endStep() {
    std::lock_guard<std::mutex> lock(stepLock);
    stepOpen.store(false, std::memory_order_release);
    stepWrites.clear();
    stepOverflowed = false;
  }

  bool stepActive() const { return stepOpen.load(std::memory_order_acquire); }

  void noteStep(uint64_t address, size_t size) {
    if (!stepActive())
      return;
    std::lock_guard<std::mutex> lock(stepLock);
    if (stepOverflowed)
      return;
    if (stepWrites.size() >= stepLimit) {
      stepOverflowed = true;
      stepWrites.clear();
      return;
    }
    stepWrites.emplace_back(address, static_cast<uint8_t>(size));
  }

  // Each address written since the step began, once, in order; or nothing when there were too many to remember or no step began.
  bool stepAddresses(std::vector<uint64_t> &addresses) {
    std::lock_guard<std::mutex> lock(stepLock);
    if (stepOverflowed || !stepOpen.load(std::memory_order_acquire))
      return false;
    for (const auto &write : stepWrites)
      for (size_t index = 0; index != write.second; ++index)
        addresses.push_back(write.first + index);
    std::sort(addresses.begin(), addresses.end());
    addresses.erase(std::unique(addresses.begin(), addresses.end()), addresses.end());
    return true;
  }

  // Bytes in bulk into a memory that nothing else can see yet, later over earlier, which is why it needs nothing to be atomic and takes
  // no longer than a copy. What is all zeros makes no page. It doesn't go past the end of the address space.
  void fill(uint64_t address, const uint8_t *bytes, size_t size) {
    size_t done = 0;
    while (done != size) {
      uint64_t at = address + done;
      if (at < address)
        return;
      size_t offset = at & (pageSize - 1);
      size_t count = pageSize - offset < size - done ? pageSize - offset : size - done;
      const uint8_t *from = bytes + done;
      bool zero = from[0] == 0 && std::memcmp(from, from + 1, count - 1) == 0;
      uint8_t *page = zero ? find(at) : ensure(at);
      if (page != nullptr)
        std::memcpy(page + offset, from, count);
      done += count;
    }
  }

  // Zeros from `first` to `last`, as a step can know of, in as long as the pages that there are between them. That is what unmapping comes
  // to, which shouldn't take as long as all that the process holds.
  void zeroRange(uint64_t first, uint64_t last) {
    if (last < first)
      return;
    const uint8_t zeros[wordSize] = {0};
    auto zeroInPage = [&](uint64_t base, uint8_t *page) {
      uint64_t lower = first > base ? first : base;
      uint64_t upper = last < base + (pageSize - 1) ? last : base + (pageSize - 1);
      if (last < base || first > base + (pageSize - 1))
        return;
      uint64_t at = lower;
      while (true) {
        uint64_t wordEnd = at | (wordSize - 1);
        uint64_t end = wordEnd < upper ? wordEnd : upper;
        size_t count = static_cast<size_t>(end - at) + 1;
        // Only what this range has of the word: the rest of it is someone else's.
        uint64_t word = __atomic_load_n(wordAt(page, at), __ATOMIC_ACQUIRE);
        uint8_t bytes[wordSize];
        std::memcpy(bytes, &word, wordSize);
        if (std::memcmp(bytes + (at & (wordSize - 1)), zeros, count) != 0) {
          storeInWord(at, count, zeros);
          noteStep(at, count);
        }
        if (end == upper)
          break;
        at = end + 1;
      }
    };
    // By the page when that is fewer than all that there are, as a range can be most of the address space.
    if ((last >> pageBits) - (first >> pageBits) < (size_t{1} << 16)) {
      uint64_t base = first & ~static_cast<uint64_t>(pageSize - 1);
      while (true) {
        if (uint8_t *page = find(base))
          zeroInPage(base, page);
        if (base >= (last & ~static_cast<uint64_t>(pageSize - 1)))
          break;
        base += pageSize;
      }
    } else {
      forEachPage(zeroInPage);
    }
  }

  // Each page there is, by ascending address.
  template <typename F> void forEachPage(F &&action) const { visit(&root, 0, 0, action); }

  void copyFrom(const PagedMemory &other) {
    other.forEachPage([&](uint64_t address, const uint8_t *from) {
      uint8_t *to = ensure(address);
      for (size_t offset = 0; offset != pageSize; offset += wordSize) {
        uint64_t value = __atomic_load_n(reinterpret_cast<const uint64_t *>(from + offset), __ATOMIC_ACQUIRE);
        __atomic_store_n(reinterpret_cast<uint64_t *>(to + offset), value, __ATOMIC_RELEASE);
      }
    });
  }

  // Gives the system back what holds only zeros of the pages wholly in this range, where it can. A page stays where it is and reads the
  // same, so that this is for the memory of a host and changes nothing that can be seen. Nothing should be storing there: it is for
  // what has just been unmapped, which a store is refused at.
  void trim(uint64_t first, uint64_t last) {
#if defined(__linux__)
    if (last < first)
      return;
    uint64_t start = (first + pageSize - 1) & ~static_cast<uint64_t>(pageSize - 1);
    if (start < first)
      return;
    forEachPage([&](uint64_t address, uint8_t *page) {
      if (address < start || address + (pageSize - 1) > last || address + (pageSize - 1) < address)
        return;
      for (size_t offset = 0; offset != pageSize; offset += wordSize)
        if (__atomic_load_n(reinterpret_cast<const uint64_t *>(page + offset), __ATOMIC_ACQUIRE) != 0)
          return;
      madvise(page, pageSize, MADV_DONTNEED);
    });
#else
    (void)first;
    (void)last;
#endif
  }
};
