// What `PagedMemory` promises when threads race on it, on its own, to run under ThreadSanitizer. It takes no part in a build:
//   clang++ -std=c++17 -O1 -g -fsanitize=thread -fuse-ld=lld -pthread native/paged_memory_stress.cpp -o /tmp/stress && /tmp/stress

#include "paged_memory.h"

#include <cstdio>
#include <thread>
#include <vector>

#if defined(__linux__)
#include <unistd.h>
#endif

static int failures = 0;

static void check(bool condition, const char *what) {
  if (!condition) {
    std::fprintf(stderr, "FAILED: %s\n", what);
    ++failures;
  }
}

template <typename F> static void together(size_t threads, F action) {
  std::vector<std::thread> running;
  for (size_t index = 0; index != threads; ++index)
    running.emplace_back(action, index);
  for (auto &thread : running)
    thread.join();
}

static uint64_t word(const PagedMemory &memory, uint64_t address) {
  uint64_t value;
  memory.load(address, 8, reinterpret_cast<uint8_t *>(&value));
  return value;
}

int main() {
  // Threads that make the same pages and tables at once find the same ones, and nothing is lost.
  {
    PagedMemory memory;
    constexpr size_t threads = 8, pages = 1000;
    together(threads, [&](size_t thread) {
      for (size_t page = 0; page != pages; ++page) {
        uint8_t value = static_cast<uint8_t>(thread + 1);
        // Far apart, to make tables as well as pages, and the same for all, each with a byte of its own.
        memory.store((static_cast<uint64_t>(page) << 30) + thread, 1, &value);
      }
    });
    for (size_t page = 0; page != pages; ++page)
      for (size_t thread = 0; thread != threads; ++thread)
        check(memory.read((static_cast<uint64_t>(page) << 30) + thread) == thread + 1, "a byte of a shared new page");
  }
  // What is written whole is read whole: within a word at any alignment, of any size, whichever way it was written.
  for (size_t offset = 0; offset != 8; ++offset)
    for (size_t size = 1; size + offset <= 8; ++size) {
      PagedMemory memory;
      const uint64_t base = 0x5000 + offset;
      std::atomic<bool> stop{false};
      std::atomic<int> torn{0};
      std::thread writer([&] {
        uint8_t ones[8], zeros[8] = {0};
        std::memset(ones, 0xFF, 8);
        for (int round = 0; round != 5000; ++round) {
          memory.store(base, size, ones);
          memory.store(base, size, zeros);
        }
        stop = true;
      });
      std::thread neighbour([&] {
        // Stores to the rest of the word don't undo those of the writer, nor it theirs.
        uint8_t other = 0x5A;
        while (!stop)
          if (offset != 0)
            memory.store(0x5000, 1, &other);
      });
      std::thread reader([&] {
        while (!stop) {
          uint8_t bytes[8];
          memory.load(base, size, bytes);
          for (size_t index = 1; index != size; ++index)
            if (bytes[index] != bytes[0])
              ++torn;
        }
      });
      writer.join();
      neighbour.join();
      reader.join();
      check(torn == 0, "an access within a word is seen whole");
      if (offset != 0)
        check(memory.read(0x5000) == 0x5A || memory.read(0x5000) == 0, "the rest of a word is its own");
    }
  // A word written byte by byte through `writeAll` is one store.
  {
    PagedMemory memory;
    std::atomic<bool> stop{false};
    std::atomic<int> torn{0};
    std::thread writer([&] {
      uint64_t addresses[8];
      for (size_t index = 0; index != 8; ++index)
        addresses[index] = 0x7000 + index;
      uint8_t ones[8], zeros[8] = {0};
      std::memset(ones, 0xFF, 8);
      for (int round = 0; round != 40000; ++round) {
        memory.writeAll(addresses, ones, 8);
        memory.writeAll(addresses, zeros, 8);
      }
      stop = true;
    });
    std::thread reader([&] {
      while (!stop) {
        uint64_t value = word(memory, 0x7000);
        if (value != 0 && value != ~uint64_t{0})
          ++torn;
      }
    });
    writer.join();
    reader.join();
    check(torn == 0, "writeAll of a word is seen whole");
  }
  // A release that another thread acquires brings what came before it.
  {
    PagedMemory memory;
    std::atomic<int> missed{0};
    std::thread reader([&] {
      for (uint64_t round = 1; round != 20000; ++round) {
        // The writer may be past it by now, which is why this is at least.
        while (word(memory, 0x9000) < round) {
        }
        if (word(memory, 0xA000) < round)
          ++missed;
      }
    });
    for (uint64_t round = 1; round != 20000; ++round) {
      memory.store(0xA000, 8, reinterpret_cast<const uint8_t *>(&round));
      memory.store(0x9000, 8, reinterpret_cast<const uint8_t *>(&round));
    }
    reader.join();
    check(missed == 0, "release and acquire order what is between them");
  }
  // A copy is its own, while what it came from goes on, and a page that nobody wrote isn't made by reading it.
  {
    PagedMemory memory;
    uint8_t value = 3;
    memory.store(0x1000, 1, &value);
    check(memory.read(0xFFFFFFFFFFFFF000) == 0 && memory.find(0xFFFFFFFFFFFFF000) == nullptr, "a read makes no page");
    PagedMemory copy;
    copy.copyFrom(memory);
    uint8_t other = 4;
    copy.store(0x1000, 1, &other);
    check(memory.read(0x1000) == 3 && copy.read(0x1000) == 4, "a copy is its own");
  }
  // At the very top, nothing goes wrong with what wraps.
  {
    PagedMemory memory;
    uint64_t value = 0x1122334455667788;
    memory.store(0xFFFFFFFFFFFFFFF8, 8, reinterpret_cast<const uint8_t *>(&value));
    check(word(memory, 0xFFFFFFFFFFFFFFF8) == value, "the last word of the address space");
    memory.trim(0xFFFFFFFFFFFFF000, 0xFFFFFFFFFFFFFFFF);
    check(word(memory, 0xFFFFFFFFFFFFFFF8) == value, "trim leaves what isn't zero");
  }
#if defined(__linux__)
  // What is trimmed reads as it did, and is no longer held; what isn't all zeros is left alone.
  {
    PagedMemory memory;
    uint8_t filled[4096];
    std::memset(filled, 0xAB, sizeof filled);
    memory.store(0x20000, sizeof filled, filled);
    memory.store(0x21000, sizeof filled, filled);
    std::memset(filled, 0, sizeof filled);
    memory.store(0x20000, sizeof filled, filled);
    auto held = [&](uint64_t address) {
      unsigned char state = 0;
      long size = sysconf(_SC_PAGESIZE);
      check(size == 4096, "this check is for pages of 4 KB");
      mincore(memory.find(address), 4096, &state);
      return (state & 1) != 0;
    };
    check(held(0x20000) && held(0x21000), "written pages are held");
    memory.trim(0x20000, 0x21FFF);
    check(!held(0x20000), "a page of zeros goes back");
    check(held(0x21000) && memory.read(0x21000) == 0xAB, "a page with something in it stays");
    check(memory.read(0x20000) == 0, "a trimmed page reads as it did");
    uint8_t value = 9;
    memory.store(0x20000, 1, &value);
    check(memory.read(0x20000) == 9, "a trimmed page can be written");
  }
#endif
  std::fprintf(stderr, failures == 0 ? "paged memory: all passed\n" : "paged memory: %d failed\n", failures);
  return failures == 0 ? 0 : 1;
}
