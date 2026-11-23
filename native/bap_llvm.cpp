#include <lean/lean.h>

#include <llvm/MC/MCAsmBackend.h>
#include <llvm/MC/MCAsmInfo.h>
#include <llvm/MC/MCCodeEmitter.h>
#include <llvm/MC/MCContext.h>
#include <llvm/MC/MCDisassembler/MCDisassembler.h>
#include <llvm/MC/MCInstPrinter.h>
#include <llvm/MC/MCInstrInfo.h>
#include <llvm/MC/MCObjectFileInfo.h>
#include <llvm/MC/MCObjectWriter.h>
#include <llvm/MC/MCParser/MCAsmParser.h>
#include <llvm/MC/MCRegisterInfo.h>
#include <llvm/MC/MCStreamer.h>
#include <llvm/MC/MCSubtargetInfo.h>
#include <llvm/MC/MCTargetOptions.h>
#include <llvm/MC/TargetRegistry.h>
#include <llvm/Object/ObjectFile.h>
#include <llvm/Support/Error.h>
#include <llvm/Support/MemoryBuffer.h>
#include <llvm/Support/MemoryBufferRef.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/Support/TargetSelect.h>
#include <llvm/TargetParser/Triple.h>
#include <llvm-c/Target.h>

#include <cstring>
#include <memory>
#include <mutex>
#include <string>
#include <unordered_map>
#include <vector>

using namespace llvm;

namespace {

void initialize() {
  static std::once_flag flag;
  std::call_once(flag, [] {
#define BAP_INITIALIZE_TARGET(name) \
    LLVMInitialize##name##TargetInfo(); \
    LLVMInitialize##name##TargetMC(); \
    LLVMInitialize##name##AsmParser(); \
    LLVMInitialize##name##Disassembler();
    BAP_INITIALIZE_TARGET(X86)
    BAP_INITIALIZE_TARGET(AArch64)
    BAP_INITIALIZE_TARGET(ARM)
    BAP_INITIALIZE_TARGET(RISCV)
    BAP_INITIALIZE_TARGET(Mips)
    BAP_INITIALIZE_TARGET(PowerPC)
    BAP_INITIALIZE_TARGET(SystemZ)
    BAP_INITIALIZE_TARGET(Sparc)
#undef BAP_INITIALIZE_TARGET
  });
}

lean_obj_res io_error(const std::string &message) {
  return lean_io_result_mk_error(
      lean_mk_io_error_other_error(0, lean_mk_string(message.c_str())));
}

lean_obj_res io_bytes(const std::vector<uint8_t> &bytes) {
  lean_object *result = lean_alloc_sarray(1, bytes.size(), bytes.size());
  if (!bytes.empty())
    std::memcpy(lean_sarray_cptr(result), bytes.data(), bytes.size());
  return lean_io_result_mk_ok(result);
}

// The features that the upstream disassemblers enable, see plugins/riscv/riscv_main.ml and
// lib/arm/arm_target.ml; without them, these encodings are invalid. The assembler keeps the
// predictable sizes of the uncompressed RISC-V encodings.
std::string targetFeatures(const Triple &triple, bool assembling) {
  if (triple.isRISCV())
    return assembling ? "+a,+d,+f,+m,+zba,+zbb,+zbs" : "+a,+c,+d,+f,+m,+zba,+zbb,+zbs";
  // Of ARM, the multiprocessing extensions too, whose PLDW is what a prefetch for a write is on a Cortex-A, and the security
  // extensions, whose SMC a user program has as an undefined instruction, which the semantics say, rather than as nothing.
  if (triple.getArch() == Triple::arm)
    return "+hwdiv,+hwdiv-arm,+vfp4,+fp-armv8,+mp,+trustzone";
  if (triple.getArch() == Triple::thumb)
    return "+thumb2,+hwdiv,+hwdiv-arm,+vfp4,+fp-armv8,+mp,+trustzone";
  if (triple.getArch() == Triple::aarch64)
    return "+v8.1a,+v8.2a,+v8.3a,+fullfp16,+aes,+sha2,+sha3,+sm4,+crc,+lse,+rdm,+dotprod,+fp16fml,"
           "+flagm,+rand,+pauth,+jsconv,+complxnum,+rcpc,+rcpc-immo,+fptoint,+sb,+predres,+ccdp,+sve,"
           "+mte,+sve2,+sme2";
  // Release 2 adds to the base CPU of the triple: SEB, SEH, ROTR, WSBH. Release 6 is the subarchitecture
  // of the triple and removes what these add to.
  if (triple.isMIPS() && triple.getSubArch() != Triple::MipsSubArch_r6)
    return triple.isMIPS64() ? "+mips64r2" : "+mips32r2";
  // The instructions of eight bytes of Power10, whose second table the decoder doesn't look at otherwise.
  if (triple.isPPC64())
    return "+prefix-instrs,+pcrelative-memops,+paired-vector-memops,+isa-v31-instructions";
  return "";
}

struct TargetContext {
  Triple triple;
  const Target *target = nullptr;
  std::unique_ptr<MCRegisterInfo> registers;
  std::unique_ptr<MCAsmInfo> asmInfo;
  std::unique_ptr<MCSubtargetInfo> subtarget;
  std::unique_ptr<MCInstrInfo> instructions;
  MCTargetOptions options;

  explicit TargetContext(const char *name, bool assembling = false, const char *more = "")
      : triple(Triple::normalize(name)) {
    std::string error;
    target = TargetRegistry::lookupTarget("", triple, error);
    if (!target)
      throw std::runtime_error(error);
    registers.reset(target->createMCRegInfo(triple));
    if (!registers)
      throw std::runtime_error("unable to create register information");
    asmInfo.reset(target->createMCAsmInfo(*registers, triple, options));
    if (!asmInfo)
      throw std::runtime_error("unable to create assembler information");
    subtarget.reset(target->createMCSubtargetInfo(triple, "", targetFeatures(triple, assembling) + more));
    if (!subtarget)
      throw std::runtime_error("unable to create subtarget information");
    instructions.reset(target->createMCInstrInfo());
    if (!instructions)
      throw std::runtime_error("unable to create instruction information");
  }
};

std::vector<uint8_t> assemble(const char *triple, const char *source) {
  TargetContext context(triple, true);
  SourceMgr sources;
  sources.AddNewSourceBuffer(
      MemoryBuffer::getMemBufferCopy(source, "<lean-assembly>"), SMLoc());
  MCContext machineContext(context.triple, *context.asmInfo,
                           *context.registers, *context.subtarget, &sources);
  auto objectInfo = context.target->createMCObjectFileInfo(machineContext,
                                                            false, false);
  machineContext.setObjectFileInfo(objectInfo);

  SmallVector<char, 256> objectBytes;
  raw_svector_ostream objectStream(objectBytes);
  auto backend = std::unique_ptr<MCAsmBackend>(
      context.target->createMCAsmBackend(*context.subtarget, *context.registers,
                                         context.options));
  auto writer = backend->createObjectWriter(objectStream);
  auto emitter = std::unique_ptr<MCCodeEmitter>(
      context.target->createMCCodeEmitter(*context.instructions, machineContext));
  auto streamer = context.target->createMCObjectStreamer(
      context.triple, machineContext, std::move(backend), std::move(writer),
      std::move(emitter), *context.subtarget);
  auto parser = createMCAsmParser(sources, machineContext, *streamer,
                                  *context.asmInfo);
  auto targetParser = context.target->createMCAsmParser(
      *context.subtarget, *parser, *context.instructions);
  if (!targetParser)
    throw std::runtime_error("target does not support assembly parsing");
  parser->setTargetParser(*targetParser);
  if (parser->Run(false) != 0)
    throw std::runtime_error("assembly failed");
  streamer->finish();

  auto object = object::ObjectFile::createObjectFile(MemoryBufferRef(
      StringRef(objectBytes.data(), objectBytes.size()), "<lean-object>"));
  if (!object)
    throw std::runtime_error(toString(object.takeError()));
  std::vector<uint8_t> result;
  for (auto section : (*object)->sections()) {
    if (!section.isText())
      continue;
    auto contents = section.getContents();
    if (!contents)
      throw std::runtime_error(toString(contents.takeError()));
    result.insert(result.end(), contents->begin(), contents->end());
  }
  return result;
}

struct Operand {
  bool isRegister;
  std::string name;
  int64_t immediate;
};

struct Disassembly {
  std::string text;
  std::string opcode;
  std::vector<Operand> operands;
  MCInst instruction;
  size_t size = 0;
  uint32_t flags = 0;
};

// Building these takes longer than decoding, so each thread keeps one set per triple.
struct DecoderContext {
  TargetContext context;
  MCContext machineContext;
  std::unique_ptr<MCDisassembler> decoder;
  std::unique_ptr<MCInstPrinter> printer;

  explicit DecoderContext(const char *triple)
      : context(triple), machineContext(context.triple, *context.asmInfo,
                                        *context.registers, *context.subtarget) {
    decoder.reset(context.target->createMCDisassembler(*context.subtarget, machineContext));
    if (!decoder)
      throw std::runtime_error("target does not support disassembly");
    unsigned dialect = context.triple.isX86() ? 1 : context.asmInfo->getAssemblerDialect();
    printer.reset(context.target->createMCInstPrinter(
        context.triple, dialect, *context.asmInfo, *context.instructions,
        *context.registers));
    if (!printer)
      throw std::runtime_error("unable to create instruction printer");
    printer->setPrintImmHex(true);
  }

  // A decoder of Thumb keeps the IT block it last decoded and predicates what it decodes next. That is right of the
  // instructions of the block, decoded in turn, but not of any other decode, which a decoder made again starts clean for.
  uint64_t itNext = 0;
  unsigned itLeft = 0;
  // The first condition and the mask of that block, and how many instructions it has.
  unsigned itFirst = 0;
  unsigned itMask = 0;
  unsigned itCount = 0;

  // The same decoder with the instructions of ARMv8, which `definedSoftFail` asks.
  struct Later {
    TargetContext context;
    MCContext machineContext;
    explicit Later(const char *triple)
        : context(triple, false, ",+v8"),
          machineContext(context.triple, *context.asmInfo, *context.registers, *context.subtarget) {}
  };
  std::unique_ptr<Later> later;

  // Whether an instruction of ARM or Thumb that the decoder has as SoftFail, decoded but UNPREDICTABLE or deprecated by what
  // LLVM knows, is one whose behaviour the architecture defines, and so one to run. Any other stays what didn't decode:
  // - what ARMv8-A defines and ARMv7 had as UNPREDICTABLE, the stack pointer as an operand of T32 (`sub.w r10, r8, sp`,
  //   `ldr.w r0, [r1, sp]`) or as the shifted register of A32: what a decoder of ARMv8 has as the same instruction with nothing
  //   to say against it, in the same place of an IT block;
  // - the pc as the register that an instruction of A32 shifts by an immediate (`and r10, r4, pc, lsr #2`), which reads as the
  //   instruction's address plus 8, and is deprecated rather than UNPREDICTABLE, as it is where the register is shifted by a
  //   register: the instruction with another register there is one that the decoder has nothing to say against.
  bool definedSoftFail(const MCInst &instruction, const uint8_t *bytes, size_t size, uint64_t address) {
    Triple::ArchType arch = context.triple.getArch();
    if (arch != Triple::arm && arch != Triple::thumb)
      return false;
    unsigned opcode = instruction.getOpcode();
    ArrayRef<uint8_t> input(bytes, size);
    if (!later)
      later = std::make_unique<Later>(context.triple.str().c_str());
    std::unique_ptr<MCDisassembler> other(
        context.target->createMCDisassembler(*later->context.subtarget, later->machineContext));
    if (other) {
      MCInst again;
      uint64_t length = 0;
      if (itLeft > 0) {
        // An IT of the condition that this instruction has in its block, and of whether it is the last of it.
        unsigned index = itCount - itLeft;
        unsigned condition = index == 0 ? itFirst : (itFirst & 14) | ((itMask >> (4 - index)) & 1);
        unsigned mask = itLeft == 1 ? 8 : ((condition & 1) << 3) | 4;
        uint8_t it[2] = {static_cast<uint8_t>(condition << 4 | mask), 0xbf};
        other->getInstruction(again, length, ArrayRef<uint8_t>(it, 2), address - 2, nulls());
        again = MCInst();
      }
      if (other->getInstruction(again, length, input, address, nulls()) == MCDisassembler::Success &&
          again.getOpcode() == opcode)
        return true;
    }
    if (arch == Triple::arm && size >= 4 && (bytes[0] & 15) == 15) {
      static const char *const shifted[] = {"ANDrsi", "EORrsi", "SUBrsi", "RSBrsi", "ADDrsi", "ADCrsi", "SBCrsi", "RSCrsi",
                                            "ORRrsi", "BICrsi", "TSTrsi", "TEQrsi", "CMPrsi", "CMNzrsi", "MOVsi",  "MVNsi"};
      StringRef name = context.instructions->getName(opcode);
      bool listed = false;
      for (const char *each : shifted)
        listed = listed || name == each;
      if (!listed)
        return false;
      uint8_t changed[4] = {static_cast<uint8_t>(bytes[0] & 0xf0), bytes[1], bytes[2], bytes[3]};
      MCInst again;
      uint64_t length = 0;
      return decoder->getInstruction(again, length, ArrayRef<uint8_t>(changed, 4), address, nulls()) ==
                 MCDisassembler::Success &&
             again.getOpcode() == opcode;
    }
    return false;
  }

  void beforeDecode(uint64_t address) {
    if (itLeft == 0 || address == itNext)
      return;
    decoder.reset(context.target->createMCDisassembler(*context.subtarget, machineContext));
    itLeft = 0;
  }

  void failedDecode() {
    if (!context.triple.isThumb())
      return;
    decoder.reset(context.target->createMCDisassembler(*context.subtarget, machineContext));
    itLeft = 0;
  }

  void afterDecode(uint64_t address, const MCInst &instruction, size_t size, const uint8_t *bytes) {
    if (!context.triple.isThumb())
      return;
    if (context.instructions->getName(instruction.getOpcode()) == "t2IT" && size >= 2) {
      // The mask's lowest bit that is set ends the block: as many instructions as there are bits above it.
      unsigned mask = bytes[0] & 15;
      itLeft = mask == 0 ? 0 : 4 - __builtin_ctz(mask);
      itFirst = bytes[0] >> 4;
      itMask = mask;
      itCount = itLeft;
    } else if (itLeft > 0) {
      itLeft -= 1;
    }
    itNext = address + size;
  }
};

DecoderContext &decoderContext(const char *triple) {
  thread_local std::unordered_map<std::string, std::unique_ptr<DecoderContext>> contexts;
  auto &entry = contexts[triple];
  if (!entry)
    entry = std::make_unique<DecoderContext>(triple);
  return *entry;
}

const std::unordered_map<std::string, unsigned> &opcodeTable(const char *triple) {
  thread_local std::unordered_map<std::string, std::unordered_map<std::string, unsigned>> tables;
  auto [entry, fresh] = tables.try_emplace(triple);
  if (fresh) {
    TargetContext context(triple);
    for (unsigned opcode = 0; opcode != context.instructions->getNumOpcodes(); ++opcode)
      entry->second.emplace(context.instructions->getName(opcode).str(), opcode);
  }
  return entry->second;
}

Disassembly disassemble(const char *triple, const uint8_t *bytes, size_t size,
                        uint64_t address) {
  DecoderContext &cached = decoderContext(triple);
  TargetContext &context = cached.context;
  cached.beforeDecode(address);
  auto &decoder = cached.decoder;
  auto &printer = cached.printer;

  Disassembly result;
  uint64_t decodedSize = 0;
  ArrayRef<uint8_t> input(bytes, size);
  auto status = decoder->getInstruction(result.instruction, decodedSize, input, address,
                                        nulls());
  if (status != MCDisassembler::Success &&
      !(status == MCDisassembler::SoftFail && cached.definedSoftFail(result.instruction, bytes, size, address))) {
    // What didn't decode may have left the decoder of Thumb in a block all the same, as an IT that it refuses does.
    cached.failedDecode();
    throw std::runtime_error("instruction decoding failed");
  }
  cached.afterDecode(address, result.instruction, decodedSize, bytes);
  raw_string_ostream output(result.text);
  printer->printInst(&result.instruction, address, "", *context.subtarget, output);
  result.size = decodedSize;
  result.opcode = context.instructions->getName(result.instruction.getOpcode()).str();
  for (const auto &operand : result.instruction) {
    if (operand.isReg()) {
      const char *name = context.registers->getName(operand.getReg());
      result.operands.push_back({true, name && *name ? name : "Nil", 0});
    } else if (operand.isImm()) {
      result.operands.push_back({false, "", operand.getImm()});
    } else {
      throw std::runtime_error("unsupported LLVM operand kind");
    }
  }
  const auto &description = context.instructions->get(result.instruction.getOpcode());
  result.flags |= description.isReturn() ? 1 : 0;
  result.flags |= description.isCall() ? 2 : 0;
  result.flags |= description.isBarrier() ? 4 : 0;
  result.flags |= description.isBranch() ? 8 : 0;
  result.flags |= description.isIndirectBranch() ? 16 : 0;
  result.flags |= description.isConditionalBranch() ? 32 : 0;
  result.flags |= description.isUnconditionalBranch() ? 64 : 0;
  result.flags |= description.mayLoad() ? 128 : 0;
  result.flags |= description.mayStore() ? 256 : 0;
  result.flags |= description.isTerminator() ? 512 : 0;
  return result;
}

void finalizeInstruction(void *data) { delete static_cast<MCInst *>(data); }
void foreachInstruction(void *, b_lean_obj_arg) {}

lean_external_class *instructionClass() {
  static lean_external_class *cls =
      lean_register_external_class(finalizeInstruction, foreachInstruction);
  return cls;
}

} // namespace

extern "C" lean_obj_res bap_llvm_assemble(lean_obj_arg triple,
                                            lean_obj_arg source,
                                            lean_obj_arg) {
  initialize();
  try {
    return io_bytes(assemble(lean_string_cstr(triple), lean_string_cstr(source)));
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_disassemble(lean_obj_arg triple,
                                               lean_obj_arg data,
                                               uint64_t address,
                                               lean_obj_arg) {
  initialize();
  try {
    auto result = disassemble(lean_string_cstr(triple),
                              reinterpret_cast<const uint8_t *>(lean_sarray_cptr(data)),
                              lean_sarray_size(data), address);
    lean_object *operands = lean_box(0);
    for (auto iterator = result.operands.rbegin(); iterator != result.operands.rend(); ++iterator) {
      lean_object *operand = nullptr;
      if (iterator->isRegister) {
        operand = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(operand, 0, lean_mk_string(iterator->name.c_str()));
      } else {
        operand = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(operand, 0, lean_int64_to_int(iterator->immediate));
      }
      lean_object *tail = operands;
      operands = lean_alloc_ctor(1, 2, 0);
      lean_ctor_set(operands, 0, operand);
      lean_ctor_set(operands, 1, tail);
    }
    lean_object *opcodeAndOperands = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(opcodeAndOperands, 0, lean_mk_string(result.opcode.c_str()));
    lean_ctor_set(opcodeAndOperands, 1, operands);
    lean_object *metadata = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(metadata, 0, lean_box(result.flags));
    lean_ctor_set(metadata, 1, opcodeAndOperands);
    lean_object *sizeAndMetadata = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(sizeAndMetadata, 0, lean_box(result.size));
    lean_ctor_set(sizeAndMetadata, 1, metadata);
    lean_object *decoded = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(decoded, 0, lean_mk_string(result.text.c_str()));
    lean_ctor_set(decoded, 1, sizeAndMetadata);
    return lean_io_result_mk_ok(decoded);
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_disassemble_mc(lean_obj_arg triple,
                                                  lean_obj_arg data,
                                                  uint64_t address,
                                                  lean_obj_arg) {
  initialize();
  try {
    auto result = disassemble(lean_string_cstr(triple),
                              reinterpret_cast<const uint8_t *>(lean_sarray_cptr(data)),
                              lean_sarray_size(data), address);
    lean_object *instruction = lean_alloc_external(
        instructionClass(), new MCInst(std::move(result.instruction)));
    lean_object *flagsAndInstruction = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(flagsAndInstruction, 0, lean_box(result.flags));
    lean_ctor_set(flagsAndInstruction, 1, instruction);
    lean_object *sizeAndMetadata = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(sizeAndMetadata, 0, lean_box(result.size));
    lean_ctor_set(sizeAndMetadata, 1, flagsAndInstruction);
    lean_object *decoded = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(decoded, 0, lean_mk_string(result.text.c_str()));
    lean_ctor_set(decoded, 1, sizeAndMetadata);
    return lean_io_result_mk_ok(decoded);
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_mc_opcode(lean_obj_arg instruction) {
  auto *mc = static_cast<MCInst *>(lean_get_external_data(instruction));
  return lean_uint64_to_nat(mc->getOpcode());
}

extern "C" lean_obj_res bap_llvm_mc_operands(lean_obj_arg instruction,
                                               lean_obj_arg) {
  auto *mc = static_cast<MCInst *>(lean_get_external_data(instruction));
  for (const auto &operand : *mc)
    if (!operand.isReg() && !operand.isImm())
      return io_error("unsupported LLVM operand kind");
  std::vector<lean_object *> values;
  for (const auto &operand : *mc) {
    lean_object *value = nullptr;
    if (operand.isReg()) {
      value = lean_alloc_ctor(0, 1, 0);
      lean_ctor_set(value, 0, lean_uint64_to_nat(operand.getReg()));
    } else {
      value = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(value, 0, lean_int64_to_int(operand.getImm()));
    }
    values.push_back(value);
  }
  lean_object *operands = lean_box(0);
  for (auto iterator = values.rbegin(); iterator != values.rend(); ++iterator) {
    lean_object *tail = operands;
    operands = lean_alloc_ctor(1, 2, 0);
    lean_ctor_set(operands, 0, *iterator);
    lean_ctor_set(operands, 1, tail);
  }
  return lean_io_result_mk_ok(operands);
}

extern "C" lean_obj_res bap_llvm_opcode_id(lean_obj_arg triple, lean_obj_arg name,
                                             lean_obj_arg) {
  initialize();
  try {
    const auto &table = opcodeTable(lean_string_cstr(triple));
    auto found = table.find(lean_string_cstr(name));
    if (found != table.end())
      return lean_io_result_mk_ok(lean_uint64_to_nat(found->second));
    return io_error("unknown LLVM opcode");
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_opcode_id_opt(lean_obj_arg triple, lean_obj_arg name,
                                                 lean_obj_arg) {
  initialize();
  try {
    const auto &table = opcodeTable(lean_string_cstr(triple));
    auto found = table.find(lean_string_cstr(name));
    if (found != table.end()) {
      lean_object *result = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(result, 0, lean_uint64_to_nat(found->second));
      return lean_io_result_mk_ok(result);
    }
    return lean_io_result_mk_ok(lean_box(0));
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_register_id(lean_obj_arg triple, lean_obj_arg name,
                                               lean_obj_arg) {
  initialize();
  try {
    TargetContext context(lean_string_cstr(triple));
    const char *expected = lean_string_cstr(name);
    for (unsigned reg = 0; reg != context.registers->getNumRegs(); ++reg)
      if (StringRef(context.registers->getName(reg)) == expected)
        return lean_io_result_mk_ok(lean_uint64_to_nat(reg));
    return io_error(std::string("unknown LLVM register: ") + expected);
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_register_names(lean_obj_arg triple, lean_obj_arg) {
  initialize();
  try {
    TargetContext context(lean_string_cstr(triple));
    lean_object *registers = lean_box(0);
    for (unsigned reg = context.registers->getNumRegs(); reg-- > 0;) {
      const char *name = context.registers->getName(reg);
      if (!name || !*name)
        continue;
      lean_object *entry = lean_alloc_ctor(0, 2, 0);
      lean_ctor_set(entry, 0, lean_uint64_to_nat(reg));
      lean_ctor_set(entry, 1, lean_mk_string(name));
      lean_object *tail = registers;
      registers = lean_alloc_ctor(1, 2, 0);
      lean_ctor_set(registers, 0, entry);
      lean_ctor_set(registers, 1, tail);
    }
    return lean_io_result_mk_ok(registers);
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}
