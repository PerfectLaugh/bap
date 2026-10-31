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
  if (triple.getArch() == Triple::arm)
    return "+hwdiv,+hwdiv-arm,+vfp4";
  if (triple.getArch() == Triple::thumb)
    return "+thumb2,+hwdiv,+hwdiv-arm,+vfp4";
  if (triple.getArch() == Triple::aarch64)
    return "+v8.1a,+v8.2a,+v8.3a,+fullfp16,+aes,+sha2,+sha3,+sm4,+crc,+lse,+rdm,+dotprod,+fp16fml,"
           "+flagm,+rand,+pauth,+jsconv,+complxnum,+rcpc,+rcpc-immo,+fptoint,+sb,+predres,+ccdp,+sve";
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

  explicit TargetContext(const char *name, bool assembling = false)
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
    subtarget.reset(target->createMCSubtargetInfo(triple, "", targetFeatures(triple, assembling)));
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

Disassembly disassemble(const char *triple, const uint8_t *bytes, size_t size,
                        uint64_t address) {
  TargetContext context(triple);
  MCContext machineContext(context.triple, *context.asmInfo,
                           *context.registers, *context.subtarget);
  auto decoder = std::unique_ptr<MCDisassembler>(
      context.target->createMCDisassembler(*context.subtarget, machineContext));
  if (!decoder)
    throw std::runtime_error("target does not support disassembly");
  unsigned dialect = context.triple.isX86() ? 1 : context.asmInfo->getAssemblerDialect();
  auto printer = context.target->createMCInstPrinter(
      context.triple, dialect, *context.asmInfo, *context.instructions,
      *context.registers);
  if (!printer)
    throw std::runtime_error("unable to create instruction printer");
  printer->setPrintImmHex(true);

  Disassembly result;
  uint64_t decodedSize = 0;
  ArrayRef<uint8_t> input(bytes, size);
  auto status = decoder->getInstruction(result.instruction, decodedSize, input, address,
                                        nulls());
  if (status != MCDisassembler::Success)
    throw std::runtime_error("instruction decoding failed");
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
    TargetContext context(lean_string_cstr(triple));
    const char *expected = lean_string_cstr(name);
    for (unsigned opcode = 0; opcode != context.instructions->getNumOpcodes(); ++opcode)
      if (context.instructions->getName(opcode) == expected)
        return lean_io_result_mk_ok(lean_uint64_to_nat(opcode));
    return io_error("unknown LLVM opcode");
  } catch (const std::exception &error) {
    return io_error(error.what());
  }
}

extern "C" lean_obj_res bap_llvm_opcode_id_opt(lean_obj_arg triple, lean_obj_arg name,
                                                 lean_obj_arg) {
  initialize();
  try {
    TargetContext context(lean_string_cstr(triple));
    const char *expected = lean_string_cstr(name);
    for (unsigned opcode = 0; opcode != context.instructions->getNumOpcodes(); ++opcode) {
      if (context.instructions->getName(opcode) == expected) {
        lean_object *result = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(result, 0, lean_uint64_to_nat(opcode));
        return lean_io_result_mk_ok(result);
      }
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
