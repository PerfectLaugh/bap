//===- flattening.cpp - The flattening of Obfuscator-LLVM -----------------===//
//
// The flattening pass of Obfuscator-LLVM 4.0, lib/Transforms/Obfuscation/
// Flattening.cpp and Utils.cpp, which is distributed under the University of
// Illinois Open Source License, ported to the pass plugins of LLVM 22, e.g.,
//
//   opt -load-pass-plugin=./flattening.so -passes=lower-switch,ollvm-fla
//
// The numbers of the cases are scrambled with a fixed key, instead of the
// random one, so that the obfuscated programs are the same, when they are
// built again.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Transforms/Utils/Local.h"
#include <vector>

using namespace llvm;

namespace {

// the scrambled number of the case, see CryptoUtils::scramble32
uint32_t scramble32(uint32_t x) {
  uint32_t h = x ^ 0x5bd1e995u;
  h ^= h >> 16;
  h *= 0x85ebca6bu;
  h ^= h >> 13;
  h *= 0xc2b2ae35u;
  h ^= h >> 16;
  return h;
}

bool valueEscapes(Instruction *Inst) {
  BasicBlock *BB = Inst->getParent();
  for (User *U : Inst->users()) {
    Instruction *I = cast<Instruction>(U);
    if (I->getParent() != BB || isa<PHINode>(I))
      return true;
  }
  return false;
}

void fixStack(Function *f) {
  std::vector<PHINode *> tmpPhi;
  std::vector<Instruction *> tmpReg;
  BasicBlock *bbEntry = &*f->begin();
  do {
    tmpPhi.clear();
    tmpReg.clear();
    for (BasicBlock &i : *f) {
      for (Instruction &j : i) {
        if (auto *phi = dyn_cast<PHINode>(&j)) {
          tmpPhi.push_back(phi);
          continue;
        }
        if (!(isa<AllocaInst>(&j) && j.getParent() == bbEntry) &&
            (valueEscapes(&j) || j.isUsedOutsideOfBlock(&i))) {
          tmpReg.push_back(&j);
          continue;
        }
      }
    }
    for (Instruction *I : tmpReg)
      DemoteRegToStack(*I);
    for (PHINode *P : tmpPhi)
      DemotePHIToStack(P);
  } while (!tmpReg.empty() || !tmpPhi.empty());
}

bool flatten(Function *f) {
  std::vector<BasicBlock *> origBB;
  LLVMContext &ctx = f->getContext();
  Type *i32 = Type::getInt32Ty(ctx);

  for (BasicBlock &bb : *f) {
    origBB.push_back(&bb);
    if (isa<InvokeInst>(bb.getTerminator()))
      return false;
  }
  if (origBB.size() <= 1)
    return false;
  origBB.erase(origBB.begin());

  BasicBlock *insert = &*f->begin();
  BranchInst *br = dyn_cast<BranchInst>(insert->getTerminator());
  if ((br && br->isConditional()) ||
      insert->getTerminator()->getNumSuccessors() > 1) {
    BasicBlock::iterator i = insert->end();
    --i;
    if (insert->size() > 1)
      --i;
    BasicBlock *tmpBB = insert->splitBasicBlock(i, "first");
    origBB.insert(origBB.begin(), tmpBB);
  }

  insert->getTerminator()->eraseFromParent();

  AllocaInst *switchVar = new AllocaInst(i32, 0, "switchVar", insert);
  new StoreInst(ConstantInt::get(i32, scramble32(0)), switchVar, insert);

  BasicBlock *loopEntry = BasicBlock::Create(ctx, "loopEntry", f, insert);
  BasicBlock *loopEnd = BasicBlock::Create(ctx, "loopEnd", f, insert);
  LoadInst *load = new LoadInst(i32, switchVar, "switchVar", loopEntry);

  insert->moveBefore(loopEntry);
  BranchInst::Create(loopEntry, insert);
  BranchInst::Create(loopEntry, loopEnd);

  BasicBlock *swDefault = BasicBlock::Create(ctx, "switchDefault", f, loopEnd);
  BranchInst::Create(loopEnd, swDefault);

  SwitchInst *switchI = SwitchInst::Create(load, swDefault, 0, loopEntry);

  for (BasicBlock *i : origBB) {
    i->moveBefore(loopEnd);
    switchI->addCase(cast<ConstantInt>(ConstantInt::get(
                         i32, scramble32(switchI->getNumCases()))),
                     i);
  }

  auto caseOf = [&](BasicBlock *succ) {
    ConstantInt *numCase = switchI->findCaseDest(succ);
    if (!numCase)
      numCase = cast<ConstantInt>(
          ConstantInt::get(i32, scramble32(switchI->getNumCases() - 1)));
    return numCase;
  };

  for (BasicBlock *i : origBB) {
    Instruction *term = i->getTerminator();
    if (term->getNumSuccessors() == 0)
      continue;
    if (term->getNumSuccessors() == 1) {
      ConstantInt *numCase = caseOf(term->getSuccessor(0));
      term->eraseFromParent();
      new StoreInst(numCase, switchVar, i);
      BranchInst::Create(loopEnd, i);
      continue;
    }
    if (term->getNumSuccessors() == 2) {
      ConstantInt *numCaseTrue = caseOf(term->getSuccessor(0));
      ConstantInt *numCaseFalse = caseOf(term->getSuccessor(1));
      BranchInst *br = cast<BranchInst>(term);
      SelectInst *sel = SelectInst::Create(br->getCondition(), numCaseTrue,
                                           numCaseFalse, "", term->getIterator());
      term->eraseFromParent();
      new StoreInst(sel, switchVar, i);
      BranchInst::Create(loopEnd, i);
      continue;
    }
  }

  fixStack(f);
  return true;
}

struct Flattening : PassInfoMixin<Flattening> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &) {
    if (F.isDeclaration() || F.hasAvailableExternallyLinkage())
      return PreservedAnalyses::all();
    return flatten(&F) ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};

} // namespace

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "ollvm-flattening", "1.0",
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (name == "ollvm-fla") {
                    FPM.addPass(Flattening());
                    return true;
                  }
                  return false;
                });
          }};
}
