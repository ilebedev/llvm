//===-- InstrumentMOP.cpp - callbacks for every MOP ------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This allows compiled code to be instrumented with library callbacks for
// *every* memory access, simplifying for example the collection of traces.
// AddressSanitizer was the template for this code.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Instrumentation.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/Triple.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Endian.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/ASanStackFrameLayout.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include <algorithm>
#include <string>
#include <system_error>

using namespace llvm;

#define DEBUG_TYPE "imop"

// Accesses sizes are powers of two: 1, 2, 4, 8, 16.
//static const size_t kNumberOfAccessSizes = 5;

// Command-line flags.

// This flag may need to be replaced with -f[no-]asan-reads.
static cl::opt<bool> ClInstrumentReads("imop-instrument-reads",
       cl::desc("instrument read instructions"), cl::Hidden, cl::init(true));
static cl::opt<bool> ClInstrumentWrites("imop-instrument-writes",
       cl::desc("instrument write instructions"), cl::Hidden, cl::init(true));
static cl::opt<bool> ClInstrumentAtomics("imop-instrument-atomics",
       cl::desc("instrument atomic instructions (rmw, cmpxchg)"),
       cl::Hidden, cl::init(true));


//STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
//STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");

namespace {
/// Frontend-provided metadata for source location.
struct LocationMetadata {
  StringRef Filename;
  int LineNo;
  int ColumnNo;

  LocationMetadata() : Filename(), LineNo(0), ColumnNo(0) {}

  bool empty() const { return Filename.empty(); }

  void parse(MDNode *MDN) {
    assert(MDN->getNumOperands() == 3);
    MDString *MDFilename = cast<MDString>(MDN->getOperand(0));
    Filename = MDFilename->getString();
    LineNo = cast<ConstantInt>(MDN->getOperand(1))->getLimitedValue();
    ColumnNo = cast<ConstantInt>(MDN->getOperand(2))->getLimitedValue();
  }
};

// Instrument MOP: Instrument memory operations
struct InstrumentMOP : public FunctionPass {
  InstrumentMOP() : FunctionPass(ID) {
    initializeBreakCriticalEdgesPass(*PassRegistry::getPassRegistry());
  }
  const char *getPassName() const override {
    return "InstrumentMOPFunctionPass";
  }
  bool runOnFunction(Function &F) override;
  bool doInitialization(Module &M) override;
  static char ID;  // Pass identification, replacement for typeid

 private:
  int LongSize;
  Type *IntptrTy;
  LLVMContext *C;
  const DataLayout *DL;
};

} // namespace

char InstrumentMOP::ID = 0;

INITIALIZE_PASS(InstrumentMOP, "imop",
    "InstrumentMOP: adds calbacks before every memory acccess to allow special handling or book keeping.",
    false, false)
FunctionPass *llvm::createInstrumentMOPFunctionPass() {
  return new InstrumentMOP();
}

/*
static size_t TypeSizeToSizeIndex(uint32_t TypeSize) {
  size_t Res = countTrailingZeros(TypeSize / 8);
  assert(Res < kNumberOfAccessSizes);
  return Res;
}
*/

// virtual
bool InstrumentMOP::doInitialization(Module &M) {
  // Initialize the private fields. No one has accessed them before.
  DataLayoutPass *DLP = getAnalysisIfAvailable<DataLayoutPass>();
  if (!DLP)
    report_fatal_error("data layout missing");
  DL = &DLP->getDataLayout();

  C = &(M.getContext());
  LongSize = DL->getPointerSizeInBits();
  IntptrTy = Type::getIntNTy(*C, LongSize);

  return true;
}

bool InstrumentMOP::runOnFunction(Function &F) {
  DEBUG(dbgs() << "IMOP instrumenting:\n" << F << "\n");

  // We want to instrument every address only once per basic block (unless there
  // are calls between uses).
  SmallVector<Instruction*, 16> ToInstrument;
  SmallVector<Instruction*, 8> NoReturnCalls;
  SmallVector<BasicBlock*, 16> AllBlocks;
  SmallVector<Instruction*, 16> PointerComparisonsOrSubtracts;

  //int NumAllocas = 0;
  //bool IsWrite;
  //unsigned Alignment;

  // Fill the set of memory operations to instrument.
  for (auto &BB : F) {
    AllBlocks.push_back(&BB);
    for (auto &Inst : BB) {
      ToInstrument.push_back(&Inst);
    }
  }

  // Instrument.
  int NumInstrumented = 0;
  for (auto Inst : ToInstrument) {
    /*
    if (ClDebugMin < 0 || ClDebugMax < 0 ||
        (NumInstrumented >= ClDebugMin && NumInstrumented <= ClDebugMax)) {
      if (isInterestingMemoryAccess(Inst, &IsWrite, &Alignment))
        instrumentMop(Inst, UseCalls);
      else
        instrumentMemIntrinsic(cast<MemIntrinsic>(Inst));
    }
    */

    //TODO: call Instruction
    //IRBuilder<> IRB(&I);
    //IRB.createCall(
    //    mop_instrumentation,
    //    TODO: const char Name?
    //  );
    //NumInstrumented++;
  }

  bool res = NumInstrumented > 0 || false;

  DEBUG(dbgs() << "IMPO done instrumenting: " << res << " " << F << "\n");
  return res;
}

