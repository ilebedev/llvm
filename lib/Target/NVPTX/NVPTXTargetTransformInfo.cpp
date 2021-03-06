//===-- NVPTXTargetTransformInfo.cpp - NVPTX specific TTI pass ---------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// \file
// This file implements a TargetTransformInfo analysis pass specific to the
// NVPTX target machine. It uses the target's detailed information to provide
// more precise answers to certain TTI queries, while letting the target
// independent and default TTI implementations handle the rest.
//
//===----------------------------------------------------------------------===//

#include "NVPTXTargetMachine.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/Debug.h"
#include "llvm/Target/CostTable.h"
#include "llvm/Target/TargetLowering.h"
using namespace llvm;

#define DEBUG_TYPE "NVPTXtti"

// Declare the pass initialization routine locally as target-specific passes
// don't have a target-wide initialization entry point, and so we rely on the
// pass constructor initialization.
namespace llvm {
void initializeNVPTXTTIPass(PassRegistry &);
}

namespace {

class NVPTXTTI final : public ImmutablePass, public TargetTransformInfo {
  const NVPTXTargetMachine *TM;
  const NVPTXSubtarget *ST;
  const NVPTXTargetLowering *TLI;

  /// Estimate the overhead of scalarizing an instruction. Insert and Extract
  /// are set if the result needs to be inserted and/or extracted from vectors.
  unsigned getScalarizationOverhead(Type *Ty, bool Insert, bool Extract) const;

public:
  NVPTXTTI() : ImmutablePass(ID), TM(nullptr), ST(nullptr), TLI(nullptr) {
    llvm_unreachable("This pass cannot be directly constructed");
  }

  NVPTXTTI(const NVPTXTargetMachine *TM)
      : ImmutablePass(ID), TM(TM), ST(TM->getSubtargetImpl()),
        TLI(TM->getSubtargetImpl()->getTargetLowering()) {
    initializeNVPTXTTIPass(*PassRegistry::getPassRegistry());
  }

  void initializePass() override { pushTTIStack(this); }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    TargetTransformInfo::getAnalysisUsage(AU);
  }

  /// Pass identification.
  static char ID;

  /// Provide necessary pointer adjustments for the two base classes.
  void *getAdjustedAnalysisPointer(const void *ID) override {
    if (ID == &TargetTransformInfo::ID)
      return (TargetTransformInfo *)this;
    return this;
  }

  bool hasBranchDivergence() const override;

  /// @}
};

} // end anonymous namespace

INITIALIZE_AG_PASS(NVPTXTTI, TargetTransformInfo, "NVPTXtti",
                   "NVPTX Target Transform Info", true, true, false)
char NVPTXTTI::ID = 0;

ImmutablePass *
llvm::createNVPTXTargetTransformInfoPass(const NVPTXTargetMachine *TM) {
  return new NVPTXTTI(TM);
}

bool NVPTXTTI::hasBranchDivergence() const { return true; }
