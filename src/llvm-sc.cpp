#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <llvm/IR/LegacyPassManager.h>

#include "llvm-version.h"
#include "codegen_shared.h"
#include "julia.h"
using namespace llvm;

#define DEBUG_TYPE "sc"
#undef DEBUG

static bool isTBAA(MDNode *TBAA, std::initializer_list<const char*> const strset)
{
    if (!TBAA)
        return false;
    if (TBAA->getNumOperands() > 2) {
        // Get Access Type from Access Tag
        TBAA = cast<MDNode>(TBAA->getOperand(1).get());
        auto str = cast<MDString>(TBAA->getOperand(0))->getString();
        for (auto str2 : strset) {
            if (str == str2) {
                return true;
            }
        }
    }
    return false;
}

struct SC : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    SC() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
        bool changed = false;
        for (auto &BB : F.getBasicBlockList()) {
            for (auto &I : BB.getInstList()) {
                if (!isa<LoadInst>(I) && !isa<StoreInst>(I))
                    continue;
                if (I.getMetadata(LLVMContext::MD_invariant_load))
                    continue;
                MDNode *TBAA = I.getMetadata(LLVMContext::MD_tbaa);
                if (isTBAA(TBAA, {"jtbaa", "jtbaa_value", "jtbaa_data", "jtbaa_mutab", "jtbaa_arraybuf", "jtbaa_ptrarraybuf"})) {
                    if (isa<LoadInst>(I)) {
                        LoadInst &LI = cast<LoadInst>(I);
                        PointerType *PTy = dyn_cast<PointerType>(LI.getOperand(0)->getType());
                        Type *ElTy = PTy->getElementType();
                        const DataLayout &DL = F.getParent()->getDataLayout();
                        unsigned Size = DL.getTypeSizeInBits(ElTy);
                        if (LI.getAlignment() == 0
                                || (!ElTy->isIntegerTy() && !ElTy->isPointerTy() && !ElTy->isFloatingPointTy())
                                || (Size < 8 || (Size & (Size - 1)))){
                            IRBuilder<> builder(&LI);
                            builder.SetCurrentDebugLocation(LI.getDebugLoc());
                            FenceInst *acquire = new FenceInst(builder.getContext(), AtomicOrdering::Acquire, SyncScope::System);
                            acquire->insertAfter(&LI);
                        } else {
                            LI.setOrdering(AtomicOrdering::SequentiallyConsistent);
                        }
                        changed = true;
                    } else if (isa<StoreInst>(I)) {
                        StoreInst &SI = cast<StoreInst>(I);
                        PointerType *PTy = dyn_cast<PointerType>(SI.getOperand(1)->getType());
                        Type *ElTy = PTy->getElementType();
                        const DataLayout &DL = F.getParent()->getDataLayout();
                        unsigned Size = DL.getTypeSizeInBits(ElTy);
                        if (SI.getAlignment() == 0
                                || (!ElTy->isIntegerTy() && !ElTy->isPointerTy() && !ElTy->isFloatingPointTy())
                                || (Size < 8 || (Size & (Size - 1)))) {
                            IRBuilder<> builder(&SI);
                            builder.SetCurrentDebugLocation(SI.getDebugLoc());
                            FenceInst *release = new FenceInst(builder.getContext(), AtomicOrdering::Release, SyncScope::System);
                            release->insertBefore(&SI);
                            FenceInst *sc = new FenceInst(builder.getContext(), AtomicOrdering::SequentiallyConsistent, SyncScope::System);
                            sc->insertAfter(&SI);
                        } else {
                            SI.setOrdering(AtomicOrdering::SequentiallyConsistent);
                        }
                        changed = true;
                    }
                }

            }
        }

      return changed;
    }


    StringRef getPassName() const override {
      return StringRef("SC");
    }

//    void getAnalysisUsage(AnalysisUsage &AU) const override{
//        AU.addRequired<PromoteLegacyPass>();
//    }
};

char SC::ID = 0;
static RegisterPass<SC> X("SC", "Rewrite read and write with atomic access", false, false);

Pass *createSCPass() {
    return new SC();
}

extern "C" JL_DLLEXPORT void LLVMExtraAddSCPass(LLVMPassManagerRef PM)
{
    unwrap(PM)->add(createSCPass());
}
