#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include "llvm/IR/InstIterator.h"
#include <llvm/IR/Instructions.h>
#include <llvm/Pass.h>

#include <llvm/IR/LegacyPassManager.h>

#include "llvm-version.h"
#include "codegen_shared.h"
#include "julia.h"
using namespace llvm;

#define DEBUG_TYPE "sc"
#undef DEBUG

struct SCExpand : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    SCExpand() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
        bool changed = false;
        SmallVector<Instruction *, 1> AtomicInsts;

        // Changing control-flow while iterating through it is a bad idea, so gather a
        // list of all atomic instructions before we start.
        for (inst_iterator II = inst_begin(F), E = inst_end(F); II != E; ++II) {
            Instruction *I = &*II;
            if (I->isAtomic() && !isa<FenceInst>(I))
                AtomicInsts.push_back(I);
        }


        for (auto I : AtomicInsts) {
            auto LI = dyn_cast<LoadInst>(I);
            auto SI = dyn_cast<StoreInst>(I);
            auto RMWI = dyn_cast<AtomicRMWInst>(I);
            auto CASI = dyn_cast<AtomicCmpXchgInst>(I);
            assert((LI || SI || RMWI || CASI) && "Unknown atomic instruction");
            // For SC
            if (LI) {
                if (LI->getOrdering() == AtomicOrdering::SequentiallyConsistent) {
                    PointerType *PTy = dyn_cast<PointerType>(LI->getOperand(0)->getType());
                    Type *ElTy = PTy->getElementType();
                    const DataLayout &DL = LI->getModule()->getDataLayout();
                    unsigned Size = DL.getTypeSizeInBits(ElTy);
                    if ((!ElTy->isIntegerTy() && !ElTy->isPointerTy() && !ElTy->isFloatingPointTy())
                            || LI->getAlignment() == 0
#if defined(_OS_DARWIN_)
							|| LI->getAlignment() < Size
#endif
                            || (Size < 8 || (Size & (Size - 1)))){
                        IRBuilder<> builder(LI);
                        LI->setOrdering(AtomicOrdering::NotAtomic);

                        FenceInst *acquire = new FenceInst(builder.getContext(), AtomicOrdering::Acquire, SyncScope::System);
                        acquire->insertAfter(LI);
                        LI->setVolatile(1);
                        changed = true;
                        continue;
                    } 
                }
            } else if (SI) {
                if (SI->getOrdering() == AtomicOrdering::SequentiallyConsistent) {
                    PointerType *PTy = dyn_cast<PointerType>(SI->getOperand(1)->getType());
                    Type *ElTy = PTy->getElementType();
                    const DataLayout &DL = SI->getModule()->getDataLayout();
                    unsigned Size = DL.getTypeSizeInBits(ElTy);
                    if ((!ElTy->isIntegerTy() && !ElTy->isPointerTy() && !ElTy->isFloatingPointTy())
                            || SI->getAlignment() == 0
#if defined(_OS_DARWIN_)
							|| SI->getAlignment() < Size
#endif
                            || (Size < 8 || (Size & (Size - 1)))){
                        SI->setOrdering(AtomicOrdering::NotAtomic);
                        IRBuilder<> builder(SI);
                        FenceInst *release = new FenceInst(builder.getContext(), AtomicOrdering::Release, SyncScope::System);
                        release->insertBefore(SI);
                        FenceInst *sc = new FenceInst(builder.getContext(), AtomicOrdering::SequentiallyConsistent, SyncScope::System);
                        sc->insertAfter(SI);
                        SI->setVolatile(1);
                        changed = true;
                        continue;
                    }

                }
            }
        }
        return changed;
    }


    StringRef getPassName() const override {
      return StringRef("SC");
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override{
        FunctionPass::getAnalysisUsage(AU);
        AU.setPreservesCFG();
    }
};

char SCExpand::ID = 0;
static RegisterPass<SCExpand> X("SCExpand", "rewrite read and write that don't support atomic access", false, false);

Pass *createSCExpandPass() {
    return new SCExpand();
}

extern "C" JL_DLLEXPORT void LLVMExtraAddSCExpandPass(LLVMPassManagerRef PM)
{
    unwrap(PM)->add(createSCExpandPass());
}
