#include <llvm/Analysis/LoopPass.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Pass.h>

#include <llvm/IR/LegacyPassManager.h>

#include <set>

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

static void getTBAAName(const char *prefix, MDNode *TBAA)
{
    if (!TBAA)
        return;
    if (TBAA->getNumOperands() > 2) {
        // Get Access Type from Access Tag
        TBAA = cast<MDNode>(TBAA->getOperand(1).get());
        auto str = cast<MDString>(TBAA->getOperand(0))->getString();
        printf("%s: %s\n", prefix, str);
    }
    return;
}

struct SC : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    SC() : FunctionPass(ID) {}

    bool runOnFunction(Function &F) override {
        bool changed = false;
        std::set<BasicBlock *> BBs;
        for (auto &BB : F.getBasicBlockList()) {
            BBs.insert(&BB);
        }   
        //Function *loopinfo_marker = F.getParent()->getFunction("julia.loopinfo_marker");
        //if (loopinfo_marker) {
        //     for (User *U : loopinfo_marker->users()) {
        //        Instruction *I = cast<Instruction>(U);
        //        if (I->getParent()->getParent() != &F)
        //            continue;
        //        LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
        //        Loop *L = LI.getLoopFor(I->getParent());

        //        bool skip_sc = false;
        //        // Walk `julia.loopinfo` metadata and filter out `julia.noscloop`
        //        if (I->hasMetadataOtherThanDebugLoc()) {
        //            MDNode *JLMD= I->getMetadata("julia.loopinfo");
        //            if (JLMD) {
        //                LLVM_DEBUG(dbgs() << "LSL: has julia.loopinfo metadata with " << JLMD->getNumOperands() <<" operands\n");
        //                for (unsigned i = 0, ie = JLMD->getNumOperands(); i < ie; ++i) {
        //                    Metadata *Op = JLMD->getOperand(i);
        //                    const MDString *S = dyn_cast<MDString>(Op);
        //                    if (S) {
        //                        LLVM_DEBUG(dbgs() << "LSL: found " << S->getString() << "\n");
        //                        if (S->getString().startswith("julia")) {
        //                            if (S->getString().equals("julia.noscloop"))
        //                                skip_sc = true;
        //                            continue;
        //                        }
        //                    }
        //                }
        //            }
        //        }

        //        if (skip_sc) {
        //            for (BasicBlock *BB : L->blocks()) {
        //                BBs.erase(BB);
        //            }
        //        }
        //     }
        //}

        for (auto *BB : BBs) {
            for (auto &I : BB->getInstList()) {
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
                        if (LI.getPointerAddressSpace() == DL.getAllocaAddrSpace()) {
                            // load from alloca space
                            //getTBAAName("alloca load", TBAA);
                            continue;
                        }
                        //if (LI.getAlignment() == 0
                        //        || (!ElTy->isIntegerTy() && !ElTy->isPointerTy() && !ElTy->isFloatingPointTy())
                        //        || (Size < 8 || (Size & (Size - 1)))){
                        //    //getTBAAName("unsupported atomic load", TBAA);
                        //    //ElTy->dump();
                        //    //printf("a: %d, s: %d\n", LI.getAlignment(), Size);
                        //    IRBuilder<> builder(&LI);
                        //    builder.SetCurrentDebugLocation(LI.getDebugLoc());
                        //    FenceInst *acquire = new FenceInst(builder.getContext(), AtomicOrdering::Acquire, SyncScope::System);
                        //    acquire->insertAfter(&LI);
                        //} else {
                            //if (LI.getAlignment() == 0) {
                            //    LI.setAlignment(DL.getABITypeAlignment(ElTy));
                            //}
                            LI.setOrdering(AtomicOrdering::SequentiallyConsistent);
                        //}
                        changed = true;
                    } else if (isa<StoreInst>(I)) {
                        StoreInst &SI = cast<StoreInst>(I);
                        PointerType *PTy = dyn_cast<PointerType>(SI.getOperand(1)->getType());
                        Type *ElTy = PTy->getElementType();
                        const DataLayout &DL = F.getParent()->getDataLayout();
                        unsigned Size = DL.getTypeSizeInBits(ElTy);
                        if (SI.getPointerAddressSpace() == DL.getAllocaAddrSpace()) {
                            //write to alloca space
                            //getTBAAName("alloca store", TBAA);
                            continue;
                        }
                        //if (SI.getAlignment() == 0
                        //        || (!ElTy->isIntegerTy() && !ElTy->isPointerTy() && !ElTy->isFloatingPointTy())
                        //        || (Size < 8 || (Size & (Size - 1)))) {
                        //    //getTBAAName("unsupported atomic store", TBAA);
                        //    //ElTy->dump();
                        //    //printf("a: %d, s: %d\n", SI.getAlignment(), Size);
                        //    IRBuilder<> builder(&SI);
                        //    builder.SetCurrentDebugLocation(SI.getDebugLoc());
                        //    FenceInst *release = new FenceInst(builder.getContext(), AtomicOrdering::Release, SyncScope::System);
                        //    release->insertBefore(&SI);
                        //    FenceInst *sc = new FenceInst(builder.getContext(), AtomicOrdering::SequentiallyConsistent, SyncScope::System);
                        //    sc->insertAfter(&SI);
                        //} else {
                            //if (SI.getAlignment() == 0) {
                            //    SI.setAlignment(DL.getABITypeAlignment(ElTy));
                            //}
                            SI.setOrdering(AtomicOrdering::SequentiallyConsistent);
                        //}
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

    void getAnalysisUsage(AnalysisUsage &AU) const override{
        FunctionPass::getAnalysisUsage(AU);
        AU.addRequired<LoopInfoWrapperPass>();
        AU.addPreserved<LoopInfoWrapperPass>();
        AU.setPreservesCFG();
    }
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
