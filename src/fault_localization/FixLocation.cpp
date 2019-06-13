/* #########################################################################
This file is part of Fix2Fit.
Copyright (C) 2016

This is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
###########################################################################*/


/*
 * Simple tool to find fix locations.
 *
 * Commands:
 *
 * COMPILE THIS PASS:
 *      clang++-4.0 FixLoc.cpp -c -g -O0 -fPIC `llvm-config-4.0 --cxxflags` `llvm-config-4.0 --includedir`; clang++-4.0 -o FixLoc.so FixLoc.o -shared `llvm-config-4.0 --ldflags`
 *
 * USE THIS PASS:
 *		opt-4.0 -S -load=../LowFat/FixLoc.so -fixloc program.ll > /dev/null
 *
 * PREPARE PROGRAM FOR ANALYSIS:
 *		clang-4.0 -O0 -S -emit-llvm program.c; opt-4.0 -S -mem2reg -inline -dce program.ll > program1.ll; mv program1.ll program.ll
 */

#include <cassert>
#include <cstdio>
#include <cstring>

#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>

#include <cxxabi.h>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/DiagnosticPrinter.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/SpecialCaseList.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MD5.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

struct SeenEntry
{
    bool forward;
    Value *X;

    bool operator<(const SeenEntry &Entry) const
    {
        if (Entry.forward < forward)
            return true;
        if (Entry.forward > forward)
            return false;
        return (Entry.X < X);
    }
};

static void findFixLocsDataFlow(const DominatorTree &DT, std::set<SeenEntry> &Seen,
                                Value *X, Instruction *Dst);

/*
 * Suggest fix locations for X.
 *
 * Does a forward data-flow analysis.
 */
static void findFixLocsForward(const DominatorTree &DT, std::set<SeenEntry> &Seen,
                               Value *X, Instruction *Dst)
{
    SeenEntry Entry = {/*forward=*/true, X};
    auto i = Seen.find(Entry);
    if (i != Seen.end())
        return;
    Seen.insert(Entry);

//    fprintf(stderr, "\t\tFORWARD ");
//    X->dump();

    if (auto *Cmp = dyn_cast<ICmpInst>(X))
    {
        // We have found a comparison that may effect control flow.
        if (!DT.dominates(Cmp, Dst))
        {
            return;         // Does not dominate
        }
        for (auto *User: Cmp->users())
        {
            auto *Br = dyn_cast<BranchInst>(User);
            if (Br == nullptr)
                continue;   // Not a branch
            if (!Br->isConditional() || Br->getCondition() != Cmp)
                continue;   // Not conditional.
            fprintf(stderr, "\t\t\33[32mFIX LOC\33[0m (control flow) ");
            // Cmp->dump();
            Cmp->print(outs());
            findFixLocsDataFlow(DT, Seen, Cmp->getOperand(0), Dst);
            findFixLocsDataFlow(DT, Seen, Cmp->getOperand(1), Dst);
            break;
        }
        return;
    }

    // This is a forward analysis, so we look at all "users" of X.
    for (auto *User: X->users())
    {
        if (isa<GetElementPtrInst>(User) ||
            isa<CastInst>(User) ||
            isa<PHINode>(User) ||
            isa<BinaryOperator>(User) ||
            isa<ICmpInst>(User))
        {
            findFixLocsForward(DT, Seen, User, Dst);
        }
    }
}

/*
 * Suggest fix locations for X.
 *
 * Does a backwards data-flow analysis.
 */
static void findFixLocsDataFlow(const DominatorTree &DT, std::set<SeenEntry> &Seen,
                                Value *X, Instruction *Dst)
{
    SeenEntry Entry = {/*forward=*/false, X};
    auto i = Seen.find(Entry);
    if (i != Seen.end())
        return;
    Seen.insert(Entry);

    // Only care about instructions:
    if (!isa<Instruction>(X))
        return;

//    fprintf(stderr, "\t\tBACKWARD ");
//    X->dump();

    // Find control-flow locations:
    findFixLocsForward(DT, Seen, X, Dst);

    // Data-flow patching:
    if (auto *GEP = dyn_cast<GetElementPtrInst>(X))
    {
        // Pointer arithmetic: ptr = ptr + k;
        if (DT.dominates(GEP, Dst))
        {
            fprintf(stderr, "\t\t\33[32mFIX LOC\33[0m (data flow) ");
            GEP->print(outs());
        }

        int numIdxs = GEP->getNumIndices();
        for (int i = 0; i < numIdxs; i++)
        {
            Value *Idx = GEP->getOperand(i+1);
            findFixLocsDataFlow(DT, Seen, Idx, Dst);
        }
        findFixLocsDataFlow(DT, Seen, GEP->getPointerOperand(), Dst);
    }
    else if (auto *BinOp = dyn_cast<BinaryOperator>(X))
    {
        if (DT.dominates(BinOp, Dst))
        {
            fprintf(stderr, "\t\t\33[32mFIX LOC\33[0m (data flow) ");
            BinOp->print(outs());
        }
        findFixLocsDataFlow(DT, Seen, BinOp->getOperand(0), Dst);
        findFixLocsDataFlow(DT, Seen, BinOp->getOperand(1), Dst);
    }
    else if (auto *Cast = dyn_cast<CastInst>(X))
    {
        findFixLocsDataFlow(DT, Seen, Cast->getOperand(0), Dst);
    }
    else if (auto *PHI = dyn_cast<PHINode>(X))
    {
        // PHI-nodes: attempt to find fix locations along all paths.
        //
        // Note: Perhaps a better approach is to restrict the analysis to the
        // path of the failing test case.
        size_t numValues = PHI->getNumIncomingValues();
        for (size_t i = 0; i < numValues; i++)
            findFixLocsDataFlow(DT, Seen, PHI->getIncomingValue(i), Dst);
    }
    else
    {
        // Not yet implemented!
        fprintf(stderr, "\t\t\33[33mSTOP\33[0m [not yet implemented] ");
        X->print(outs());
    }
}

static void suggestFixLocs(const DominatorTree &DT, StoreInst *Store)
{
    fprintf(stderr, "\n-------------------------------------------------------\n");
    fprintf(stderr, "\t\33[31mSTORE\33[0m ");
    Store->print(outs());
    std::set<SeenEntry> Seen;
    findFixLocsDataFlow(DT, Seen, Store->getPointerOperand(), Store);
}

static void suggestFixLocs(const DominatorTree &DT, LoadInst *Load)
{
    fprintf(stderr, "\n-------------------------------------------------------\n");
    fprintf(stderr, "\t\33[31mLOAD\33[0m ");
    Load->print(outs());
    std::set<SeenEntry> Seen;
    findFixLocsDataFlow(DT, Seen, Load->getPointerOperand(), Load);
}

/*
 * NOTE: The current code analyzes fix locations for *all* loads/stores.
 *       This needs to be changed so that it only considers the variable of
 *       interest (& not necessarily load/store for other types of errors).
 */
static void suggestFixLocs(Module &M)
{
    for (auto &F: M)
    {
        fprintf(stderr, "\n\33[32mFUNCTION\33[0m %s\n",
                F.getName().str().c_str());
        DominatorTree DT(F);
        for (auto &BB: F)
        {
            for (auto &I: BB)
            {
                if (auto *Store = dyn_cast<StoreInst>(&I))
                    suggestFixLocs(DT, Store);
                else if (auto *Load = dyn_cast<LoadInst>(&I))
                    suggestFixLocs(DT, Load);
            }
        }
    }
}

/*
 * LLVM Module pass biolerplate.
 */

namespace
{
    struct FixLoc : public ModulePass
    {
        static char ID;

        FixLoc() : ModulePass(ID) { }

        virtual bool runOnModule(Module &M)
        {
            suggestFixLocs(M);
            return true;
        }

    };

    char FixLoc::ID = 0;
}

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"

static RegisterPass<FixLoc> X("fixloc", "FixLoc pass");

static void register_pass(const PassManagerBuilder &PMB,
                          legacy::PassManagerBase &PM)
{
    PM.add(new FixLoc());
}

static RegisterStandardPasses RegisterPass(
        PassManagerBuilder::EP_LoopOptimizerEnd, register_pass);

