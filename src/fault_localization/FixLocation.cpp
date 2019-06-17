/* #########################################################################
This file is part of crash-free-fix.
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
using namespace std;


static cl::opt<string> functionCallList("lf",
                                        cl::desc("Specify the list of executed function by failing test"),
                                        cl::value_desc("F1 F2 ... Fn"));

static cl::opt<string> targetFunction("fun",
                                      cl::desc("Specify the function where the crash is triggered"),
                                      cl::value_desc("FUNCTION_NAME"));

static cl::opt<int> targetNO("no",
                             cl::desc("Specify the crash line number"),
                             cl::value_desc("LINE_NUMBER"));

struct SeenEntry{
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

struct FixEntry{
    string description;
    string funcName;
    int lineNo;

    bool operator==(const FixEntry &fixEntry){
        return funcName == fixEntry.funcName && lineNo == fixEntry.lineNo;
    }

    bool operator<(const FixEntry &fixEntry) const
    {
        if (funcName == fixEntry.funcName)
            return lineNo > fixEntry.lineNo;
        return funcName < fixEntry.funcName;
    }
};

static bool isCrashFunction = true;
static std::set<FixEntry> potentialFixLocs;
static vector<int> argumentsForBackwardAnalysis;

bool isFuncArgument(Function *func, Value * val){
    int index = 0;
    for(auto arg = func->arg_begin(); arg != func->arg_end(); ++arg, index++) {
        if (&(*arg) == &(*val)){
            argumentsForBackwardAnalysis.push_back(index);
            return true;
        }
    }
    return false;
}

static void findFixLocsDataFlow(const DominatorTree &DT, std::set<SeenEntry> &Seen,
                                Value *X, Instruction *Dst, Function* funcName);

static void printout(const char* message, const string funcName, const Instruction* inst){
    const DebugLoc debugLoc = inst->getDebugLoc();
    // the instruction does not contain debug location
    if (!debugLoc){
        fprintf(stderr, "debug information is not found.");;
    }
    int lineNo = debugLoc.getLine();

    FixEntry Entry = {message, funcName, lineNo};
    auto i = potentialFixLocs.find(Entry);
    if (i != potentialFixLocs.end())
        return;
    potentialFixLocs.insert(Entry);

    // fprintf(stderr, "%s", message);
    // inst->print(errs());
    // fprintf(stderr, "line no: %d\n", lineNo);
}

/*
 * Suggest fix locations for X.
 *
 * Does a forward data-flow analysis.
 */
static void findFixLocsForward(const DominatorTree &DT, std::set<SeenEntry> &Seen,
                               Value *X, Instruction *Dst, Function * func)
{
    SeenEntry Entry = {/*forward=*/true, X};
    auto i = Seen.find(Entry);
    if (i != Seen.end())
        return;
    Seen.insert(Entry);

    // fprintf(stderr, "\t\tFORWARD ");
    // X->print(errs()); fprintf(stderr, "\n");

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

            printout("\t\33[32mFIX LOC\33[0m (control flow)", func->getName(), Cmp);

            findFixLocsDataFlow(DT, Seen, Cmp->getOperand(0), Dst, func);
            findFixLocsDataFlow(DT, Seen, Cmp->getOperand(1), Dst, func);
            break;
        }
        return;
    }
    else if(auto *store = dyn_cast<StoreInst>(X)){ //store instruction may affect the value of memory
        if (!DT.dominates(store, Dst))
        {
            return;         // Does not dominate
        }
        findFixLocsDataFlow(DT, Seen, store->getOperand(0), Dst, func);
        findFixLocsDataFlow(DT, Seen, store->getOperand(1), Dst, func);
    }

    // This is a forward analysis, so we look at all "users" of X.
    for (auto *User: X->users())
    {
        if(isa<StoreInst>(User)){
            if (isFuncArgument(func, User->getOperand(0)))
                fprintf(stderr, "PROPAGATE ARGUMENT\n");
        }


        if (isa<GetElementPtrInst>(User) ||
            isa<CastInst>(User) ||
            isa<PHINode>(User) ||
            isa<BinaryOperator>(User) ||
            isa<ICmpInst>(User) ||
            isa<LoadInst>(User) ||
            isa<StoreInst>(User))
        {
            findFixLocsForward(DT, Seen, User, Dst, func);
        }
    }
}

/*
 * Suggest fix locations for X.
 *
 * Does a backwards data-flow analysis.
 */
static void findFixLocsDataFlow(const DominatorTree &DT, std::set<SeenEntry> &Seen,
                                Value *X, Instruction *Dst, Function * func)
{
    SeenEntry Entry = {/*forward=*/false, X};
    auto i = Seen.find(Entry);
    if (i != Seen.end())
        return;
    Seen.insert(Entry);

    // Only care about instructions:
    if (!isa<Instruction>(X))
        return;

    // fprintf(stderr, "\t\tBACKWARD ");
    // X->print(errs()); fprintf(stderr, "\n");

    // Find control-flow locations:
    findFixLocsForward(DT, Seen, X, Dst, func);

    // Data-flow patching:
    if (auto *GEP = dyn_cast<GetElementPtrInst>(X))
    {
        // Pointer arithmetic: ptr = ptr + k;
        if (DT.dominates(GEP, Dst))
        {
            printout("\t\33[32mFIX LOC\33[0m (data flow)", func->getName(), GEP);
        }

        int numIdxs = GEP->getNumIndices();
        for (unsigned int j = 0; j < numIdxs; j++)
        {
            Value *Idx = GEP->getOperand(j+1);
            findFixLocsDataFlow(DT, Seen, Idx, Dst, func);
        }
        findFixLocsDataFlow(DT, Seen, GEP->getPointerOperand(), Dst, func);
    }
    else if (auto *BinOp = dyn_cast<BinaryOperator>(X))
    {
        if (DT.dominates(BinOp, Dst))
        {
            printout("\t\33[32mFIX LOC\33[0m (data flow)", func->getName(), BinOp);
        }
        findFixLocsDataFlow(DT, Seen, BinOp->getOperand(0), Dst, func);
        findFixLocsDataFlow(DT, Seen, BinOp->getOperand(1), Dst, func);
    }
    else if (auto *Cast = dyn_cast<CastInst>(X))
    {
        findFixLocsDataFlow(DT, Seen, Cast->getOperand(0), Dst, func);
    }
    else if (auto *PHI = dyn_cast<PHINode>(X))
    {
        // PHI-nodes: attempt to find fix locations along all paths.
        //
        // Note: Perhaps a better approach is to restrict the analysis to the
        // path of the failing test case.
        size_t numValues = PHI->getNumIncomingValues();
        for (size_t j = 0; j < numValues; j++)
            findFixLocsDataFlow(DT, Seen, PHI->getIncomingValue(j), Dst, func);
    }
    else if(auto *load = dyn_cast<LoadInst>(X)){
        findFixLocsDataFlow(DT, Seen, load->getOperand(0), Dst, func);
    }
    else if(auto *store = dyn_cast<StoreInst>(X)){
        // X->print(errs());
        if (isFuncArgument(func, store->getOperand(0)))
            fprintf(stderr, "PROPAGATE ARGUMENT\n");
        findFixLocsDataFlow(DT, Seen, store->getOperand(0), Dst, func);
        findFixLocsDataFlow(DT, Seen, store->getOperand(1), Dst, func);
    }
    else
    {
        // Not yet implemented!
        // fprintf(stderr, "\t\t\33[33mSTOP\33[0m [not yet implemented] \n");
        // X->print(errs()); fprintf(stderr, "\n");
    }
}

static void suggestFixLocs(const DominatorTree &DT, Instruction *inst, Function *func)
{
    fprintf(stderr, "\n-------------------------------------------------------\n");
    fprintf(stderr, "\t\33[31mSTORE\33[0m ");
    inst->print(errs()); fprintf(stderr, "\n");
    std::set<SeenEntry> Seen;
    findFixLocsDataFlow(DT, Seen, inst, inst, func);
}


static void suggestFixLocs(Module &M)
{
    // parse function list
    vector<string> funcCalls;
    size_t pos = 0;
    std::string token;
    // TODO: check crash function
    while ((pos = functionCallList.find(" ")) != std::string::npos) {
        token = functionCallList.substr(0, pos);
        funcCalls.push_back(token);
        functionCallList.erase(0, pos + 1);
    }
    funcCalls.push_back(functionCallList);

    // set<string> seenFun;
    string callee, current_function;
    for(long i=funcCalls.size()-1; i>=0; i--){
        // if(seenFun.find(funcCalls[i]) != seenFun.end())
        //     continue;
        // seenFun.insert(funcCalls[i]);
        current_function = funcCalls[i];

        Function *F = M.getFunction(current_function);

        fprintf(stderr, "\nFound \33[32mFUNCTION\33[0m %s\n",
                F->getName().str().c_str());

        DominatorTree DT(*F);
        int index = 0;
        for (auto &BB: *F)
        {
            for (auto &I: BB) {
                index++;
                if (isCrashFunction && index == targetNO){
                    if (auto *inst = dyn_cast<Instruction>(&I)) {
                        std::set<SeenEntry> Seen;
                        findFixLocsDataFlow(DT, Seen, inst, inst, F);
                        // suggestFixLocs(DT, dyn_cast<Instruction>(inst), F);
                    }
                    isCrashFunction = false;
                    goto done;
                }
                else if(!isCrashFunction && isa<CallInst>(&I)){
                    auto *inst = dyn_cast<CallInst>(&I);
                    if (inst->getCalledFunction()->getName() == callee){
                        for(int argumentIndex: argumentsForBackwardAnalysis){
                            std::set<SeenEntry> Seen;
                            findFixLocsDataFlow(DT, Seen, inst->getArgOperand(argumentIndex), inst, F);
                            // suggestFixLocs(DT, inst->getArgOperand(argumentIndex), F);
                        }
                        goto done;
                    }
                }
            }
        }
    done:
        callee = current_function;
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

        FixLoc() : ModulePass(ID) {
        }

        virtual bool runOnModule(Module &M)
        {
            suggestFixLocs(M);
            for (FixEntry fixEntry: potentialFixLocs){
                fprintf(stderr, "%s", fixEntry.description.c_str());
                // inst->print(errs());
                fprintf(stderr, "\t%s:%d\n", fixEntry.funcName.c_str(), fixEntry.lineNo);
            }
            return true;
        }
    };

    char FixLoc::ID = 0;
}

#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/CommandLine.h"


static RegisterPass<FixLoc> X("fixloc", "FixLoc pass");

static void register_pass(const PassManagerBuilder &PMB,
                          legacy::PassManagerBase &PM)
{
    PM.add(new FixLoc());
}

static RegisterStandardPasses RegisterPass(
        PassManagerBuilder::EP_LoopOptimizerEnd, register_pass);

