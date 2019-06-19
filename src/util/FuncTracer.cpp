/*
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
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Transforms/Utils/Local.h"


using namespace llvm;
using namespace std;

static void insertPrintf(Module *M, Instruction *I, std::string msg){
    IRBuilder<> builder(I);

    Function* funcPrintf = M->getFunction("printf");
    if (!funcPrintf) {
        std::vector<Type*> printfTypeVec;
        printfTypeVec.push_back(PointerType::get(IntegerType::get(M->getContext(), 8), 0));
        FunctionType* printfType = FunctionType::get(IntegerType::get(M->getContext(), 32), printfTypeVec, true);
        funcPrintf = Function::Create(printfType, GlobalValue::ExternalLinkage, "printf", M);
        funcPrintf->setCallingConv(CallingConv::C);
    }

    Constant *msgConst = ConstantDataArray::getString(M->getContext(), msg, true);

    // plus one for \0
    size_t len = msg.length() + 1;

    Type *arr_type = ArrayType::get(IntegerType::get(M->getContext(), 8), len);
    GlobalVariable *gvar_name = new GlobalVariable(*M,
                                                   arr_type,
                                                   true,
                                                   GlobalValue::PrivateLinkage,
                                                   msgConst,
                                                   ".str");

    gvar_name->setAlignment(1);
    ConstantInt *zero = ConstantInt::get(M->getContext(), APInt(32, StringRef("0"), 10));

    std::vector<Constant *> indices;
    indices.push_back(zero);
    indices.push_back(zero);
    Constant *get_ele_ptr = ConstantExpr::getGetElementPtr(arr_type, gvar_name, indices);

    builder.CreateCall(funcPrintf, get_ele_ptr);
}


namespace
{
    struct FuncTracer : public FunctionPass
    {
        static char ID;

        FuncTracer() : FunctionPass(ID) { }

        virtual bool runOnFunction (Function &F) override
        {
            if(F.isDeclaration()){
                return false;
            }
            Module* M = F.getParent();

            std::string enter = "CRASH_FREE_TRACER: IN  >>>> " + F.getName().str() + "\n";
            std::string exit =  "CRASH_FREE_TRACER: OUT >>>> " + F.getName().str() + "\n";


            BasicBlock& firstBB = *(F.begin());
            Instruction& firstI = *(firstBB.begin());

            insertPrintf(M, &firstI, enter);

            for (auto &BB: F) {
                for (auto &I: BB) {
                    if(ReturnInst* returnInst = dyn_cast<ReturnInst>(&I)){
                        insertPrintf(M, &I, exit);
                    }
                }
            }


            return true;
        }


    };

    char FuncTracer::ID = 0;
}


#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"

static RegisterPass<FuncTracer> X("func_tracer", "Instrumentation to dump the executed function");

static void register_pass(const PassManagerBuilder &PMB,
                          legacy::PassManagerBase &PM)
{
    PM.add(new FuncTracer());
}

static RegisterStandardPasses RegisterPass(PassManagerBuilder::EP_LoopOptimizerEnd, register_pass);

