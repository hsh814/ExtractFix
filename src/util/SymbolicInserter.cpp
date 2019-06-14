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

/*
 * LLVM Module pass biolerplate.
 */
 

static cl::opt<string> InsertFunction("insert_function", cl::init("-"), cl::desc("Insert function name"), cl::value_desc("function"));
static cl::opt<string> InsertIndex("insert_index", cl::init("-1"), cl::desc("Specify insert indexes"), cl::value_desc("idx0:idx1:...:idxN"));

inline bool ends_with(std::string const & value, std::string const & ending)
{
    if (ending.size() > value.size()) return false;
    return std::equal(ending.rbegin(), ending.rend(), value.rbegin());
}


static void makeSymbolic(const DominatorTree &DT, DependenceInfo &DI, Instruction* I, Instruction* idx){

	if(DT.dominates(I, idx)){
	
		std::unique_ptr<Dependence> D = DI.depends(idx, I, false);
		
		I->dump();
		idx->dump();
		if (D) {
			errs()<<"############################################\n";
		}
	}
}

static Instruction* getInstFromDbgInst(DbgDeclareInst* dbgDecl){

	if(MetadataAsValue* val = dyn_cast_or_null<MetadataAsValue>(dbgDecl->getOperand(0))){
		if(ValueAsMetadata* valueAsMetadata = dyn_cast<ValueAsMetadata>(val->getMetadata())){

            Value* key = valueAsMetadata->getValue();
    		
    		return dyn_cast_or_null<Instruction>(key);
   		}
   	}
   	return NULL;
}

static Constant* getStringConstantGEP(Module &M, std::string msg){

    Constant *msgConst = ConstantDataArray::getString(M.getContext(), msg, true);

    // plus one for \0
    size_t len = msg.length() + 1;

    Type *arr_type = ArrayType::get(IntegerType::get(M.getContext(), 8), len);
    GlobalVariable *gvar_name = new GlobalVariable(M,
                                                   arr_type,
                                                   true,
                                                   GlobalValue::PrivateLinkage,
                                                   msgConst,
                                                   ".str");
    gvar_name->setAlignment(1);

    ConstantInt *zero = ConstantInt::get(M.getContext(), APInt(32, StringRef("0"), 10));

    std::vector<Constant *> indices;
    indices.push_back(zero);
    indices.push_back(zero);

    Constant *get_ele_ptr = ConstantExpr::getGetElementPtr(arr_type, gvar_name, indices);
    return get_ele_ptr;
}

static string get_va_nm(Function *F, Value *param, map<Value *, string> &valueNameMap){
    int instCount = 0;
    for (BasicBlock& BB : *F) {
        instCount += std::distance(BB.begin(), BB.end());
    }
    int i = 0;
    while(i < instCount){
        i++;
        if(valueNameMap.count(param)){
            return valueNameMap[param];
        } else {

            if(BitCastInst* bc = dyn_cast<BitCastInst>(param)){
                param = dyn_cast<Instruction>(bc->getOperand(0));
                continue;
            }
            if(AllocaInst* al = dyn_cast<AllocaInst>(param)){
                param = al->getArraySize();
                continue;
            }
            if(SExtInst* se = dyn_cast<SExtInst>(param)){
                if(Value* oper = dyn_cast<Instruction>(se->getOperand(0))){
                    param = oper;
                    continue;
                } else {
                    break;
                }

            }

        }
    }
    static int counter = 0;
    string tmp_name = "tmp_" + F->getName().str() + "_" + std::to_string(counter);
    counter++;
    return tmp_name;
}

static int insert(Module &M, Function &F, Instruction &I, std::map<Value*, string> valueNameMap){
    int insertedInst = 0;
    // TODO: 
    if(LoadInst* load = dyn_cast<LoadInst>(&I)){
        IRBuilder<> builder(load);

        Function* func = M.getFunction("klee_make_symbolic");
        if (!func) {
            //void lowfat_insert_map(size_t size, void* result, MALLOC_LIST_HEAD* global_head)
            std::vector<Type*> params;
            params.push_back(PointerType::get(IntegerType::get(M.getContext(), 8), 0));
            params.push_back(IntegerType::get(M.getContext(), 64));
            params.push_back(PointerType::get(IntegerType::get(M.getContext(), 8), 0));

            FunctionType* func_tp = FunctionType::get(
                    Type::getVoidTy(M.getContext()),
                    params,
                    false);

            func = Function::Create(func_tp, GlobalValue::ExternalLinkage, "klee_make_symbolic", &M);
            func->setCallingConv(CallingConv::C);
        }

        Value* pointer = load->getPointerOperand();
        Value* pointerOp = pointer;
        Value* widthVal = nullptr;

        if (PointerType *PT = dyn_cast<PointerType>(pointer->getType())) {
            if (IntegerType *IT = dyn_cast<IntegerType>(PT->getPointerElementType())) {
                unsigned width = IT->getBitWidth();

                widthVal = ConstantInt::get(IntegerType::get(M.getContext(), 64), width/8, false);

                if (width != 8) {
                    pointerOp = builder.CreateBitCast(pointer, PointerType::get(IntegerType::get(M.getContext(), 8), 0));
                    insertedInst++;
                }
            }
        }

        string name = get_va_nm(&F, pointer, valueNameMap);
        Value* GEP = getStringConstantGEP(M, name);
        builder.CreateCall(func, {pointerOp, widthVal, GEP});
    }

    return insertedInst;
}

static std::map<Value*, string> collect_local_variable_metadata(Function& F){
    std::map<Value*, string> valueNameMap;
    for (auto &BB: F){
        for (auto &I: BB){

            if(DbgValueInst *dbgValue = dyn_cast<DbgValueInst>(&I)){
                if(MetadataAsValue* val = dyn_cast_or_null<MetadataAsValue>(dbgValue->getOperand(0))){
                    if(ValueAsMetadata* valueAsMetadata = dyn_cast<ValueAsMetadata>(val->getMetadata())){

                        Value* key = valueAsMetadata->getValue();
                        if(key != nullptr){
                            string name = dbgValue->getVariable()->getRawName()->getString();
                            valueNameMap[key] = name;
                        }
                    }
                }
            } else if (DbgDeclareInst* dbgDecl = dyn_cast<DbgDeclareInst>(&I)){
                if(MetadataAsValue* val = dyn_cast_or_null<MetadataAsValue>(dbgDecl->getOperand(0))){
                    if(ValueAsMetadata* valueAsMetadata = dyn_cast<ValueAsMetadata>(val->getMetadata())){
                        Value* key = valueAsMetadata->getValue();
                        if(key != nullptr){
                            string name = dbgDecl->getVariable()->getRawName()->getString();
                            valueNameMap[key] = name;
                        }
                    }
                }
            }
        }// end for(I)
    }// end for(BB)
    return valueNameMap;
}

namespace
{
    struct SymbolicInserter : public ModulePass
    {
        static char ID;
    
        SymbolicInserter() : ModulePass(ID) { }
    
        virtual bool runOnModule (Module &M) override
        {
            for (auto &F: M) {
            	if(F.isDeclaration()){
					continue;
				}
            	
            	if(F.getName().str() != InsertFunction){
                    continue;                    
                }
            	

				fprintf(stderr, "\n\33[32mFUNCTION\33[0m %s\n", F.getName().str().c_str());
				DominatorTree DT(F);
				
                int index = 0;
                int inserted = 0;

                int target = std::stoi(InsertIndex);

                std::map<Value*, string> valueNameMap = collect_local_variable_metadata(F);

				for (auto &BB: F) {

				    for (auto &I: BB) {

                        fprintf(stderr, "\n\33[32m%d\33[0m ", index);
                        I.dump();

                        if(index + inserted == target){
                            fprintf(stderr, "\n\33[32mHIT\33[0m \n");
                            //I.dump();
                            int newlyAdded = insert(M, F, I, valueNameMap);
                            inserted += newlyAdded;
                        }
                        index++;
				    }
				}
			}
            //M.dump();
            return true;
        }
        
        void getAnalysisUsage(llvm::AnalysisUsage &Info) const override {
    	}
    };

    char SymbolicInserter::ID = 0;
}


#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"

static RegisterPass<SymbolicInserter> X("symbolic_inserter", "Insert symbolic value pass");

static void register_pass(const PassManagerBuilder &PMB,
    legacy::PassManagerBase &PM)
{
    PM.add(new SymbolicInserter());
}

static RegisterStandardPasses RegisterPass(PassManagerBuilder::EP_LoopOptimizerEnd, register_pass);

