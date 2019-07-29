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

#include <sstream>
#include <string>
#include <fstream>
#include <assert.h>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTConsumers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/ASTContext.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;

#define OPT_RS "replace-size"
#define OPT_DS "declare-size"
#define OPT_RF "replace-flib"


static llvm::cl::OptionCategory PreprocessorCategory("Target Project Preprocessor");

static llvm::cl::opt<string> MissionType("mission",
                                                llvm::cl::desc("Mission type:\n"
                                                               "\t-replace-size : replace malloc size with global variable\n"
                                                               "\t-declare-size : declare the replaced global variable\n"
                                                               "\t-replace-flib : replace the float libc usages"),
                                                llvm::cl::Required, llvm::cl::cat(PreprocessorCategory));

static llvm::cl::opt<string> CalleeOutFile("callee-out",
                                              llvm::cl::desc("the file to record callees of malloc"),
                                              llvm::cl::Optional, llvm::cl::cat(PreprocessorCategory));

static const string GL_PREFIX = "LOWFAT_GLOBAL_MS_";

ofstream CalleeOFS;
vector<string> CalleeFileLines;
string OutputStr;
llvm::raw_string_ostream OS(OutputStr);

static const FunctionDecl* getParentFuncDecl(ASTContext &Context, const Decl *d);

//TODO: change to template
static const FunctionDecl* getParentFuncDecl(ASTContext &Context, const Stmt *s){
    const Stmt& currentStmt = *s;

    const auto& parents  = Context.getParents(currentStmt);
    auto it = Context.getParents(currentStmt).begin();
    if(it == Context.getParents(currentStmt).end()){
        llvm::errs()<< "parents not found\n";
        s->dump();
        return nullptr;
    }

    if (!parents.empty()){
        if(const Decl* parentDecl =  parents[0].get<Decl>()){
            if(isa<FunctionDecl>(parentDecl)){
                return cast<FunctionDecl>(parentDecl);
            } else {
                return getParentFuncDecl(Context, parentDecl);
            }
        } else if (const Stmt* parentStmt =  parents[0].get<Stmt>()){
            return getParentFuncDecl(Context, parentStmt);
        } else {
            llvm::errs()<< "parents not found\n";
            s->dump();
            return nullptr;
        }
    }
}

static const FunctionDecl* getParentFuncDecl(ASTContext &Context, const Decl *d){
    const Decl& currentDecl = *d;

    const auto& parents  = Context.getParents(currentDecl);
    auto it = Context.getParents(currentDecl).begin();
    if(it == Context.getParents(currentDecl).end()){
        llvm::errs()<< "parents not found\n";
        d->dump();
        return nullptr;
    }

    if (!parents.empty()){
        if(const Decl* parentDecl =  parents[0].get<Decl>()){
            if(isa<FunctionDecl>(parentDecl)){
                return cast<FunctionDecl>(parentDecl);
            } else {
                getParentFuncDecl(Context, parentDecl);
            }

        } else if (const Stmt* parentStmt =  parents[0].get<Stmt>()){
            return getParentFuncDecl(Context, parentStmt);
        } else {
            llvm::errs()<< "parents not found\n";
            d->dump();
            return nullptr;
        }
    }
}

class LibReplaceVisitor : public RecursiveASTVisitor<LibReplaceVisitor> {
private:
    Rewriter &TheRewriter;
    CompilerInstance &Compiler;
    map<string, string> Libs;
    map<string, string> Func2Signature;
    bool FuncDeclInserted = false;

public:
    LibReplaceVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C) {
        Libs["fabs"] = "fabs_fk";
        Func2Signature["fabs"] = "double fabs_fk(double x){return x>0? x: -x;}";
    }

    bool VisitExpr(Expr *e){

        if (isa<CallExpr>(e)) {
            CallExpr *call = cast<CallExpr>(e);

            if(call->getDirectCallee()){
                string callee = call->getDirectCallee()->getName().str();
                if(Libs.find(callee) != Libs.end()){
                    string target = Libs[callee];
                    TheRewriter.ReplaceText(call->getLocStart(), callee.length(), target);

                    FullSourceLoc FullLocation = Compiler.getASTContext().getFullLoc(call->getLocStart());

                    llvm::errs()<<"Replace "<<FullLocation.getFileEntry()->getName()<<" # "<<
                                FullLocation.getLineNumber()<<" "<<callee<<" ==>> "<<target<<"\n";

                    if(!FuncDeclInserted){
                        const FunctionDecl* currFunc = getParentFuncDecl(Compiler.getASTContext(), call);
                        if(!currFunc) {
                            call->dump();
                            llvm::errs()<<"ERROR: NULL PARENT FUNCTION!!!\n";
                            return true;
                        }

                        string declStmt = "/*LOWFAT_D*/" + Func2Signature[callee] + "\n";
                        TheRewriter.InsertText(currFunc->getLocStart(), declStmt, true, true);
                        FuncDeclInserted = true;
                    }

                }
            }
        }

        return true;
    }

    bool VisitFunctionDecl(FunctionDecl *f) {
        if (!(f->hasBody()) || f->isInlined()) {
            return false;
        }
        //f->dump();
        return true;
    }
};


class GSDeclVisitor : public RecursiveASTVisitor<GSDeclVisitor> {
private:
    Rewriter &TheRewriter;
    CompilerInstance &Compiler;
    map<string, vector<string>> Func2Global;
    map<string, string> Func2InsertedCaller;
public:
    GSDeclVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C)
    {

        ifstream calleeFile(CalleeOutFile);
        if (calleeFile.is_open())
        {
            string line;
            while (getline (calleeFile, line))
            {
                int idx = line.find(' ');
                assert(idx > 0);
                string fileName = line.substr(0, idx);
                string remaining = line.substr(idx + 1);

                idx = remaining.find(' ');
                assert(idx > 0);

                string mtd = remaining.substr(0, idx);
                string gv = remaining.substr(idx + 1);

                if(Func2Global.find(mtd) == Func2Global.end())
                    Func2Global[mtd] = vector<string>();


                Func2Global[mtd].push_back(gv);

                llvm::errs()<<mtd<<" ----->>>>> " << gv <<" @ "<<fileName<<"\n";
            }
            calleeFile.close();
        }
        //llvm::errs()<<Func2Global["xmalloc"]<<"  \n";
    }

    bool VisitExpr(Expr *e)
    {
        if (isa<CallExpr>(e))
        {
            CallExpr *call = cast<CallExpr>(e);

            if(call->getDirectCallee())
            {

                SourceManager &SM = Compiler.getSourceManager();

                if(SM.getFileID(call->getDirectCallee()->getLocStart()) == SM.getFileID(call->getLocStart())){
                    // if the callee and the current call are in the same file, it is no need to insert decl
                    return true;
                }

                // the function to be called
                string callee = call->getDirectCallee()->getName().str();

                // the function to be called contains malloc
                // and the called function has not been inserted yet
                if (Func2Global.count(callee) > 0)
                {

                    const FunctionDecl* currFunc = getParentFuncDecl(Compiler.getASTContext(), call);

                    if(!currFunc)
                    {
                        call->dump();
                        llvm::errs()<<"ERROR: NULL PARENT FUNCTION!!!\n";
                        return true;
                    }

                    string funcName = currFunc->getName().str();

                    if(Func2InsertedCaller.find(funcName) == Func2InsertedCaller.end())
                    {
                        for(string globalName : Func2Global[callee])
                        {

                            string declStmt = "/*M_SIZE_G*/ extern size_t " + globalName + ";\n";
                            TheRewriter.InsertText(currFunc->getLocStart(), declStmt, true, true);

                            Func2InsertedCaller[funcName] = callee;

                            string oriFileName(Compiler.getSourceManager().getFileEntryForID(Compiler.getSourceManager().getMainFileID())->getName().str());
                            llvm::errs()<<">>>>>>>> "<<oriFileName<<" @ "<<funcName<<"()  EXTERN: "<<globalName<<"\n";
                        }
                    }

                }
            }

        }
        return true;
    }

    bool VisitFunctionDecl(FunctionDecl *f)
    {
        if (!(f->hasBody()) || f->isInlined())
            return false;

        //f->dump();
        return true;
    }
};


class GSReplaceVisitor : public RecursiveASTVisitor<GSReplaceVisitor> {

private:
    Rewriter &TheRewriter;
    CompilerInstance &Compiler;

public:
    GSReplaceVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C) {}

    /**
     *  For malloc(s), change to malloc(({GV = s; GV}))
     *  For realloc(ptr, s), change to realloc(ptr, ({GV = s; GV}))
     *  For calloc(n, s), change to calloc(1, ({GV = n * s; GV}))
     *
     * */
    bool VisitExpr(Expr *e)
    {
        if (isa<CallExpr>(e)) {
            CallExpr *call = cast<CallExpr>(e);
            //call->dump();

            FunctionDecl* callee = call->getDirectCallee();
            if(!callee)
                return true;

            if(callee->getName() == "malloc" || callee->getName() == "realloc" || callee->getName() == "calloc")
            {
                SourceManager &SM = Compiler.getSourceManager();
                LangOptions &OPT = Compiler.getLangOpts();

                Expr* size;
                if(callee->getName() == "malloc")
                    size = call->getArg(0);
                else
                    size = call->getArg(1);

                const string oriSize = Lexer::getSourceText(CharSourceRange::getTokenRange(size->getSourceRange()), SM, OPT);

                const FunctionDecl* currFunc = getParentFuncDecl(Compiler.getASTContext(), call);
                if(!currFunc) {
                    call->dump();
                    llvm::errs()<<"ERROR: NULL PARENT FUNCTION!!!\n";
                    return true;
                }

                //currFunc->dump();
                string oriFileName(SM.getFileEntryForID(SM.getMainFileID())->getName().str());
                string fileName = SM.getFileEntryForID(SM.getMainFileID())->getName().str();
                int idx = fileName.rfind("/");
                if(idx > 0) {
                    fileName = fileName.substr(idx + 1);
                }
                idx = fileName.find(".");
                if(idx > 0) {
                    fileName = fileName.substr(0, idx);
                }
                replace(fileName.begin(), fileName.end(), '-', '_');

                FullSourceLoc FullLocation = Compiler.getASTContext().getFullLoc(call->getLocStart());

                string funcName = currFunc->getName().str();

                string globalName = GL_PREFIX + "_" + fileName + "_" + funcName + "_" +
                        std::to_string(FullLocation.getSpellingLineNumber());

                string newArg;
                if (callee->getName() != "calloc")
                    newArg = "( /*LOWFAT_GS*/ {" + globalName + " = " + oriSize + "; " + globalName + ";} )";
                else {
                    Expr* nmemb = call->getArg(0);
                    const string oriN = Lexer::getSourceText(CharSourceRange::getTokenRange(nmemb->getSourceRange()), SM, OPT);
                    newArg = "( /*LOWFAT_GS*/ {" + globalName + " = " + oriN + " * " + oriSize + "; " + globalName + ";} )";
                }

                llvm::errs()<<">>>>>>>> "<<oriFileName<<" @ "<<funcName<<"()\n";
                if (callee->getName() == "malloc")
                    llvm::errs()<<"\tMALLOC ARG : "<<oriSize<<" -->> "<<newArg<<"\n";
                else if (callee->getName() == "realloc")
                    llvm::errs()<<"\tREALLOC ARG: "<<oriSize<<" -->> "<<newArg<<"\n";
                else
                    llvm::errs()<<"\tCALLOC ARG : "<<oriSize<<" -->> "<<newArg<<"\n";
                
                //size->dump();
                llvm::errs()<<" "<<oriSize.length()<<" "<<newArg<<"\n";

                // repalce calloc(n, s) to calloc(1, s)
                if(callee->getName() == "calloc"){
                    Expr* nmemb = call->getArg(0);
                    const string oriN = Lexer::getSourceText(CharSourceRange::getTokenRange(nmemb->getSourceRange()), SM, OPT);

                    SourceLocation nmembStart = nmemb->getLocStart();
                    if(nmembStart.isMacroID() ) {
                        std::pair< SourceLocation, SourceLocation > expansionRange = TheRewriter.getSourceMgr().getImmediateExpansionRange(nmembStart);
                        nmembStart = expansionRange.first;
                    }
                    TheRewriter.ReplaceText(nmembStart, oriN.length(), "1"); // oriSize.length()
                }

                SourceLocation sizeStart = size->getLocStart();
                if(sizeStart.isMacroID() ) {
                    std::pair< SourceLocation, SourceLocation > expansionRange = TheRewriter.getSourceMgr().getImmediateExpansionRange(sizeStart);
                    sizeStart = expansionRange.first;
                }

                TheRewriter.ReplaceText(sizeStart, oriSize.length(), newArg); // oriSize.length()


                string declStmt = "/*LOWFAT_GS*/ size_t " + globalName + ";\n";
                TheRewriter.InsertText(currFunc->getLocStart(), declStmt, true, true);

                if(funcName != "main"){
                    string calleeLine = oriFileName + " " + funcName + " " + globalName + "\n";
                    llvm::errs()<<"ADDING INTO CALLEE FILE: "<<calleeLine;
                    CalleeFileLines.push_back(calleeLine);
                }
            }

        }

        return true;
    }

    bool VisitFunctionDecl(FunctionDecl *f)
    {
        if (!(f->hasBody()) || f->isInlined())
            return false;

        return true;
    }
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class PreprocessASTConsumer : public ASTConsumer {
public:
    PreprocessASTConsumer(Rewriter &R, CompilerInstance &Compiler) {

      if(MissionType == OPT_RS ){
          ReplaceVisitor = new GSReplaceVisitor(R, Compiler);
      } else if (MissionType == OPT_RF) {
          LibVisitor = new LibReplaceVisitor(R, Compiler);
      } else if (MissionType == OPT_DS){
          DeclVisitor = new GSDeclVisitor(R, Compiler);
      } else {
          llvm::errs()<<"ERROR MISSION TYPE\n";
          abort();
      }
    }

    // Override the method that gets called for each parsed top-level
    // declaration.
    bool HandleTopLevelDecl(DeclGroupRef DR) override {

        for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
            if(MissionType == OPT_RS){
                ReplaceVisitor->TraverseDecl(*b);
            } else if (MissionType == OPT_RF){
                LibVisitor->TraverseDecl(*b);
            } else if (MissionType == OPT_DS){
                DeclVisitor->TraverseDecl(*b);
            } else {
                llvm::errs()<<"ERROR MISSION TYPE: "<<MissionType<<"\n";
                abort();
            }
            //(*b)->dump();
        }

        return true;
    }

private:
    GSReplaceVisitor* ReplaceVisitor;
    GSDeclVisitor* DeclVisitor;
    LibReplaceVisitor* LibVisitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class PreprocessFrontendAction : public ASTFrontendAction {
public:
    PreprocessFrontendAction() {}
    void EndSourceFileAction() override {
        SourceManager &SM = TheRewriter.getSourceMgr();

        string fileName = SM.getFileEntryForID(SM.getMainFileID())->getName().str();
        llvm::errs() << "** EndSourceFileAction for: "<<fileName<<"\n";

        // Now emit the rewritten buffer.

        TheRewriter.getEditBuffer(SM.getMainFileID()).write(OS); //llvm::outs()
    }


    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                 StringRef file) override {

        llvm::errs() << "** Creating AST consumer for: " << file << "\n";
        TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
        return std::unique_ptr<clang::ASTConsumer>(new PreprocessASTConsumer(TheRewriter, CI));
    }

private:
    Rewriter TheRewriter;
};


static bool processOptionsSucc(){
    bool succ = true;
    if (MissionType.length()) {
        llvm::errs()<< "Current Mission: "<<MissionType<< "\n";
        if (MissionType == OPT_RS || MissionType == OPT_DS){

            if(CalleeOutFile.length()){
                if(MissionType == OPT_RS) {
                    CalleeOFS.open(CalleeOutFile, std::ios_base::app);
                }
            } else {
                llvm::errs() << "Empty CalleeOutFile.\n";
                succ = false;
            }
        } else if(MissionType != OPT_RF){
            llvm::errs() << "Error MissionType"<<MissionType<<"\n";
            succ = false;
        }
    } else {
        llvm::errs() << "Empty MissionType"<<MissionType<<"\n";
        succ = false;
    }
    return succ;
}

/**
 *  Usage example:
 *  ./GSInserter -mission=replace-size -callee-out="callee.txt"  /home/nightwish/workspace/subjects/crash_free/coreutils_ig/coreutils/lib/xmalloc.c -- -I/home/nightwish/workspace/subjects/crash_free/coreutils_ig/coreutils/src -I/home/nightwish/workspace/subjects/crash_free/coreutils_ig/coreutils/lib -I/usr/local/lib/clang/6.0.1/include
 *  ./GSInserter -mission=declare-size -callee-out="callee.txt"  /home/nightwish/workspace/subjects/crash_free/coreutils_ig/coreutils/src/pwd.c -- -I/home/nightwish/workspace/subjects/crash_free/coreutils_ig/coreutils/src -I/home/nightwish/workspace/subjects/crash_free/coreutils_ig/coreutils/lib -I/usr/local/lib/clang/6.0.1/include
 */
int main(int argc, const char **argv) {
    CommonOptionsParser op(argc, argv, PreprocessorCategory);

    // only process single file
    assert(op.getSourcePathList().size() == 1);

    ClangTool Tool(op.getCompilations(), op.getSourcePathList());

    if(!processOptionsSucc()){
        return 0;
    }

    int ret = Tool.run(newFrontendActionFactory<PreprocessFrontendAction>().get());
    if(ret == 0){
        for(string line : CalleeFileLines){
            CalleeOFS<<line;
        }
        CalleeOFS.close();

        // write to file
        if(OS.str().length() != 0){
            string fileName = op.getSourcePathList()[0];
            ofstream srcFile;
            srcFile.open(fileName);
            srcFile<<OS.str();
            srcFile.close();
        }
    }

    return ret;
}
