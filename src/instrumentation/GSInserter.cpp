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

ofstream CalleeOFS;

static llvm::cl::OptionCategory PreprocessorCategory("Target Project Preprocessor");

static llvm::cl::opt<string> MissionType("mission",
                                                llvm::cl::desc("Mission type:\n"
                                                               "\t-replace-size : replace malloc size with global variable\n"
                                                               "\t-declare-size : declare the replaced global variable\n"
                                                               "\t-replace-flib : replace the float libc usages"),
                                                llvm::cl::Required, llvm::cl::cat(PreprocessorCategory));

static llvm::cl::opt<string> CalleeOutFile("callee-out",
                                              llvm::cl::desc("the file to record callees of malloc"),
                                              llvm::cl::Required, llvm::cl::cat(PreprocessorCategory));

static const string GL_PREFIX = "LOWFAT_GLOBAL_MS_";


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
public:
    LibReplaceVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C) {}


};

class GSDeclVisitor : public RecursiveASTVisitor<GSDeclVisitor> {
private:
    Rewriter &TheRewriter;
    CompilerInstance &Compiler;
    map<string, vector<string>> Func2Global;
    map<string, string> Func2InsertedCaller;

public:
    GSDeclVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C) {

        ifstream calleeFile(CalleeOutFile);
        if (calleeFile.is_open()) {
            string line;
            while (getline (calleeFile, line)) {
                int idx = line.find(' ');
                assert(idx > 0);
                string mtd = line.substr(0, idx);
                string gv = line.substr(idx + 1);

                if(Func2Global.find(mtd) == Func2Global.end()){
                    Func2Global[mtd] = vector<string>();
                }

                Func2Global[mtd].push_back(gv);

                //llvm::errs()<<mtd<<" ----->>>>> " << gv <<"\n";
            }
            calleeFile.close();
        }
        //llvm::errs()<<Func2Global["xmalloc"]<<"  \n";
    }

    bool VisitExpr(Expr *e){
        if (isa<CallExpr>(e)) {
            CallExpr *call = cast<CallExpr>(e);

            if(call->getDirectCallee()){

                // the function to be called
                string callee = call->getDirectCallee()->getName().str();

                // the function to be called contains malloc
                // and the called function has not been inserted yet
                if (Func2Global.count(callee) > 0) {

                    const FunctionDecl* currFunc = getParentFuncDecl(Compiler.getASTContext(), call);

                    string funcName = currFunc->getName().str();

                    if(Func2InsertedCaller.find(funcName) == Func2InsertedCaller.end()){

                        for(string globalName : Func2Global[callee]){

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

    bool VisitFunctionDecl(FunctionDecl *f) {
        if (!f->hasBody() || f->isInlined()) {
            return false;
        }
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

        bool VisitExpr(Expr *e){
        if (isa<CallExpr>(e)) {
            CallExpr *call = cast<CallExpr>(e);

            if(call->getDirectCallee()){
                if(call->getDirectCallee()->getName() == "malloc"){

                    SourceManager &SM = Compiler.getSourceManager();
                    LangOptions &OPT = Compiler.getLangOpts();

                    Expr* size = call->getArg(0);

                    const string oriSize = Lexer::getSourceText(CharSourceRange::getTokenRange(size->getSourceRange()), SM, OPT);

                    const FunctionDecl* currFunc = getParentFuncDecl(Compiler.getASTContext(), call);

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

                    string newArg = "( /*LOWFAT_GS*/ {" + globalName + " = " + oriSize + "; " + oriSize + ";} )";

                    llvm::errs()<<">>>>>>>> "<<oriFileName<<" @ "<<funcName<<"()  MALLOC ARG: "<<oriSize<<"\n";

                    TheRewriter.ReplaceText(size->getLocStart(), oriSize.length(), newArg);

                    string declStmt = "/*M_SIZE_G*/ size_t " + globalName + ";\n";
                    TheRewriter.InsertText(currFunc->getLocStart(), declStmt, true, true);

                    if(funcName != "main"){
                        CalleeOFS<<funcName<<" "<<globalName<<"\n";
                    }
                }
            }
        }

        return true;
    }

    bool VisitFunctionDecl(FunctionDecl *f) {
        if (!f->hasBody() || f->isInlined()) {
            return false;
        }
        return true;
    }
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class PreprocessASTConsumer : public ASTConsumer {
public:
    PreprocessASTConsumer(Rewriter &R, CompilerInstance &Compiler) {

      if(MissionType == "replace-size" || MissionType == "replace-flib"){
          ReplaceVisitor = new GSReplaceVisitor(R, Compiler);
      } else {
          DeclVisitor = new GSDeclVisitor(R, Compiler);
      }

    }

    // Override the method that gets called for each parsed top-level
    // declaration.
    bool HandleTopLevelDecl(DeclGroupRef DR) override {
    for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {

        if(MissionType == "replace-size" || MissionType == "replace-flib"){
            ReplaceVisitor->TraverseDecl(*b);
        } else {
            DeclVisitor->TraverseDecl(*b);
        }
        //(*b)->dump();
    }
    return true;
    }

private:
    GSReplaceVisitor* ReplaceVisitor;
    GSDeclVisitor* DeclVisitor;
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
    std::error_code EC;
    llvm::raw_fd_ostream OS(fileName, EC, llvm::sys::fs::F_None);

    TheRewriter.getEditBuffer(SM.getMainFileID()).write(OS);
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
        if (MissionType == "replace-size" || MissionType == "declare-size"){

            if(CalleeOutFile.length()){
                if(MissionType == "replace-size") {
                    CalleeOFS.open(CalleeOutFile, std::ios_base::app);
                }
            } else {
                llvm::errs() << "Empty CalleeOutFile.\n";
                succ = false;
            }
        } else if(MissionType != "replace-flib"){
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
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());

    if(!processOptionsSucc()){
        return 0;
    }

    return Tool.run(newFrontendActionFactory<PreprocessFrontendAction>().get());
}
