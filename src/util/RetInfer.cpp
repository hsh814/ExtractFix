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
#include <vector>

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
#include "clang/AST/Expr.h"

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;

string OutputStr;
llvm::raw_string_ostream output(OutputStr);

static llvm::cl::OptionCategory RETCategory("Infer the return type of a function");

static llvm::cl::opt<string> func_name("fun_name",
                                     llvm::cl::desc("the name of the function"),
                                     llvm::cl::Required, llvm::cl::cat(RETCategory));

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
    MyASTVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C), CurrFunc(nullptr) {}

    bool VisitStmt(Stmt *s) {
        FullSourceLoc FullLocation = Compiler.getASTContext().getFullLoc(s->getLocStart());
        if (isa<ReturnStmt>(s)){
            llvm::errs() << "hit return statement\n";
            auto* retStmt = dyn_cast<ReturnStmt>(s);
            Expr * retValue = retStmt->getRetValue();
            SourceLocation sl = retValue->getSourceRange().getBegin();
            if(retValue->isIntegerConstantExpr(Compiler.getASTContext(), &sl) ||
                retValue->isNullPointerConstant(Compiler.getASTContext(), Expr::NPC_ValueDependentIsNull)){
                SourceManager &SM = Compiler.getSourceManager();
                LangOptions &OPT = Compiler.getLangOpts();
                const string oriStm = Lexer::getSourceText(CharSourceRange::getTokenRange(retValue->getSourceRange()),
                        SM, OPT);
                llvm::outs() << "constant: " << oriStm << "\n";
            }
        }

        return true;
    }

    bool VisitFunctionDecl(FunctionDecl *f) {
        if (f->getName() != func_name)
            return false;
        SourceManager &SM = Compiler.getSourceManager();
        LangOptions &OPT = Compiler.getLangOpts();
        const string retType = Lexer::getSourceText(CharSourceRange::getTokenRange(f->getReturnTypeSourceRange()),
                                                   SM, OPT);
        llvm::outs() << "retType: " << retType << "\n";
        return true;
    }


private:
    Rewriter &TheRewriter;
    CompilerInstance &Compiler;
    FunctionDecl* CurrFunc;
};

// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer {
public:
    MyASTConsumer(Rewriter &R, CompilerInstance &Compiler) : Visitor(R, Compiler) {}
    // Override the method that gets called for each parsed top-level
    // declaration.
    bool HandleTopLevelDecl(DeclGroupRef DR) override {
        for (DeclGroupRef::iterator b = DR.begin(), e = DR.end(); b != e; ++b) {
            // Traverse the declaration using our AST visitor.
            Visitor.TraverseDecl(*b);
            (*b)->dump();
        }
        return true;
    }

private:
    MyASTVisitor Visitor;
};

// For each source file provided to the tool, a new FrontendAction is created.
class MyFrontendAction : public ASTFrontendAction {
public:
    MyFrontendAction() {}
    void EndSourceFileAction() override {
        SourceManager &SM = TheRewriter.getSourceMgr();
        llvm::errs() << "** EndSourceFileAction for: "
                     << SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";

        TheRewriter.getEditBuffer(SM.getMainFileID()).write(output);
    }

    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                   StringRef file) override {
        TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
        return llvm::make_unique<MyASTConsumer>(TheRewriter, CI);
    }

private:
    Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
    CommonOptionsParser op(argc, argv, RETCategory);
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());

    int ret = Tool.run(newFrontendActionFactory<MyFrontendAction>().get());
    /*if (ret==0){
        // write to file
        if(output.str().length() != 0){
            string fileName = op.getSourcePathList()[0];
            ofstream srcFile;
            srcFile.open(fileName);
            srcFile << output.str();
            srcFile.close();
        }
    }*/

    return 0;
}

