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

using namespace clang;
using namespace clang::driver;
using namespace clang::tooling;
using namespace std;

string OutputStr;
llvm::raw_string_ostream output(OutputStr);
bool hasInsertedVars = false;
bool hasInsertedCFC = false;

static llvm::cl::OptionCategory SVCategory("Symbolic variable inserter");

static llvm::cl::opt<int> fixLoc("fix",
                                 llvm::cl::desc("the line number of fix location"),
                                 llvm::cl::Required, llvm::cl::cat(SVCategory));

static llvm::cl::opt<int> crashLoc("crash",
                                   llvm::cl::desc("the line number of crash location"),
                                   llvm::cl::Required, llvm::cl::cat(SVCategory));

static llvm::cl::opt<string> vars("vars",
                                 llvm::cl::desc("the variables to symbolize"),
                                 llvm::cl::Required, llvm::cl::cat(SVCategory));

static llvm::cl::opt<string> cfc("cfc",
                                  llvm::cl::desc("the crash-free constraints at crash location"),
                                  llvm::cl::Required, llvm::cl::cat(SVCategory));

vector<string> getVars(){
    vector<string> var_vector;
    size_t pos = 0;
    std::string token;
    // TODO: check crash function
    while ((pos = vars.find(" ")) != std::string::npos) {
        token = vars.substr(0, pos);
        var_vector.push_back(token);
        vars.erase(0, pos + 1);
    }
    var_vector.push_back(vars);
    assert (!var_vector.empty());
    return var_vector;
}

class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor> {
public:
    MyASTVisitor(Rewriter &R, CompilerInstance &C) : TheRewriter(R), Compiler(C) {}

    bool VisitStmt(Stmt *s) {

        FullSourceLoc FullLocation = Compiler.getASTContext().getFullLoc(s->getLocStart());
        int curLineNo = FullLocation.getLineNumber();

        bool isInsertPoint = false;
        string varToInsert;
        if (!hasInsertedVars && fixLoc == curLineNo){
            hasInsertedVars = true;
            isInsertPoint = true;
            vector<string> var_vector = getVars();
            for (const string &var: var_vector)
                varToInsert += "klee_make_symbolic(&" + var + ", sizeof(" + var + "), \"" + var + "\");";
        } else if (!hasInsertedCFC && crashLoc == curLineNo){
            isInsertPoint = true;
            hasInsertedCFC = true;
            varToInsert = "klee_assume(" + cfc + ");";
        }

        if (isInsertPoint){
            SourceManager &SM = Compiler.getSourceManager();
            LangOptions &OPT = Compiler.getLangOpts();
            SourceLocation startPoint = s->getLocStart();
            const string oriStm = Lexer::getSourceText(CharSourceRange::getTokenRange(s->getSourceRange()), SM, OPT);
            if (isa<Expr>(s)){
                string newStmt = "({" + varToInsert+oriStm + ";})";
                TheRewriter.ReplaceText(startPoint, u_int(oriStm.length()), newStmt);
            }
            else if (isa<Stmt>(s)){
                string newStmt = varToInsert + oriStm;
                TheRewriter.ReplaceText(startPoint, u_int(oriStm.length()), newStmt);
            }
        }

        if (hasInsertedVars && hasInsertedCFC)
            return false;

        return true;
    }


private:
    Rewriter &TheRewriter;
    CompilerInstance &Compiler;
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

        // Now emit the rewritten buffer.
        TheRewriter.getEditBuffer(SM.getMainFileID()).write(output);
    }

    std::unique_ptr<ASTConsumer> CreateASTConsumer(CompilerInstance &CI,
                                                   StringRef file) override {
        // llvm::errs() << "** Creating AST consumer for: " << file << "\n";
        TheRewriter.setSourceMgr(CI.getSourceManager(), CI.getLangOpts());
        return llvm::make_unique<MyASTConsumer>(TheRewriter, CI);
    }

private:
    Rewriter TheRewriter;
};

int main(int argc, const char **argv) {
    CommonOptionsParser op(argc, argv, SVCategory);
    ClangTool Tool(op.getCompilations(), op.getSourcePathList());

    int ret = Tool.run(newFrontendActionFactory<MyFrontendAction>().get());

    if (ret==0){
        // write to file
        if(output.str().length() != 0){
            string fileName = op.getSourcePathList()[0];
            ofstream srcFile;
            srcFile.open(fileName);
            srcFile << "#include<klee/klee.h>\n" << output.str();
            srcFile.close();
        }
    }

    return ret;
}
