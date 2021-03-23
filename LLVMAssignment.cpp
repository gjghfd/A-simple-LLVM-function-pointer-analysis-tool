//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include <llvm/Support/CommandLine.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Support/ToolOutputFile.h>

#include <llvm/Transforms/Scalar.h>
#include <llvm/Transforms/Utils.h>

#include <llvm/IR/Function.h>
#include <llvm/Pass.h>
#include <llvm/Support/raw_ostream.h>

#include <llvm/Bitcode/BitcodeReader.h>
#include <llvm/Bitcode/BitcodeWriter.h>

//head files added:
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/DebugInfoMetadata.h>
#include <llvm/IR/CFG.h>

#include <llvm/ADT/SmallSet.h>
using namespace llvm;
static ManagedStatic<LLVMContext> GlobalContext;
static LLVMContext &getGlobalContext() { return *GlobalContext; }
/* In LLVM 5.0, when  -O0 passed to clang , the functions generated with clang will
 * have optnone attribute which would lead to some transform passes disabled, like mem2reg.
 */
struct EnableFunctionOptPass: public FunctionPass {
    static char ID;
    EnableFunctionOptPass():FunctionPass(ID){}
    bool runOnFunction(Function & F) override{
        if(F.hasFnAttribute(Attribute::OptimizeNone))
        {
            F.removeFnAttr(Attribute::OptimizeNone);
        }
        return true;
    }
};

char EnableFunctionOptPass::ID=0;


///!TODO TO BE COMPLETED BY YOU FOR ASSIGNMENT 2
///Updated 11/10/2017 by fargo: make all functions
///processed by mem2reg before this pass.

static void PrintName(Function *F) {          //print name for a specific function
  MDNode *mdn = F->getMetadata("dbg");
  DISubprogram *sbp = dyn_cast<DISubprogram>(mdn);
  errs() << sbp->getName();
}

static SmallSet<Function *, 32> S;
static std::map<Function *, unsigned> Map;      //if a function returns function ptr, calculate which operand it will return
static CallInst *CI;

static void PrintAllFunctions(Value *V, Function *Fc, bool fl) {    //print all functions that might be called, fl=1 means that we need to determine the callinst's args
  if (Function *FF = dyn_cast<Function>(V)) S.insert(FF);					//a function
  else if (CallInst *callinst = dyn_cast<CallInst>(V)) {         //a call instruction
    if (Function *CF = callinst->getCalledFunction()) {
      if (CF->getReturnType()->isPointerTy()) {
        PrintAllFunctions(callinst->getArgOperand(Map[CF]), Fc, fl);
      }
    }
    else if (!fl) CI = callinst, PrintAllFunctions(callinst->getCalledOperand(), Fc, 1);
  }
  else if (PHINode *I = dyn_cast<PHINode>(V)) {     //a phi instruction
    BasicBlock *BB = I->getParent();
    for (BasicBlock *prev : predecessors(BB)) {
      Value *V_ = V->DoPHITranslation(BB, prev);
      if (!V_->hasName()) continue;				//remove NULL ptr
      if (Function *F = dyn_cast<Function>(V_)) {
        if (!fl) S.insert(F);
        else if (F->getReturnType()->isPointerTy()) {
          Value *Ope = CI->getArgOperand(Map[F]);
          if (Function *FF = dyn_cast<Function>(Ope)) S.insert(FF);
          else if (PHINode *phi = dyn_cast<PHINode>(Ope)){      //do phi translation
            Value *Ope_ = Ope->DoPHITranslation(BB, prev);
            if (Function *FF = dyn_cast<Function>(Ope)) S.insert(FF);
          }
        }
      } else PrintAllFunctions(V_, Fc, fl);
    }
  } else {   //is an argument of function it belongs to
    unsigned num = 0;
    for (Function::arg_iterator A = Fc->arg_begin(), E = Fc->arg_end(); A != E; A++, num++) {
      if (&*A == V) {
        for (Value::use_iterator U = Fc->use_begin(), E = Fc->use_end(); U != E; U++) {
          Value *I = U->getUser();
          if (CallInst *callinst = dyn_cast<CallInst>(I))
            PrintAllFunctions(callinst->getArgOperand(num), callinst->getFunction(), fl);
        }
      }
    }
  }
}

struct FuncPtrPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  FuncPtrPass() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {
    errs() << "Hello: ";
    errs().write_escaped(M.getName()) << '\n';
    M.dump();
    errs()<<"------------------------------\n";

    for (Function &F : M)       //if a function returns function ptr, first calculate which arg it will return
      if (F.getReturnType()->isPointerTy()) {
        for (BasicBlock &B : F)
          for (Instruction &I : B)
            if (ReturnInst *ret = dyn_cast<ReturnInst>(&I)) {
              Value *V = ret->getReturnValue();
              int num = 0;
              for (Function::arg_iterator A = F.arg_begin(), E = F.arg_end(); A != E; A++, num++)
                if (&*A == V) {Map[&F] = num; break;}
            }
      }

    for (Function &F : M)       //work part
      for (BasicBlock &B : F) 
        for (Instruction &I : B) {
          if (isa<DbgInfoIntrinsic>((const Instruction *) &I)) continue;
          if (CallInst *callinst = dyn_cast<CallInst>(&I)) {
            MDNode *mdn = callinst->getMetadata("dbg");
            DILocation *loc = dyn_cast<DILocation>(mdn);
            errs() << loc->getLine() << " : ";

            if (Function *F_ = callinst->getCalledFunction()) {
              PrintName(F_);
            } else {
              Value *V = callinst->getCalledOperand();
              //V->dump();
              S.clear();
              PrintAllFunctions(V, &F, 0);
              bool fl = 1;
              for (auto I : S) {
                if (fl) {
                  if ((int) S.size() == 1) callinst->setCalledFunction(I);
                  fl = 0;
                } else errs() << ", ";
                PrintName(I);
              }
            }
            errs() << '\n';
          }
        }
    return false;
  }
};


char FuncPtrPass::ID = 0;
static RegisterPass<FuncPtrPass> X("funcptrpass", "Print function call instruction");

static cl::opt<std::string>
InputFilename(cl::Positional,
              cl::desc("<filename>.bc"),
              cl::init(""));


int main(int argc, char **argv) {
   LLVMContext &Context = getGlobalContext();
   SMDiagnostic Err;
   // Parse the command line to read the Inputfilename
   cl::ParseCommandLineOptions(argc, argv,
                              "FuncPtrPass \n My first LLVM too which does not do much.\n");


   // Load the input module
   std::unique_ptr<Module> M = parseIRFile(InputFilename, Err, Context);
   if (!M) {
      Err.print(argv[0], errs());
      return 1;
   }

   llvm::legacy::PassManager Passes;
   
   ///Remove functions' optnone attribute in LLVM5.0
   Passes.add(new EnableFunctionOptPass());
   ///Transform it to SSA
   Passes.add(llvm::createPromoteMemoryToRegisterPass());

   /// Your pass to print Function and Call Instructions
   Passes.add(new FuncPtrPass());
   Passes.run(*M.get());
}

