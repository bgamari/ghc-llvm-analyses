// Originally based on PyAliasAnalysis from the unladen-swallow project!
#include "llvm/ADT/APInt.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/Passes.h"
#include "llvm/IR/CallingConv.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/ConstantRange.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include <set>

#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
  // This AliasAnalysis pass captures GHC-specific knowledge about aliasing:
  //
  //  For functions using the GHC calling convention, we know that the second
  //  argument (%Sp_Arg) doesn't alias any pointers.  This is important because
  //  arguments are passed on the stack, and it *really* pessimises things if
  //  writes to e.g. arrays prevent us from forwarding earlier loads from the
  //  stack to later ones.
  class GHCAliasAnalysis : public FunctionPass, public AliasAnalysis {
  public:
      static char ID;
      GHCAliasAnalysis() : FunctionPass(ID) { }
  
  private:
      ScalarEvolution *scev_;
      const Argument *sp_arg_;
  
      virtual void getAnalysisUsage(AnalysisUsage &usage) const {
          AliasAnalysis::getAnalysisUsage(usage);
          // Used to canonicalize a value into an underlying
          // pointer and an offset, if possible.
          usage.addRequiredTransitive<ScalarEvolution>();
          usage.setPreservesAll();
      }
  
      virtual bool runOnFunction(Function&);
  
      virtual AliasResult alias(const Location &L1, const Location &L2);
      
      virtual void *getAdjustedAnalysisPointer(const void *PI) {
          if (PI == &AliasAnalysis::ID)
              return (AliasAnalysis*)this;
          return this;
      }
  };
}  // End of anonymous namespace
  
// The address of this variable identifies the pass
char GHCAliasAnalysis::ID = 0;

// Ensure our pass can be used from "opt"
static RegisterPass<GHCAliasAnalysis> P("ghc-aa", "GHC-specific Alias Analysis");
static RegisterAnalysisGroup<AliasAnalysis> G(P);

bool
SomeOperandIsSPPointer(std::set<const Value*> &SpPointers, const Instruction *I) {
  for (User::const_op_iterator OI = I->op_begin(), OE = I->op_end(); OI != OE; ++OI) {
    if (SpPointers.find(OI->get()) != SpPointers.end()) {
      return true;
    }
  }
  return false;
}

bool
SPEscapes(Function &F, const Argument *sp_arg) {
  // We monotonically accumulate the set of values that hold a pointer based on Sp
  // INVARIANT: an Instruction in the work list never defines a Value that is already in SpPointers
  std::set<const Value*> SpPointers;
  SpPointers.insert(sp_arg);

  // Initialize the worklist to all of the instructions using the Sp
  std::set<const Instruction*> WorkList;
  for (Value::const_use_iterator UI = sp_arg->use_begin(), UE = sp_arg->use_end(); UI != UE; ++UI)
      WorkList.insert(cast<Instruction>(*UI));
  
  while (!WorkList.empty()) {
    // Get an element from the worklist
    const Instruction *I = *WorkList.begin();
    WorkList.erase(WorkList.begin());

    // Switch on the kind of instruction to decide whether this instruction should add to SpPointers
    //
    // NB: it is safe to say "load" never adds to SpPointers, since we terminate the
    // fixed point process immediately if we ever detect that a SpPointer escapes.
    //
    // NB: The only calls we see in GHC-generated code will be unsafe foreign calls
    // or tail calls. In either case we can safely assume no escape.
    if (const StoreInst *SI = dyn_cast<StoreInst>(I)) {
      // Check for escape:
      if (SpPointers.find(SI->getValueOperand()) != SpPointers.end()) {
        return true;
      }
      continue;
#if 0
    } else if (AtomicCmpXchgInst *ACXI = dyn_cast<AtomicCmpXchgInst>(I)) {
      // Check for escape:
      if (SpPointers.find(ACXI->getNewValOperand()) != SpPointers.end()) {
        return true;
      }
      continue;
    } else if (AtomicRMWInst *ARMWI = dyn_cast<AtomicRMWInst>(I)) {
      // Check for escape:
      if (SpPointers.find(ARMWI->getValOperand()) != SpPointers.end()) {
        return true;
      }
      continue;
#endif
    } else if (const GetElementPtrInst *GEPI = dyn_cast<GetElementPtrInst>(I)) {
      if (SpPointers.find(GEPI->getPointerOperand()) == SpPointers.end()) {
        continue;
      }
    } else if (const SelectInst *SI = dyn_cast<SelectInst>(I)) {
      if ((SpPointers.find(SI->getTrueValue())  == SpPointers.end()) &&
          (SpPointers.find(SI->getFalseValue()) == SpPointers.end())) {
        continue;
      }
    } else if (isa<PHINode>(I)) {
      if (!SomeOperandIsSPPointer(SpPointers, I)) continue;
    } else if (isa<BinaryOperator>(I)) {
      if (!SomeOperandIsSPPointer(SpPointers, I)) continue;
    } else if (isa<CastInst>(I)) {
      if (!SomeOperandIsSPPointer(SpPointers, I)) continue;
    } else {
      // Assume all other instructions do not define new SpPointers or avenues for escape.
      continue;
    }

    // We fall through to here if this instruction defines a new SpPointer:
    // add all the use sites to the work list.
    SpPointers.insert(I);
    for (Value::const_use_iterator UI = I->use_begin(), UE = I->use_end(); UI != UE; ++UI) {
      // There is nothing more to do if we have already decided that this defines a SpPointer
      if (SpPointers.find(*UI) == SpPointers.end()) {
        WorkList.insert(cast<Instruction>(*UI));
      }
    }
  }

  return false;
}

bool
GHCAliasAnalysis::runOnFunction(Function &F) {
  AliasAnalysis::InitializeAliasAnalysis(this);
  this->scev_ = &getAnalysis<ScalarEvolution>();
  
  //errs() << "GHC Alias Analysis:\t";
  
  // Find the Sp argument to the function, if it is a GHC-convention function
  this->sp_arg_ = NULL;
  if (F.getCallingConv() == CallingConv::GHC) {
    const Function::ArgumentListType &args = F.getArgumentList();
    int ix = 0;
    Function::ArgumentListType::const_iterator it;
    for (it = args.begin(); it != args.end(); ix++, it++) {
      if (ix == 1) {
        this->sp_arg_ = &*it;
        //errs() << "Argument found!\n";
        //WriteAsOperand(errs(), it, true);
        //errs() << "\n";
        break;
      }
    }

    // Check safety: if we had code like:
    // %SpRef = alloca 8
    // store %SpRef, %Sp
    //
    // Then it would not be safe to assume that %Sp does  not alias with any
    // other non-%Sp pointer, because (load %SpRef) would not be based on %Sp
    // but would be an alias.
    //
    // Worse, this is exactly the sort of code that we get out of the LLVM backend!
    // Luckily, this crap is always removed quickly by LLVMs standard passes with
    // standard alias analysis. So we just need to check that we have no code like
    // this and we will be able to use our optimistic assumptions about %Sp aliasing.
    if ((this->sp_arg_ != NULL) && SPEscapes(F, this->sp_arg_)) {
      errs() << "SP escapes!\n";
      this->sp_arg_ = NULL;
    }
  } else {
    //errs() << "Not a GHC function!\n";
  }

  return false;
}

// Copied and adapted from ScalarEvolutionAliasAnalysis.
const Argument*
GetUnderlyingArgumentSCEV(const SCEV *S) {
  if (const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(S)) {
    // In an addrec, assume that the base will be in the start, rather
    // than the step.
    return GetUnderlyingArgumentSCEV(AR->getStart());
  } else if (const SCEVAddExpr *A = dyn_cast<SCEVAddExpr>(S)) {
    // If there's a pointer operand, it'll be sorted at the end of the list.
    const SCEV *Last = A->getOperand(A->getNumOperands()-1);
    if (isa<PointerType>(Last->getType()))
      return GetUnderlyingArgumentSCEV(Last);
  } else if (const SCEVUnknown *U = dyn_cast<SCEVUnknown>(S)) {
    // Determine if we've found a Argument.
    if (const Argument *A = dyn_cast<Argument>(U->getValue()))
      return A;
  }
  // No Argument found.
  return NULL;
}

AliasAnalysis::AliasResult
GHCAliasAnalysis::alias(const Location &L1, const Location &L2) {
  // Only do this check for functions using the GHC calling convention
  if (this->sp_arg_) {
    const Argument *A1 = GetUnderlyingArgumentSCEV(this->scev_->getSCEV(const_cast<Value*>(L1.Ptr)));
    const Argument *A2 = GetUnderlyingArgumentSCEV(this->scev_->getSCEV(const_cast<Value*>(L2.Ptr)));
    
    /*
    errs() << "Underlying arguments: ";
    if (A1) WriteAsOperand(errs(), A1, true);
    errs() << ", ";
    if (A2) WriteAsOperand(errs(), A2, true);
    errs() << "\n";
    */

    // This check may appear way too optimistic! The reason that it is safe is because we already checked
    // that the SP does not escape (locally) into any memory locations.
    if (!(A1 == this->sp_arg_ && A2 == this->sp_arg_) &&
         (A1 == this->sp_arg_ || A2 == this->sp_arg_))
        return NoAlias;
  }

  return AliasAnalysis::alias(L1, L2);
}
