#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/TinyPtrVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/StringSet.h"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/TypeBuilder.h"

#include "llvm/Pass.h"

#include "llvm/Transforms/Utils/ModuleUtils.h"

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/Regex.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include <string>


using namespace std;
using namespace llvm;


namespace FuncHook {

  enum class HookType {
    PRE_HOOK = 1,
    REPLACE_HOOK = 2,
    POST_HOOK = 4,
  };


  // FuncHook Pass
  class FuncHookPass : public ModulePass {

    public:
      static char ID;

      FuncHookPass() : ModulePass(ID) {}

      bool runOnModule(Module &M) override;

    private:

      const string fn_lltap_get_hook = "__lltap_inst_get_hook";
      const string fn_lltap_add_hook = "__lltap_inst_add_hook_target";
      const string fn_lltap_has_hooks = "__lltap_inst_has_hooks";

      const int DEFAULT_CTOR_PRIORITY = 0;

      SmallPtrSet<Function*, 100> funcHookFunctions;

      bool shouldBeInstrumented(Function& F);
      bool runOnFunction(Function& F);
      bool isUseInFuncHook(User* user);

      bool instrumentCall(CallSite* inst, Module& M);

      string mangleFunctionArgs(CallSite* CS);

      void addToGlobalCtors(Module& M, Function* fn);

      string getHookFunctionNameFor(Function* origFunc, CallSite* CS=nullptr);
      Function* getHookFunctionFor(CallSite* CS, Module& M);
      Function* getHookFunctionFor(Function* origFunc, Module& M);
      Function* createHookFunction(StringRef name, CallSite* call, Function* F, Module& M);
      Function* createHookFunction(StringRef name, Function* origFunc, Module& M);
      bool createHookingCode(Function* origFunc, Function* F, Module& M);

      void addCallTarget(Function* calledFn, Module &M);
      Function* getOrAddInitializerToModule(Module &M);
      void declareFuncHookFunctions(Module &M);
  };

}

using namespace FuncHook;

// Register the FuncHook Pass with the LLVM environment
char FuncHook::FuncHookPass::ID = 0;
static RegisterPass<FuncHook::FuncHookPass> IP("LLTapInst", "FuncHook instrumentation pass");

// The below function is used for mangling Function args.
string FuncHookPass::mangleFunctionArgs(CallSite* CS) {

  string mangled = "";
  DEBUG(dbgs() << "starting arg mangling\n");
  
  for (size_t i = 0; i < CS->getNumArgOperands(); ++i) {
    string typestr = "";
    Type* type = CS->getArgument(i)->getType();
    llvm::raw_string_ostream rso(typestr);
    type->print(rso);
    rso.flush();

    DEBUG(dbgs() << "typestring arg " << i << " " << typestr << " (should be " << *type << ")\n");

    Regex star("[\\*]");
    Regex whitespace("\\s");
    Regex printable("[^a-zA-Z0-9_]+");

    while (star.match(typestr)) {
      typestr = star.sub("p", typestr);
    }

    while (whitespace.match(typestr)) {
      typestr = whitespace.sub("_", typestr);
    }

    while (printable.match(typestr)) {
      typestr = printable.sub("", typestr);
    }
    DEBUG(dbgs() << "mangled type string " << typestr << "\n");

    mangled += typestr;
  }

  return mangled;
}


// The below function inserts the runtime functions into the module.
void FuncHookPass::declareFuncHookFunctions(Module &M) {

  PointerType* i8ptr = PointerType::getUnqual(IntegerType::get(M.getContext(), 8));
  Type* i32 = IntegerType::get(M.getContext(), 32);

  PointerType* voidptr = i8ptr;
  FunctionType *ft;
  std::vector<Type*> ftargs;

  // add function declarations to module:
  ftargs.clear();
  ftargs.push_back(voidptr);
  ftargs.push_back(i8ptr);
  ft = FunctionType::get(
      Type::getVoidTy(M.getContext()),
      ftargs,
      false);
  M.getOrInsertFunction(fn_lltap_add_hook, ft);

  ftargs.clear();
  ftargs.push_back(voidptr);
  ftargs.push_back(i32);
  ft = FunctionType::get(
      voidptr,
      ftargs,
      false);
  M.getOrInsertFunction(fn_lltap_get_hook, ft);

  ftargs.clear();
  ftargs.push_back(voidptr);
  ft = FunctionType::get(
      i32,
      ftargs,
      false);
  M.getOrInsertFunction(fn_lltap_has_hooks, ft);
}


// The below function loop over all the functions and apply instrumentation.
bool FuncHookPass::runOnModule(Module &M) {

  DEBUG(dbgs() << "Running on module: " << M.getModuleIdentifier() << "\n");

  declareFuncHookFunctions(M);

  // then instrument all the functions
  for (Function& F : M.getFunctionList()) {
    runOnFunction(F);
  }

  return true;
}

// Add function to the global constructor table of given module.
void FuncHookPass::addToGlobalCtors(Module& M, Function* fn) {
  // just use the LLVM provided function for this.
  appendToGlobalCtors(M, fn, DEFAULT_CTOR_PRIORITY);
}


// Create the initializer function
Function* FuncHookPass::getOrAddInitializerToModule(Module& M) {

  string name = "__funchook_init_";
  name.append(M.getName());

  Function* initFn = M.getFunction(name);

  if (initFn == NULL) {
    // need to create the function

    std::vector<Type*> args;
    FunctionType* FT = FunctionType::get(
        /*Result=*/Type::getVoidTy(M.getContext()),
        /*Params=*/args,
        /*isVarArg=*/false);

    initFn = Function::Create(FT, Function::ExternalLinkage, name, &M);

    BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", initFn);
    IRBuilder<> irb(BB);
    irb.CreateRetVoid();

    //DEBUG(dbgs() << "created function:" << *BB << "\n");

    addToGlobalCtors(M, initFn);
  }

  return initFn;
}

void FuncHookPass::addCallTarget(Function* calledFn, Module &M) {

  if (calledFn->isIntrinsic()) {
    return;
  }

  string fname = "";
  /*if (! HookNamespace.empty()) {
    fname += HookNamespace + "_";
  }*/
  fname += calledFn->getName();

  string varname = "__funchook_fname_";
  varname.append(fname);

  if (M.getNamedValue(varname) == NULL) {

    Function* initfunc = getOrAddInitializerToModule(M);
    IRBuilder<> irb(initfunc->getEntryBlock().getFirstNonPHIOrDbgOrLifetime());

    PointerType* voidptr = PointerType::getUnqual(IntegerType::get(M.getContext(), 8));
    Constant* funcaddr = ConstantExpr::getCast(Instruction::BitCast, calledFn, voidptr);

    Function* callee = M.getFunction(fn_lltap_add_hook);

    Value* val = irb.CreateGlobalStringPtr(fname, varname);

    SmallVector<Value*, 2> args;
    args.push_back(funcaddr);
    args.push_back(val);

    //callee, args,
    irb.CreateCall(callee, args);
  }

}


bool FuncHookPass::isUseInFuncHook(User* user) {
  
  if (Instruction* inst = dyn_cast<Instruction>(user)) {
    DEBUG(dbgs() << "user" << *user << "is inside a funcHook generated function: skipping\n");
    return funcHookFunctions.count(inst->getParent()->getParent()) == 1;
  }

  return true;
}


/**
 * Check whether the given Function matches the instrumentation mode and regexes.
 *
 */
bool FuncHookPass::shouldBeInstrumented(Function& F) {

  // skip all lltap functions
  if (F.getName().find("lltap") != string::npos) {
    return false;
  }

  if (funcHookFunctions.count(&F) == 1) {
    return false;
  }

  // Instrument all sapphire functions.
  if (F.getName().find("sapphire") != string::npos) {
    return true;
  }

  //if (F.getName() == "main.say_hello")
  if (F.getName() == "main.helloWorld")
    return true;
  else
    return false;
}


/**
 * Instrument all uses of the given function. For each function it is checked whether it should be
 * instrumented with \ref shouldBeInstrumented and for each use it is checked whether it is inside
 * a function generated by this pass.
 */
bool FuncHookPass::runOnFunction(Function &F) {

  bool changed = false;

  DEBUG(dbgs() << "Function: ");
  DEBUG(dbgs().write_escaped(F.getName()) << '\n');

  if (! shouldBeInstrumented(F)) {
    DEBUG(dbgs() << "...skipping\n");
    return false;
  }

  DEBUG(dbgs() << "got " << F.getNumUses() << " uses\n");

  SmallVector<User*, 16> worklist;
  for (User* user : F.users()) {
    DEBUG(dbgs() << "found user " << *user << "\n");
    worklist.push_back(user);
  }

  for (User* user : worklist) {
    if (! isUseInFuncHook(user)) {
      if (isa<CallInst>(user)) {
        CallSite CI(user);
        changed |= instrumentCall(&CI, *(F.getParent()));
      }
    }
  }

  return changed;
}

/**
 * Instrument a CallSite in a given Module.
 *
 */
bool FuncHookPass::instrumentCall(CallSite* call, Module& M) {

  bool mod = true;

  Value* calledVal = call->getCalledValue();

  if (! isa<Function>(calledVal)) {
    return false;
  }
  Function* calledFn = call->getCalledFunction();

  if (calledFn->isIntrinsic()) {
    DEBUG(dbgs() << "ignoring intrinsic function " << calledFn->getName() << "\n");
    return false;
  }
addCallTarget(calledFn, M);

  CallInst* inst = dyn_cast<CallInst>(call->getInstruction());
  Function* hook_fn = getHookFunctionFor(call, M);
  inst->setCalledFunction(hook_fn);

  DEBUG(dbgs() << "hooked call to " << calledFn->getName() << "\n"
      << "with type: " << *calledFn->getFunctionType() << "\n");

  return mod;
}

/**
 * Returns the name of the function that is replacing the original function in the original call.
 */
string FuncHookPass::getHookFunctionNameFor(Function* origFunc, CallSite* CS) {
  string hookfnname = string("__lltap_hook_") + string(origFunc->getName());
  if (origFunc->isVarArg()) {
    hookfnname += "_" + mangleFunctionArgs(CS);
  }
  return hookfnname;
}

/**
 * Get the hook function or create a new one if it doesn't exist.
 */
Function* FuncHookPass::getHookFunctionFor(CallSite* CS, Module& M) {
  Function* origFunc = CS->getCalledFunction();
  string hookfnname = getHookFunctionNameFor(origFunc, CS);
  if (M.getFunction(hookfnname) != NULL) {
    return M.getFunction(hookfnname);
  } else {
    return createHookFunction(StringRef(hookfnname), CS, origFunc, M);
  }
}

/**
 * Get the hook function or create a new one if it doesn't exist.
 */
Function* FuncHookPass::getHookFunctionFor(Function* origFunc, Module& M) {
  string hookfnname = getHookFunctionNameFor(origFunc);
  if (M.getFunction(hookfnname) != NULL) {
    return M.getFunction(hookfnname);
  } else {
    return createHookFunction(StringRef(hookfnname), origFunc, M);
  }
}


/**
 * Same as \ref createHookFunction but takes a callsite as parameter. This is useful for functions
 * with variable number of arguments.
 */
Function* FuncHookPass::createHookFunction(StringRef name, CallSite* call, Function* origFunc, Module& M) {

  std::vector<Type*> ftargs;
  FunctionType* FT = nullptr;
  if (! call->getCalledFunction()->isVarArg()) {
    FT = origFunc->getFunctionType();
  } else {
    for (size_t i = 0; i < call->getNumArgOperands(); ++i) {
      ftargs.push_back(call->getArgument(i)->getType());
    }
    FT = FunctionType::get(
        origFunc->getReturnType(),
        ftargs,
        false);

    ftargs.clear();
  }

  DEBUG(dbgs() << "creating hook function " << name << " with type " << *FT <<
      " numparams " << FT->getNumParams() << "\n");

  // create function
  Function* hookFn = Function::Create(FT, Function::ExternalLinkage, name, &M);
  createHookingCode(origFunc, hookFn, M);

  // add to set of FuncHook generated functions
  funcHookFunctions.insert(hookFn);

  return hookFn;
}


/**
 * Create a hook function, which replaces the original function in the original call.
 * see \ref createHookingCode
 */
Function* FuncHookPass::createHookFunction(StringRef name, Function* origFunc, Module& M) {

  std::vector<Type*> ftargs;
  FunctionType* FT = origFunc->getFunctionType();

  DEBUG(dbgs() << "creating hook function " << name << " with type " << *FT <<
      " numparams " << FT->getNumParams() << "\n");

  // create function
  Function* hookFn = Function::Create(FT, Function::ExternalLinkage, name, &M);
  createHookingCode(origFunc, hookFn, M);

  // add to set of FuncHook generated functions
  funcHookFunctions.insert(hookFn);

  return hookFn;
}


// The below function generates space for the hook
bool FuncHookPass::createHookingCode(Function* origFunc, Function* F, Module& M) {

  FunctionType* origFT = origFunc->getFunctionType();
  FunctionType* FT = F->getFunctionType();
  size_t numparams = FT->getNumParams();
  bool fn_returns_void = FT->getReturnType()->isVoidTy();

  DEBUG(dbgs() << "instrumenting call to function " << origFunc->getName()
      << " with type " << *FT << "\n");

  // append basicblocks for the hook calling
  // --> entry
  // entry --> init
  BasicBlock *entry_BB = BasicBlock::Create(M.getContext(), "entry", F);
  // init --> check_pre (if hooks bitmap != 0)
  //      --> call_orig (if hooks bitmap == 0)
  BasicBlock* init_bb = BasicBlock::Create(M.getContext(), "init", F);

  // check_pre --> call_pre (if hooks bitmap & PRE_HOOK != 0)
  //           --> check_rh
  BasicBlock* check_pre_bb = BasicBlock::Create(M.getContext(), "check_pre", F);
  // call_pre --> check_rh
  BasicBlock* call_pre_bb = BasicBlock::Create(M.getContext(), "call_pre", F);

  // check_rh --> call_rh (if hooks bitmap & REPLACE_HOOK != 0)
  //          --> call_orig
  BasicBlock* check_rh_bb = BasicBlock::Create(M.getContext(), "check_rh", F);
  // call_rh --> check_post
  BasicBlock* call_rh_bb = BasicBlock::Create(M.getContext(), "call_rh", F);
  // call_orig --> return (if hooks bitmap == 0)
  //           --> check_post
  BasicBlock* call_orig_bb = BasicBlock::Create(M.getContext(), "call_orig", F);

  // check_post --> call_post (if hooks bitmap & POST_HOOK != 0)
  //                return
  BasicBlock* check_post_bb = BasicBlock::Create(M.getContext(), "check_post", F);
  // call_post --> return
  BasicBlock* call_post_bb = BasicBlock::Create(M.getContext(), "call_post", F);

  BasicBlock *return_bb = BasicBlock::Create(M.getContext(), "return", F);


  // some "constants" used below
  PointerType* i8ptr = PointerType::getUnqual(IntegerType::get(M.getContext(), 8));
  Constant* orig_func_addr = ConstantExpr::getCast(Instruction::BitCast, origFunc, i8ptr);

  Value* i32_zero = ConstantInt::get(IntegerType::getInt32Ty(M.getContext()), 0);

  // create the instruction in the BBs
  //************************************************************
  // entry and init
  SmallVector<Value*, 4> args;
  Value* ret = nullptr;
  AllocaInst* retval = nullptr;
  AllocaInst** params = new AllocaInst*[numparams];
  Value* hooks_avail = nullptr;
  Value* no_hooks = nullptr;

  {
    IRBuilder<> entry(entry_BB);
    IRBuilder<> init(init_bb);

    size_t i = 0;
    for (auto arg = F->arg_begin(); arg != F->arg_end(); arg++) {
      params[i] = entry.CreateAlloca(arg->getType(), nullptr, "arg");
      init.CreateStore(&*arg, params[i]);
      i++;
    }

    if (! fn_returns_void) {
      retval = entry.CreateAlloca(FT->getReturnType(), nullptr, "ret");
    }


    // from entry BB jump to initialization BB
    entry.CreateBr(init_bb);

    // get the hooks availability bitmap
    Function* has_hooks = M.getFunction(fn_lltap_has_hooks);
    args.push_back(orig_func_addr);
    hooks_avail = init.CreateCall(has_hooks, args);
    no_hooks = init.CreateICmpEQ(hooks_avail, i32_zero);
    init.CreateCondBr(no_hooks, call_orig_bb, check_pre_bb);
  }


  //************************************************************
  // pre hook

  Function* get_hook = M.getFunction(fn_lltap_get_hook);
  std::vector<Type*> ftargs;

  {
    IRBuilder<> check_pre(check_pre_bb);
    IRBuilder<> call_pre(call_pre_bb);

    Value* HookType_Enum_pre = ConstantInt::get(IntegerType::getInt32Ty(M.getContext()),
        (uint64_t)HookType::PRE_HOOK);

    for (Type* param : origFT->params()) {
      PointerType* param_ptr = PointerType::getUnqual(param);
      ftargs.push_back(param_ptr);
    }

    FunctionType* pre_ft = FunctionType::get(
        Type::getVoidTy(M.getContext()),
        ftargs,
        origFunc->isVarArg());
    PointerType* pre_ptrty = PointerType::getUnqual(pre_ft);

    Value* has_pre_hook = check_pre.CreateICmpNE(
        check_pre.CreateAnd(hooks_avail, HookType_Enum_pre),
        i32_zero);
    check_pre.CreateCondBr(has_pre_hook, call_pre_bb, check_rh_bb);

    args.clear();
    args.push_back(orig_func_addr);
    args.push_back(HookType_Enum_pre);
    Value* preval = call_pre.CreateCall(get_hook, args);


    args.clear();
    for (size_t i = 0; i < numparams; ++i) {
      args.push_back(params[i]);
    }
    Value* pre = call_pre.CreateBitCast(preval, pre_ptrty);
    call_pre.CreateCall(pre, args);
    call_pre.CreateBr(check_rh_bb);
  }


  //************************************************************
  // replace hook (rh)
  {
    IRBuilder<> call_rh(call_rh_bb);
    IRBuilder<> check_rh(check_rh_bb);
    IRBuilder<> call_orig(call_orig_bb);

    Value* HookType_Enum_replace = ConstantInt::get(IntegerType::getInt32Ty(M.getContext()),
        (uint64_t)HookType::REPLACE_HOOK);

    // create replace hook
    ftargs.clear();
    for (Type* param : origFT->params()) {
      ftargs.push_back(param);
    }

    FunctionType* rh_ft = FunctionType::get(
        FT->getReturnType(),
        ftargs,
        origFunc->isVarArg());
    PointerType* rh_ptr = PointerType::getUnqual(rh_ft);

    Value* has_replace_hook = check_rh.CreateICmpNE(
        check_rh.CreateAnd(hooks_avail, HookType_Enum_replace),
        i32_zero);
    check_rh.CreateCondBr(has_replace_hook, call_rh_bb, call_orig_bb);

    // then call original function
    args.clear();
    for (size_t i = 0; i < numparams; ++i) {
      Value* p = call_orig.CreateLoad(params[i]);
      args.push_back(p);
    }
    ret = call_orig.CreateCall(origFunc, args);
    if (!fn_returns_void) {
      call_orig.CreateStore(ret, retval);
    }

    call_orig.CreateCondBr(no_hooks, return_bb, check_post_bb);

    // else call replace hook function
    args.clear();
    args.push_back(orig_func_addr);
    args.push_back(HookType_Enum_replace);

    Value* rhval = call_rh.CreateCall(get_hook, args);

    args.clear();
    for (size_t i = 0; i < numparams; ++i) {
      Value* p = call_rh.CreateLoad(params[i]);
      args.push_back(p);
    }
    Value* rh = call_rh.CreateBitCast(rhval, rh_ptr);
    ret = call_rh.CreateCall(rh, args);
    if (!fn_returns_void) {
      call_rh.CreateStore(ret, retval);
    }
    call_rh.CreateBr(check_post_bb);
  }


  //************************************************************
  // post hook

  {
    IRBuilder<> check_post(check_post_bb);
    IRBuilder<> call_post(call_post_bb);

    Value* HookType_Enum_post = ConstantInt::get(IntegerType::getInt32Ty(M.getContext()),
        (uint64_t)HookType::POST_HOOK);

    ftargs.clear();
    if (!fn_returns_void) {
      PointerType* ret_ptr = PointerType::getUnqual(FT->getReturnType());
      ftargs.push_back(ret_ptr);
    }
    for (Type* param : origFT->params()) {
      ftargs.push_back(param);
    }

    FunctionType* post_ft = FunctionType::get(
        Type::getVoidTy(M.getContext()),
        ftargs,
        origFunc->isVarArg());
    PointerType* post_ptrty = PointerType::getUnqual(post_ft);

    // check for post
    Value* has_post_hook = check_post.CreateICmpNE(
        check_post.CreateAnd(hooks_avail, HookType_Enum_post),
        i32_zero);
    check_post.CreateCondBr(has_post_hook, call_post_bb, return_bb);

    // call post hook
    args.clear();
    args.push_back(orig_func_addr);
    args.push_back(HookType_Enum_post);
    Value* postval = call_post.CreateCall(get_hook, args);

    args.clear();
    if (!fn_returns_void) {
      args.push_back(retval);
    }
    for (size_t i = 0; i < numparams; ++i) {
      Value* p = call_post.CreateLoad(params[i]);
      args.push_back(p);
    }
    Value* post = call_post.CreateBitCast(postval, post_ptrty);
    call_post.CreateCall(post, args);
    call_post.CreateBr(return_bb);
  }

  //************************************************************
  // load retval and return
  {
    IRBuilder<> return_irb(return_bb);

    if (!fn_returns_void) {
      ret = return_irb.CreateLoad(retval);
      return_irb.CreateRet(ret);
    } else {
      return_irb.CreateRetVoid();
    }
  }

  //************************************************************

  delete[] params;

  return true;
}


