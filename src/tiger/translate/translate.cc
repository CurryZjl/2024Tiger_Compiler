#include "tiger/translate/translate.h"

#include <tiger/absyn/absyn.h>

#include "tiger/env/env.h"
#include "tiger/errormsg/errormsg.h"
#include "tiger/frame/x64frame.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <iostream>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>
#include <stack>
#include <assert.h>

extern frame::Frags *frags;
extern frame::RegManager *reg_manager;
extern llvm::IRBuilder<> *ir_builder;
extern llvm::Module *ir_module;
std::stack<llvm::Function *> func_stack;
std::stack<llvm::BasicBlock *> loop_stack;
llvm::Function *alloc_record;
llvm::Function *init_array;
llvm::Function *string_equal;
std::vector<std::pair<std::string, frame::Frame *>> frame_info;

bool CheckBBTerminatorIsBranch(llvm::BasicBlock *bb) {
  auto inst = bb->getTerminator();
  if (inst) {
    llvm::BranchInst *branchInst = llvm::dyn_cast<llvm::BranchInst>(inst);
    if (branchInst && !branchInst->isConditional()) {
      return true;
    }
  }
  return false;
}

int getActualFramesize(tr::Level *level) {
  return level->frame_->calculateActualFramesize();
}

llvm::GlobalVariable *addGlobalValue(llvm::Module* ir_module, std::string name, llvm::Type *type, llvm::Constant *initializer, int align)
{
    llvm::GlobalVariable *global = (llvm::GlobalVariable *)ir_module->getOrInsertGlobal(name, type);
    global->setInitializer(initializer);
    global->setDSOLocal(true);
    global->setAlignment(llvm::MaybeAlign(align));
    return global;
}

namespace tr {

Access *Access::AllocLocal(Level *level, bool escape) {
  return new Access(level, level->frame_->AllocLocal(escape));
}

class ValAndTy {
public:
  type::Ty *ty_;
  llvm::Value *val_;
  llvm::BasicBlock *last_bb_;

  ValAndTy(llvm::Value *val, type::Ty *ty) : val_(val), ty_(ty) {}
};

void ProgTr::OutputIR(std::string_view filename) {
  std::string llvmfile = std::string(filename) + ".ll";
  std::error_code ec;
  llvm::raw_fd_ostream out(llvmfile, ec, llvm::sys::fs::OpenFlags::OF_Text);
  ir_module->print(out, nullptr);
}

void ProgTr::Translate() {
  FillBaseVEnv();
  FillBaseTEnv();
  type::Ty *s_ty = type::StringTy::Instance();
  /* TODO: Put your lab5-part1 code here */
  llvm::FunctionType *string_equal_func_type = llvm::FunctionType::get(
      	ir_builder->getInt1Ty(),
      	{s_ty->GetLLVMType(), s_ty->GetLLVMType()}, false);
  string_equal = llvm::Function::Create(string_equal_func_type,
        llvm::Function::ExternalLinkage, "string_equal", ir_module);

  llvm::FunctionType *alloc_record_func_type = llvm::FunctionType::get(
      	ir_builder->getInt64Ty(),
      	{ir_builder->getInt32Ty()}, false);
  alloc_record = llvm::Function::Create(alloc_record_func_type,
    llvm::Function::ExternalLinkage, "alloc_record", ir_module);
  
  llvm::FunctionType *init_array_func_type = llvm::FunctionType::get(
      	ir_builder->getInt64Ty(),
      	{ir_builder->getInt32Ty(), ir_builder->getInt64Ty()}, false);
  init_array = llvm::Function::Create(init_array_func_type,
    llvm::Function::ExternalLinkage, "init_array", ir_module);
  

  /*tiger main*/
  std::vector<llvm::Type *> formals_ty;
  formals_ty.push_back(ir_builder->getInt64Ty());
  formals_ty.push_back(ir_builder->getInt64Ty());
  llvm::FunctionType *func_type = llvm::FunctionType::get(
      ir_builder->getInt32Ty(), 
      formals_ty, false);
  llvm::Function *func = llvm::Function::Create(func_type, 
    llvm::Function::ExternalLinkage, "tigermain", ir_module);
  
  llvm::GlobalVariable *global_frame_size = new llvm::GlobalVariable(
      llvm::Type::getInt64Ty(ir_builder->getContext()), true,
      llvm::GlobalValue::InternalLinkage,
      llvm::ConstantInt::get(llvm::Type::getInt64Ty(ir_builder->getContext()),0),
      "tigermain_frame_size");
  ir_module->getGlobalList().push_back(global_frame_size);
  func_stack.push(func);
  llvm::BasicBlock *bb = llvm::BasicBlock::Create(ir_builder->getContext(), "tigermain", func);
  ir_builder->SetInsertPoint(bb);

  auto real_arg_it = func->arg_begin();
  this->main_level_->set_sp(real_arg_it);
  this->main_level_->frame_->framesize_global = global_frame_size;

  ValAndTy *result = this->absyn_tree_->Translate(this->venv_.get(), this->tenv_.get(), this->main_level_.get(), this->errormsg_.get());
  if (result->ty_ != type::VoidTy::Instance())
    ir_builder->CreateRet(result->val_);
  else
    ir_builder->CreateRet(llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
  
  func_stack.pop();
}

llvm::Value *GetStaticLink(tr::Level *current_level, tr::Level *target_level){
  llvm::Value *val = current_level->get_sp();
  while(current_level != target_level){
    // The first accessible frame-offset_ values is the static link
    auto sl_formal = current_level->frame_->Formals()->begin();
    assert(sl_formal != current_level->frame_->Formals()->end());
    llvm::Value *static_link_addr = (*sl_formal)->ToLLVMVal(val);
    llvm::Value *static_link_ptr = ir_builder->CreateIntToPtr(
          static_link_addr,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));
    val = ir_builder->CreateLoad(ir_builder->getInt64Ty(), static_link_ptr);
    current_level = current_level->parent_;
  }
  //返回目标sp的int值
  return val;
}

} // namespace tr

namespace absyn {

tr::ValAndTy *AbsynTree::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                   tr::Level *level,
                                   err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return this->root_->Translate(venv, tenv, level, errormsg);
}

void TypeDec::Translate(env::VEnvPtr venv, env::TEnvPtr tenv, tr::Level *level,
                        err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  //Update type declaration into tenv
  std::list<NameAndTy *> name_and_ty_list = this->types_->GetList();
  for (NameAndTy *name_and_ty : name_and_ty_list) {
    tenv->Enter(name_and_ty->name_, new type::NameTy(name_and_ty->name_, NULL));
  }
  for (NameAndTy *type_dec : name_and_ty_list) {
    type::NameTy *name_ty = (type::NameTy *) tenv->Look(type_dec->name_);
    name_ty->ty_ = type_dec->ty_->Translate(tenv, errormsg);
  }
}

void FunctionDec::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                            tr::Level *level, err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  /*
  define i32 @func_name(i64 %par_sp, i64 %sl, i32 %2, i32 %3, i32 %4 ... ...) 
  
  tr::Level::NewLevel, llvm::Function::Create, new env::FunEntry
  Add FunEntry to venv
  */
  std::list<FunDec *> fundec_list = this->functions_->GetList();
  for(FunDec *fundec : fundec_list){
    type::Ty *result_type = type::VoidTy::Instance();
    if (fundec->result_ != NULL)
      result_type = tenv->Look(fundec->result_);
    std::list<bool> *escape_list = new std::list<bool>;
    escape_list->push_back(true); // static link
    for (Field *field : fundec->params_->GetList())
      escape_list->push_back(field->escape_);
    
    temp::Label *func_label = temp::LabelFactory::NamedLabel(fundec->name_->Name());
    /* Get formals' type list */
    type::TyList *formalTys = fundec->params_->MakeFormalTyList(tenv, errormsg);
    std::list<type::Ty *> formals_list = formalTys->GetList();
    std::vector<llvm::Type *> types;
    types.push_back(ir_builder->getInt64Ty());
    types.push_back(ir_builder->getInt64Ty());
    for(type::Ty *tyy : formals_list){
      types.push_back(tyy->GetLLVMType());
    }
    /* Create level */
    tr::Level *func_level = new tr::Level(level, func_label, escape_list);
    /* Store function entry in venv */
    llvm::FunctionType *func_ty = llvm::FunctionType::get(
      	result_type->GetLLVMType(),
      	types, false);
    llvm::Function *func = llvm::Function::Create(func_ty,
      llvm::Function::ExternalLinkage, fundec->name_->Name(), ir_module);
    
    venv->Enter(fundec->name_, new env::FunEntry(func_level, formalTys, result_type, func_ty, func ));
  }

  /* Second */
  /*
  Build a @func_name_framesize_global, set into 
    fun_level->frame_->framesize_global, (keep init value 0)
  fun_level->set_sp(ir_builder->CreateSub(sp_arg_val, func_framesize));
  Build a body_bb
  Store %sl, %2 %3 … to their InFrameAccess address(init)
  Translate body
  ir_builder->CreateRet
  Framesize can be decided, set it back
  (-level->frame_->offset_ + level->frame_->outgo_size_) / 16 * 16 + 8;
  */
  for (FunDec *fundec : fundec_list) {
    venv->BeginScope();
    env::FunEntry *func_entry = (env::FunEntry *) venv->Look(fundec->name_);
    tr::Level *func_level = func_entry->level_;
    frame::Frame *func_frame = func_level->frame_;
    llvm::Function *func_llvm = func_entry->func_;
    assert(func_frame != NULL);
    //int actualFramesize = func_frame->calculateActualFramesize();
    llvm::Constant *initValue = llvm::ConstantInt::get(llvm::Type::getInt64Ty(ir_module->getContext()), 0);
    
    llvm::GlobalVariable *framesize_global = addGlobalValue(ir_module,  fundec->name_->Name() + "_framesize_global", llvm::Type::getInt64Ty(ir_module->getContext()),initValue, 8);
    ir_module->getGlobalList().push_back(framesize_global);
    func_stack.push(func_llvm);

    func_frame->framesize_global = framesize_global;
    //NOTE!!!
    llvm::Value *load_frame_size = ir_builder->CreateLoad(ir_builder->getInt64Ty(), func_frame->framesize_global);

    auto ArgIt = func_llvm->arg_begin();
    llvm::Value *sp_arg_val = ArgIt++;
    func_level->set_sp(ir_builder->CreateSub(sp_arg_val, load_frame_size));

    llvm::BasicBlock *entry_bb = llvm::BasicBlock::Create(ir_module->getContext(), fundec->name_->Name(), func_llvm);
    ir_builder->SetInsertPoint(entry_bb);
    std::list<type::Field *> param_list = fundec->params_->MakeFieldList(tenv, errormsg)->GetList();
    auto formal_it = func_frame->formals_->begin();
    //Store %sl, %2 %3 … to their InFrameAccess address(init)
    //formal_it指向的是我分配的某个access。从之前声明的栈分配看，第一个就是sl，sp是不会出现在formals的
    for (type::Field *param_it : param_list) {
      llvm::Value *arg_val = ArgIt++;
      tr::Access *param_it_access = new tr::Access(func_entry->level_, *formal_it);
      venv->Enter(param_it->name_, new env::VarEntry(param_it_access, param_it->ty_->ActualTy()));
      llvm::Value *acc_addr = (*formal_it)->ToLLVMVal(func_level->get_sp());
      llvm::Value *acc_ptr = ir_builder->CreateIntToPtr(
          acc_addr,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));
      ir_builder->CreateStore(arg_val, acc_ptr);
      
    }
    tr::ValAndTy *body_val_ty = fundec->body_->Translate(venv, tenv, func_entry->level_, errormsg);
    if (func_entry->result_->IsSameType(type::VoidTy::Instance())) {
        ir_builder->CreateRetVoid();
    } else{
       ir_builder->CreateRet(body_val_ty->val_);
    }
   
    int framesize = func_frame->calculateActualFramesize();
    framesize_global->setInitializer(llvm::ConstantInt::get(llvm::Type::getInt64Ty(ir_module->getContext()), framesize));
    venv->EndScope();
  }
}

void VarDec::Translate(env::VEnvPtr venv, env::TEnvPtr tenv, tr::Level *level,
                       err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  //Update venv
  //An assignment for init.
  tr::Access *var_access = tr::Access::AllocLocal(level, this->escape_);
  tr::ValAndTy *init_val_and_type = this->init_->Translate(venv, tenv, level, errormsg);
  venv->Enter(this->var_, new env::VarEntry(var_access, init_val_and_type->ty_));
  llvm::Value *addr = var_access->access_->ToLLVMVal(level->get_sp());
  llvm::Value *ptr = ir_builder->CreateIntToPtr(
          addr,
          init_val_and_type->ty_->GetLLVMType()->getPointerTo());
  ir_builder->CreateStore(init_val_and_type->val_, ptr);

}

type::Ty *NameTy::Translate(env::TEnvPtr tenv, err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  type::Ty *nameType = tenv->Look(this->name_);
  return new type::NameTy(this->name_, nameType);
}

type::Ty *RecordTy::Translate(env::TEnvPtr tenv,
                              err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return new type::RecordTy(this->record_->MakeFieldList(tenv, errormsg));
}

type::Ty *ArrayTy::Translate(env::TEnvPtr tenv, err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return new type::ArrayTy(tenv->Look(this->array_)->ActualTy());
}

tr::ValAndTy *SimpleVar::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                   tr::Level *level,
                                   err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  //simple->x
  env::VarEntry *var_entry = (env::VarEntry *) venv->Look(this->sym_);
  tr::Level *var_level = var_entry->access_->level_;
  frame::Access *var_faccess = var_entry->access_->access_;
  //得到这个变量所在的level的stack_top
  llvm::Value* frame_addr = tr::GetStaticLink(level, var_level);
  llvm::Value *val = ir_builder->CreateIntToPtr(
          var_faccess->ToLLVMVal(frame_addr),
          llvm::PointerType::get(var_entry->ty_->GetLLVMType(), 0),
          "x_ptr");
  return new tr::ValAndTy(val, var_entry->ty_->ActualTy());
}

tr::ValAndTy *FieldVar::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                  tr::Level *level,
                                  err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  //a.f
  tr::ValAndTy *var_and_ty = this->var_->Translate(venv, tenv, level, errormsg);
  std::list<type::Field *> field_list = ((type::RecordTy *)var_and_ty->ty_)->fields_->GetList();
  int offset = 0;
  type::Ty *type = NULL;
  for(type::Field *f : field_list){
    if(f->name_ == this->sym_){
      type = f->ty_;
      break;
    }
    ++offset;
  }
  offset *= reg_manager->WordSize();
  llvm::Value *addr = ir_builder->CreateNSWAdd(var_and_ty->val_, llvm::ConstantInt::get(llvm::Type::getInt32Ty(ir_module->getContext()), offset));
  llvm::Value *ptr = ir_builder->CreateIntToPtr(
          addr,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));
  llvm::Value *load_val = ir_builder->CreateLoad(ir_builder->getInt64Ty(), ptr);
  return new tr::ValAndTy(load_val , type);
}

tr::ValAndTy *SubscriptVar::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                      tr::Level *level,
                                      err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  tr::ValAndTy *var_val_ty = this->var_->Translate(venv, tenv, level, errormsg);
  tr::ValAndTy *sub_val_ty = this->subscript_->Translate(venv, tenv, level, errormsg);
  llvm::Value *sub_val = ir_builder->CreateNSWMul(sub_val_ty->val_, llvm::ConstantInt::get(llvm::Type::getInt32Ty(ir_module->getContext()), reg_manager->WordSize()));
  llvm::Value *val = ir_builder->CreateNSWAdd(var_val_ty->val_, sub_val);
  llvm::Value *ptr = ir_builder->CreateIntToPtr(
          val,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));
  llvm::Value *load_val = ir_builder->CreateLoad(ir_builder->getInt64Ty(), ptr);
  return new tr::ValAndTy(load_val , ((type::ArrayTy *) var_val_ty->ty_)->ty_->ActualTy());
}

tr::ValAndTy *VarExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                tr::Level *level,
                                err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return this->var_->Translate(venv, tenv, level, errormsg);
}

tr::ValAndTy *NilExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                tr::Level *level,
                                err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return  new tr::ValAndTy(NULL, type::NilTy::Instance());
}

tr::ValAndTy *IntExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                tr::Level *level,
                                err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return  new tr::ValAndTy(llvm::ConstantInt::get(llvm::Type::getInt32Ty(ir_module->getContext()), this->val_), type::IntTy::Instance());
}

tr::ValAndTy *StringExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                   tr::Level *level,
                                   err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return new tr::ValAndTy(type::StringTy::CreateGlobalStringStructPtr(this->str_), type::StringTy::Instance());
}

tr::ValAndTy *CallExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                 tr::Level *level,
                                 err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  //call void @nop(i64 %init_sp, i64 %46) 
  //
  //%84 = call i32 @bsearch(i64 %bsearch_sp, i64 %83, i32 %72, i32 %actual_parm, i32 %actual_parm11)
  env::FunEntry *func_entry = (env::FunEntry *) venv->Look(this->func_);
  std::list<absyn::Exp *> arg_list = this->args_->GetList(); //实参列表
  type::Ty *result_ty = func_entry->result_;
  std::vector<llvm::Value *> args;

  //local stack pointer
  llvm::Value *my_sp = level->get_sp();
  args.push_back(my_sp);

  //static_link
  llvm::Value* static_val = tr::GetStaticLink(level, func_entry->level_->parent_);
  args.push_back(static_val);
  llvm::Value *call_val = nullptr;
  std::vector<llvm::Type *> types;
  types.push_back(ir_builder->getInt64Ty());
  types.push_back(ir_builder->getInt64Ty());
  for(absyn::Exp *e : arg_list){
    tr::ValAndTy *arg = e->Translate(venv, tenv, level, errormsg);
    args.push_back(arg->val_);
    types.push_back(arg->ty_->GetLLVMType());
  }
  //只需要调整空间尺寸，不用在caller处将实参拷贝到outgo空间，
  //而是使用llvm的调用命令传递实参，再由callee将接收到的参数拷贝到outgo空间里对应access的位置
  level->frame_->AllocOutgoSpace(args.size() * reg_manager->WordSize());

  llvm::FunctionType *func_ty = llvm::FunctionType::get(
      	result_ty->GetLLVMType(),
      	types, false);
  llvm::Function *func = llvm::Function::Create(func_ty,
    llvm::Function::ExternalLinkage, this->func_->Name(), ir_module);

  call_val = ir_builder->CreateCall(func, args);

  return new tr::ValAndTy(call_val, result_ty);
}

tr::ValAndTy *OpExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                               tr::Level *level,
                               err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  tr::ValAndTy *left_val_ty = nullptr;
  tr::ValAndTy *right_val_ty = nullptr;
  llvm::BasicBlock *origin_bb = ir_builder->GetInsertBlock();
  llvm::BasicBlock *right_last_bb = nullptr;
  llvm::Function *parentFunction = origin_bb->getParent();
  llvm::BasicBlock *rightBlock = llvm::BasicBlock::Create(ir_module->getContext(), "right_test", parentFunction);
  llvm::BasicBlock *nextBlock = llvm::BasicBlock::Create(ir_module->getContext(), "next_test", parentFunction);
  llvm::Value *flag1 = nullptr;
  llvm::Value *flag2 = nullptr;
  llvm::PHINode *phi_node = nullptr;
  llvm::Value *val = nullptr;
  llvm::FunctionType *string_equal_func_type = nullptr;
  
  llvm::Value *neq_val = nullptr;
  switch (this->oper_)
  {
  case absyn::AND_OP:
    /* code */
    //e1 AND e2 = if e1 then e2 else 0
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    origin_bb =  ir_builder->GetInsertBlock();
    flag1 = ir_builder->CreateICmpNE(left_val_ty->val_, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
    ir_builder->CreateCondBr(flag1, rightBlock, nextBlock);

    ir_builder->SetInsertPoint(rightBlock);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    right_last_bb = ir_builder->GetInsertBlock();
    flag2 = ir_builder->CreateICmpNE(right_val_ty->val_, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
    ir_builder->CreateBr(nextBlock);

    ir_builder->SetInsertPoint(nextBlock);
    phi_node = ir_builder->CreatePHI(llvm::Type::getInt64Ty(ir_module->getContext()), 2);
    phi_node->addIncoming(llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0), origin_bb);
    phi_node->addIncoming(flag2, right_last_bb);
    return new tr::ValAndTy(phi_node, type::IntTy::Instance());
  case absyn::OR_OP:
    /* code */
    //e1 OR e2 = if e1 then 1 else e2
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    origin_bb =  ir_builder->GetInsertBlock();
    flag1 = ir_builder->CreateICmpNE(left_val_ty->val_, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
    ir_builder->CreateCondBr(flag1, nextBlock, rightBlock);
    
    ir_builder->SetInsertPoint(rightBlock);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    right_last_bb = ir_builder->GetInsertBlock();
    flag2 = ir_builder->CreateICmpNE(right_val_ty->val_, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
    ir_builder->CreateBr(nextBlock);

    ir_builder->SetInsertPoint(nextBlock);
    phi_node = ir_builder->CreatePHI(llvm::Type::getInt64Ty(ir_module->getContext()), 2);
    phi_node->addIncoming(llvm::ConstantInt::get(ir_builder->getInt32Ty(), 1), origin_bb);
    phi_node->addIncoming(flag2, right_last_bb);
    return new tr::ValAndTy(phi_node, type::IntTy::Instance());
  case absyn::PLUS_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateNSWAdd(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::MINUS_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateNSWSub(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::TIMES_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateNSWMul(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::DIVIDE_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateSDiv(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
    
  case absyn::LT_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateICmpSLT(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::LE_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateICmpSLE(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::GT_OP:{
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateICmpSGT(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::GE_OP: {
    left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    val = ir_builder->CreateICmpSGE(left_val_ty->val_, right_val_ty->val_);
    return new tr::ValAndTy( val, type::IntTy::Instance());
  }
  case absyn::EQ_OP: {
     left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    if (left_val_ty->ty_->IsSameType(type::StringTy::Instance())){
      //just calls runtime–system function stringEqual

      val = ir_builder->CreateCall(string_equal,{left_val_ty->val_, right_val_ty->val_});
      
      return new tr::ValAndTy( val, type::IntTy::Instance());
    }
    else {
      val = ir_builder->CreateICmpEQ(left_val_ty->val_, right_val_ty->val_);
      return new tr::ValAndTy( val, type::IntTy::Instance());
    }
  }
  case absyn::NEQ_OP: {
     left_val_ty = this->left_->Translate(venv, tenv, level, errormsg);
    right_val_ty = this->right_->Translate(venv, tenv, level, errormsg);
    if (left_val_ty->ty_->IsSameType(type::StringTy::Instance())){
      //just calls runtime–system function stringEqual
      val = ir_builder->CreateCall(string_equal,{left_val_ty->val_, right_val_ty->val_});
      neq_val = ir_builder->CreateICmpNE(val, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
      return new tr::ValAndTy( neq_val, type::IntTy::Instance());
    }
    else {
      val = ir_builder->CreateICmpNE(left_val_ty->val_, right_val_ty->val_);
      return new tr::ValAndTy( val, type::IntTy::Instance());
    }
  }
  }
  return new tr::ValAndTy(llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0), type::IntTy::Instance());
}

tr::ValAndTy *RecordExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                   tr::Level *level,
                                   err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  type::Ty *record_type = tenv->Look(this->typ_)->ActualTy();
  std::list<type::Field *> record_formals_list = ((type::RecordTy *) record_type)->fields_->GetList();
  std::list<EField *> record_actuals_list = this->fields_->GetList();
  auto actual_start = record_actuals_list.cbegin();
  auto actual_end = record_actuals_list.cend();
  auto formal_start = record_formals_list.cbegin();
  auto formal_end = record_formals_list.cend();

  

  llvm::Value *sizeValue = ir_builder->getInt32(record_actuals_list.size() * reg_manager->WordSize());
  std::vector<llvm::Value*> args;
  args.push_back(sizeValue);

  llvm::Value *record_addr = ir_builder->CreateCall(alloc_record , args);
  llvm::Value *record_ptr = ir_builder->CreateIntToPtr(
          record_addr,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));
  int offset = 0;
  int wordSize = reg_manager->WordSize();
  for (; actual_start != actual_end && formal_start != formal_end; ++actual_start, ++formal_start) {
    //TODO
    EField *actual_field = *actual_start; // 表达式
    // 翻译当前字段的表达式
    tr::ValAndTy *field_val_ty = actual_field->exp_->Translate(venv, tenv, level, errormsg);
    // 计算字段在记录中的偏移量
    int field_offset = offset * wordSize;
    // 生成 GEP 指令以获取字段地址
    llvm::Value *field_ptr = ir_builder->CreateGEP(
        llvm::Type::getInt64Ty(ir_builder->getContext()), // 指针类型
        record_ptr, // 基地址
        llvm::ConstantInt::get(ir_builder->getInt32Ty(), field_offset) // 偏移量
    );
    // 存储字段的值
    ir_builder->CreateStore(field_val_ty->val_, field_ptr);
    offset++;
  }
  return new tr::ValAndTy(record_ptr, record_type);
}

tr::ValAndTy *SeqExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                tr::Level *level,
                                err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  std::list<absyn::Exp *> seqexp_list = this->seq_->GetList();
  if (seqexp_list.empty()) {
    return new tr::ValAndTy(NULL, type::VoidTy::Instance());
  }
  else if (seqexp_list.size() == 1) {
    return seqexp_list.front()->Translate(venv, tenv, level, errormsg);
  }
  tr::ValAndTy *result = nullptr;
  auto start = seqexp_list.cbegin();
  auto end = seqexp_list.cend();
  while (start != end)
  {
    /* code */
    result = (*start)->Translate(venv, tenv, level, errormsg);
    start++;
  }
  return result;
}

tr::ValAndTy *AssignExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                   tr::Level *level,
                                   err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  tr::ValAndTy *var_val_ty = this->var_->Translate(venv, tenv, level, errormsg);
  tr::ValAndTy *exp_val_ty = this->exp_->Translate(venv, tenv, level, errormsg);
  // llvm::Value *load_val = ir_builder->CreateLoad(exp_val_ty->ty_->GetLLVMType(), exp_val_ty->val_);
  ir_builder->CreateStore(exp_val_ty->val_, var_val_ty->val_);
  return new tr::ValAndTy(NULL, type::VoidTy::Instance());
}

tr::ValAndTy *IfExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                               tr::Level *level,
                               err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  llvm::BasicBlock *origin_bb = ir_builder->GetInsertBlock();
  //获取当前基本块的父函数
  llvm::Function *parentFunction = origin_bb->getParent();
  if(CheckBBTerminatorIsBranch(origin_bb)){
    //需要当前的BB是一个非条件分支指令
    //First build all BasicBlocks (BB)
    llvm::BasicBlock *testBlock = llvm::BasicBlock::Create(ir_module->getContext(), "if_test", parentFunction);
    llvm::BasicBlock *thenBlock = llvm::BasicBlock::Create(ir_module->getContext(), "if_then", parentFunction);
    llvm::BasicBlock *elseBlock = nullptr;
    if (this->elsee_ != nullptr) {
      elseBlock = llvm::BasicBlock::Create(ir_module->getContext(), "if_else_b", parentFunction);
    }
    llvm::BasicBlock *nextBlock = llvm::BasicBlock::Create(ir_module->getContext(), "if_next", parentFunction);
    ir_builder->CreateBr(testBlock);

    /*test block*/
    ir_builder->SetInsertPoint(testBlock);
    tr::ValAndTy *test_val_ty = this->test_->Translate(venv, tenv, level, errormsg);
    llvm::Value *icmp = ir_builder->CreateICmpNE(test_val_ty->val_, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
    llvm::Value *test_val = test_val_ty->val_;
    llvm::Value *cast_test_val = ir_builder->CreateCast(llvm::Instruction::SExt, test_val, llvm::Type::getInt32Ty(ir_module->getContext()));
    llvm::BasicBlock *test_last_bb = ir_builder->GetInsertBlock();
    ir_builder->CreateCondBr(icmp, thenBlock, elseBlock != nullptr ? elseBlock : nextBlock);
    /*then block*/
    ir_builder->SetInsertPoint(thenBlock);
    tr::ValAndTy *then_val_ty = this->then_->Translate(venv, tenv, level, errormsg);
    llvm::Value *then_val = then_val_ty->val_;
    llvm::Value *cast_then_val = ir_builder->CreateCast(llvm::Instruction::SExt, then_val, llvm::Type::getInt32Ty(ir_module->getContext()));
    llvm::BasicBlock *then_last_bb = ir_builder->GetInsertBlock();
    ir_builder->CreateBr(nextBlock); // 完成后跳转到 nextBlock

    tr::ValAndTy *else_val_ty = nullptr;
    llvm::BasicBlock *else_last_bb = nullptr;
    llvm::Value *else_val = nullptr;
    llvm::Value *cast_else_val = nullptr;
    // 如果存在 else 分支，处理 else block
    if (elseBlock) {
        ir_builder->SetInsertPoint(elseBlock);
        else_val_ty = this->elsee_->Translate(venv, tenv, level, errormsg);
        else_val = else_val_ty->val_;
        cast_else_val = ir_builder->CreateCast(llvm::Instruction::SExt, else_val, llvm::Type::getInt32Ty(ir_module->getContext()));
        else_last_bb = ir_builder->GetInsertBlock();
        ir_builder->CreateBr(nextBlock); // 完成后跳转到 nextBlock
    }
    
    // 处理合并块
    ir_builder->SetInsertPoint(nextBlock);
    llvm::PHINode *phi_node = ir_builder->CreatePHI(llvm::Type::getInt32Ty(ir_module->getContext()), 2);
    if(elseBlock){
      phi_node->addIncoming(cast_then_val, then_last_bb);
      phi_node->addIncoming(cast_else_val, else_last_bb);
    }
    else{
      phi_node->addIncoming(cast_then_val, then_last_bb);
      phi_node->addIncoming(cast_test_val, test_last_bb);
    }
    return new tr::ValAndTy(phi_node, type::IntTy::Instance());
  }
  else {
    return new tr::ValAndTy(NULL, type::VoidTy::Instance());
  }
}

tr::ValAndTy *WhileExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                  tr::Level *level,
                                  err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  /*
  test:
	if not(condition) goto done
	body
	goto test
  done:
  */
  llvm::BasicBlock *origin_bb = ir_builder->GetInsertBlock();
  llvm::Function *parentFunction = origin_bb->getParent();

  llvm::BasicBlock *testBlock = llvm::BasicBlock::Create(ir_module->getContext(), "while_test", parentFunction);
  llvm::BasicBlock *bodyBlock = llvm::BasicBlock::Create(ir_module->getContext(), "while_body", parentFunction);
  llvm::BasicBlock *doneBlock = llvm::BasicBlock::Create(ir_module->getContext(), "while_done", parentFunction);
  loop_stack.push(doneBlock);
  /*A break statement simply jump to done
  Maintain a std::stack<llvm::BasicBlock *> break_stack;
  When find a break, br to break_stack.top()
  */
  ir_builder->CreateBr(testBlock);
  /*test block*/
  ir_builder->SetInsertPoint(testBlock);
  tr::ValAndTy *test_val_ty = this->test_->Translate(venv, tenv, level, errormsg);
  llvm::BasicBlock *test_last_bb = ir_builder->GetInsertBlock();
  llvm::Value *flag = ir_builder->CreateICmpNE(test_val_ty->val_, llvm::ConstantInt::get(ir_builder->getInt32Ty(), 0));
  ir_builder->CreateCondBr(flag, bodyBlock, doneBlock);

  /*body block*/
  ir_builder->SetInsertPoint(bodyBlock);
  tr::ValAndTy *body_val_ty = this->body_->Translate(venv, tenv, level, errormsg);
  llvm::BasicBlock *body_last_bb = ir_builder->GetInsertBlock();
  ir_builder->CreateBr(testBlock);

  /*done block*/
  ir_builder->SetInsertPoint(doneBlock);
  loop_stack.pop();
  return new tr::ValAndTy(NULL, type::VoidTy::Instance());
}

tr::ValAndTy *ForExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                tr::Level *level,
                                err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  venv->BeginScope();
  llvm::BasicBlock *origin_bb = ir_builder->GetInsertBlock();
  llvm::Function *parentFunction = origin_bb->getParent();
  llvm::BasicBlock *testBlock = llvm::BasicBlock::Create(ir_module->getContext(), "for_test", parentFunction);
  llvm::BasicBlock *bodyBlock = llvm::BasicBlock::Create(ir_module->getContext(), "for_body", parentFunction);
  llvm::BasicBlock *doneBlock = llvm::BasicBlock::Create(ir_module->getContext(), "for_done", parentFunction);
  loop_stack.push(doneBlock);

  tr::Access *it_access = tr::Access::AllocLocal(level, this->escape_);
  tr::ValAndTy *low_val_ty = this->lo_->Translate(venv, tenv, level, errormsg);
  tr::ValAndTy *high_val_ty = this->hi_->Translate(venv, tenv, level, errormsg);

  venv->Enter(this->var_, new env::VarEntry(it_access, low_val_ty->ty_));
  llvm::Value *addr = it_access->access_->ToLLVMVal(level->get_sp());
  llvm::Value *it_ptr = ir_builder->CreateIntToPtr(
          addr,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));
  ir_builder->CreateStore(low_val_ty->val_ , it_ptr);
  //check low < high
  llvm::Value *flag_lh = ir_builder->CreateICmpSLT(low_val_ty->val_, high_val_ty->val_);
  ir_builder->CreateCondBr(flag_lh, testBlock, doneBlock);
  /*test block*/
  /*
  for_incre:                                        ; preds = %for_body
  %19 = load i32, i32* %18, align 4
  %20 = add i32 1, %19
  store i32 %20, i32* %18, align 4
  %21 = icmp sle i32 %20, %14
  br i1 %21, label %for_body, label %for_next
  */
  ir_builder->SetInsertPoint(testBlock);
  llvm::Value *load_it = ir_builder->CreateLoad(low_val_ty->ty_->GetLLVMType(), it_ptr);
  llvm::Value *it_add = ir_builder->CreateNSWAdd(load_it, llvm::ConstantInt::get(llvm::Type::getInt32Ty(ir_module->getContext()), 1), "24");
  ir_builder->CreateStore(it_add, it_ptr);
  llvm::Value *flag = ir_builder->CreateICmpSLE(it_add, high_val_ty->val_);
  ir_builder->CreateCondBr(flag, bodyBlock, doneBlock);

  /*body block*/
  ir_builder->SetInsertPoint(bodyBlock);
  tr::ValAndTy *body_val_ty = this->body_->Translate(venv, tenv, level, errormsg);
  ir_builder->CreateBr(testBlock);

  /*done block*/
  ir_builder->SetInsertPoint(doneBlock);
  loop_stack.pop();
  venv->EndScope();
  return new tr::ValAndTy(NULL, type::VoidTy::Instance());
}

tr::ValAndTy *BreakExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                  tr::Level *level,
                                  err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  llvm::BasicBlock *done = loop_stack.top();
  ir_builder->CreateBr(done);
  return new tr::ValAndTy(NULL, type::VoidTy::Instance());
}

tr::ValAndTy *LetExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                tr::Level *level,
                                err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  venv->BeginScope();
  tenv->BeginScope();
  for(Dec *dec : this->decs_->GetList()){
    dec->Translate(venv, tenv, level, errormsg);
  }
  tr::ValAndTy *body_val_ty = nullptr;
  if(!body_){
    body_val_ty = new tr::ValAndTy(NULL, type::VoidTy::Instance());
  }
  else {
    body_val_ty = body_->Translate(venv, tenv, level, errormsg);
  }
  tenv->EndScope();
  venv->EndScope();
  return body_val_ty;
}

tr::ValAndTy *ArrayExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                  tr::Level *level,
                                  err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  type::Ty *array_ty = tenv->Look(this->typ_);
  //type::Ty *element_ty = ((type::ArrayTy *) array_ty)->ty_->ActualTy();
  tr::ValAndTy *size_val_ty = this->size_->Translate(venv, tenv, level, errormsg);
  tr::ValAndTy *init_val_ty = this->init_->Translate(venv, tenv, level, errormsg);
  //%11 = call i64 @init_array(i32 %10, i64 0)

  llvm::Value *array_addr = ir_builder->CreateCall(init_array,{size_val_ty->val_, init_val_ty->val_});
  llvm::Value *array_ptr = ir_builder->CreateIntToPtr(
          array_addr,
          array_ty->GetLLVMType());
  return new tr::ValAndTy(array_ptr, array_ty->ActualTy());
}

tr::ValAndTy *VoidExp::Translate(env::VEnvPtr venv, env::TEnvPtr tenv,
                                 tr::Level *level,
                                 err::ErrorMsg *errormsg) const {
  /* TODO: Put your lab5-part1 code here */
  return new tr::ValAndTy(NULL, type::VoidTy::Instance());
}

} // namespace absyn