#include "tiger/frame/x64frame.h"
#include "tiger/env/env.h"

#include <iostream>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>
#include <llvm/IR/Value.h>

extern frame::RegManager *reg_manager;
extern llvm::IRBuilder<> *ir_builder;
extern llvm::Module *ir_module;

namespace frame {

X64RegManager::X64RegManager() : RegManager() {
  for (int i = 0; i < REG_COUNT; i++)
    regs_.push_back(temp::TempFactory::NewTemp());

  // Note: no frame pointer in tiger compiler
  std::array<std::string_view, REG_COUNT> reg_name{
      "%rax", "%rbx", "%rcx", "%rdx", "%rsi", "%rdi", "%rbp", "%rsp",
      "%r8",  "%r9",  "%r10", "%r11", "%r12", "%r13", "%r14", "%r15"};
  int reg = RAX;
  for (auto &name : reg_name) {
    temp_map_->Enter(regs_[reg], new std::string(name));
    reg++;
  }
}

temp::TempList *X64RegManager::Registers() {
  const std::array reg_array{
      RAX, RBX, RCX, RDX, RSI, RDI, RBP, R8, R9, R10, R11, R12, R13, R14, R15,
  };
  auto *temp_list = new temp::TempList();
  for (auto &reg : reg_array)
    temp_list->Append(regs_[reg]);
  return temp_list;
}

temp::TempList *X64RegManager::ArgRegs() {
  const std::array reg_array{RDI, RSI, RDX, RCX, R8, R9};
  auto *temp_list = new temp::TempList();
  ;
  for (auto &reg : reg_array)
    temp_list->Append(regs_[reg]);
  return temp_list;
}

temp::TempList *X64RegManager::CallerSaves() {
  std::array reg_array{RAX, RDI, RSI, RDX, RCX, R8, R9, R10, R11};
  auto *temp_list = new temp::TempList();
  ;
  for (auto &reg : reg_array)
    temp_list->Append(regs_[reg]);
  return temp_list;
}

temp::TempList *X64RegManager::CalleeSaves() {
  std::array reg_array{RBP, RBX, R12, R13, R14, R15};
  auto *temp_list = new temp::TempList();
  ;
  for (auto &reg : reg_array)
    temp_list->Append(regs_[reg]);
  return temp_list;
}

temp::TempList *X64RegManager::ReturnSink() {
  temp::TempList *temp_list = CalleeSaves();
  temp_list->Append(regs_[SP]);
  temp_list->Append(regs_[RV]);
  return temp_list;
}

int X64RegManager::WordSize() { return 8; }

temp::Temp *X64RegManager::FramePointer() { return regs_[FP]; }

class InFrameAccess : public Access {
public:
  int offset;
  frame::Frame *parent_frame;

  explicit InFrameAccess(int offset, frame::Frame *parent)
      : offset(offset), parent_frame(parent) {}

  /* TODO: Put your lab5-part1 code here */
  /*返回该InFrameAccess的地址的int值，注意之后要使用CreateIntToPtr
  eg::llvm::Value *static_link_ptr = ir_builder->CreateIntToPtr(
          static_link_addr,
          llvm::Type::getInt64PtrTy(ir_builder->getContext()));*/
  llvm::Value *ToLLVMVal(llvm::Value *frame_addr_ptr) const override{
    llvm::Value *load_frame_size = ir_builder->CreateLoad(ir_builder->getInt64Ty(), parent_frame->framesize_global);
    llvm::Value *frame_offset = ir_builder->CreateNSWAdd(frame_addr_ptr, llvm::ConstantInt::get(llvm::Type::getInt32Ty(ir_module->getContext()), offset));
    llvm::Value *access = ir_builder->CreateNSWAdd(frame_addr_ptr, frame_offset);
    return access;
  }
};


class X64Frame : public Frame {
public:
  //X64的Frame。分配过程中默认预留outgo_size_=8，而一开始没有局部变量，所以offset_=0
  X64Frame(temp::Label *name, std::list<frame::Access *> *formals)
      : Frame(8, 0, name, formals) {}

  [[nodiscard]] std::string GetLabel() const override { return name_->Name(); }
  [[nodiscard]] temp::Label *Name() const override { return name_; }
  [[nodiscard]] std::list<frame::Access *> *Formals() const override {
    return formals_;
  }
  frame::Access *AllocLocal(bool escape) override {
    frame::Access *access;

    offset_ -= reg_manager->WordSize(); //分配InFrameAccess时需要注意调整frame的offset_
    access = new InFrameAccess(offset_, this);

    return access;
  }
  void AllocOutgoSpace(int size) override {
    if (size > outgo_size_)
      outgo_size_ = size;
  }
};

//formals是表示参数是否escape的列表，true表示escape，false表示non-escape
frame::Frame *NewFrame(temp::Label *name, std::list<bool> formals) {
  /* TODO: Put your lab5-part1 code here */
  //size_t size = formals.size() < 1 ? 1 : formals.size();
  size_t size = formals.size();
  std::list<Access *> *outgo = new std::list<Access*>;
  frame::Frame *frame = new X64Frame(name, outgo);
  int acc_off = 0;
  for(int i = 0; i < size; i++){
    acc_off += 8;
    frame::Access *access = new InFrameAccess(acc_off, frame);
    outgo->push_back(access);
  }
  
  return frame;
}


} // namespace frame