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

temp::Temp *X64RegManager::GetRax() { return regs_[RAX]; }

temp::Temp *X64RegManager::GetRsp() { return regs_[RSP]; }

class InFrameAccess : public Access {
public:
  int offset;
  frame::Frame *parent_frame;

  explicit InFrameAccess(int offset, frame::Frame *parent)
      : offset(offset), parent_frame(parent) {}

  /* TODO: Put your lab5-part1 code here */
  /*使用staticlink的情况*/
  llvm::Value *ToLLVMVal(llvm::Value *frame_addr) const override{
    llvm::Value *frame_offset = llvm::ConstantInt::get(llvm::Type::getInt64Ty(ir_module->getContext()), offset);
    llvm::Value *access = ir_builder->CreateNSWAdd(frame_addr, frame_offset);
    return access;
  }

  /*不使用staticlink的情况，直接拿当前栈帧的变量addr*/
  llvm::Value *ToLLVMVal() const override{
    llvm::Value *frame_offset = llvm::ConstantInt::get(llvm::Type::getInt64Ty(ir_module->getContext()), offset);
    llvm::Value *access = ir_builder->CreateNSWAdd(parent_frame->sp, frame_offset);
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
  size_t size = formals.size();
  std::list<Access *> *outgo = new std::list<Access*>;
  assert(name != nullptr);
  //创建新函数时，这个新函数对应这个frame。同时有参数表outgo部分。
  frame::Frame *frame = new X64Frame(name, outgo);
  int acc_off = 0;
  for(int i = 0; i < size; i++){
    acc_off += 8;
    //这些参数对应自己的offset。而且它们的附属栈帧是callee的栈帧。
    //这样就可以用callee->frame->get_sp() + frame_access_offset拿到参数对应在栈上的地址
    frame::Access *access = new InFrameAccess(acc_off, frame);
    outgo->push_back(access);
  }
  
  return frame;
}

/**
 * Moving incoming formal parameters, the saving and restoring of callee-save
 * Registers
 * @param frame curruent frame
 * @param stm statements
 * @return statements with saving, restoring and view shift
 */
assem::InstrList *ProcEntryExit1(std::string_view function_name,
                                 assem::InstrList *body) {
  // TODO: your lab5 code here
  /* Store instructions to save any callee-saved registers- including the return address register – used within the function
     Load instructions to restore the callee-save registers
  */
 /*movq %r15,t139
  movq %r14,t138
  movq %r13,t137
  movq %r12,t136
  movq %rbx,t135
  movq %rbp,t134

  ...

  movq t134,%rbp
  movq t135,%rbx
  movq t136,%r12
  movq t137,%r13
  movq t138,%r14
  movq t139,%r15
  */
  if(function_name == "tigermain"){
    body->Append(new assem::LabelInstr(std::string(function_name) + "_end"));
    return body;
  }
  temp::TempList *calleeTemps = reg_manager->CalleeSaves();
  size_t size = calleeTemps->GetList().size();
  auto calleeRegsList = calleeTemps->GetList();
  assert(size == 6);
  temp::Temp *r15Tmp = temp::TempFactory::NewTemp();
  temp::Temp *r14Tmp = temp::TempFactory::NewTemp();
  temp::Temp *r13Tmp = temp::TempFactory::NewTemp();
  temp::Temp *r12Tmp = temp::TempFactory::NewTemp();
  temp::Temp *rbxTmp = temp::TempFactory::NewTemp();
  temp::Temp *rbpTmp = temp::TempFactory::NewTemp();
  temp::TempList temps({rbpTmp, rbxTmp, r12Tmp, r13Tmp, r14Tmp, r15Tmp});
  auto tempList = temps.GetList();

  for(auto it = calleeRegsList.begin() , it2 = tempList.begin(); it != calleeRegsList.end() && it2 != tempList.end(); it++, it2++){
    //NOTE::回来看是不是应该用MoveIns而不是OperIns
    body->Insert(body->GetList().begin(), new assem::MoveInstr("movq `s0,`d0",  new temp::TempList(*it2), new temp::TempList(*it)));
  }

  body->Append(new assem::LabelInstr(std::string(function_name) + "_end"));
  for(auto it = calleeRegsList.begin() , it2 = tempList.begin(); it != calleeRegsList.end() && it2 != tempList.end(); it++, it2++){
    body->Append(new assem::MoveInstr("movq `s0,`d0",  new temp::TempList(*it), new temp::TempList(*it2)));
  }
  return body;
}

/**
 * Appends a “sink” instruction to the function body to tell the register
 * allocator that certain registers are live at procedure exit
 * @param body function body
 * @return instructions with sink instruction
 */
assem::InstrList *ProcEntryExit2(assem::InstrList *body) {
  body->Append(new assem::OperInstr("", new temp::TempList(),
                                    reg_manager->ReturnSink(), nullptr));
  return body;
}

/**
 * The procedure entry/exit sequences
 * @param frame the frame of current func
 * @param body current function body
 * @return whole instruction list with prolog_ end epilog_
 */
assem::Proc *ProcEntryExit3(std::string_view function_name,
                            assem::InstrList *body) {
  std::string prologue = "";
  std::string epilogue = "";

  // TODO: your lab5 code here
  //p120 1 2 3 9 10 11
  /*
  tigermain:
  movq tigermain_framesize_global(%rip), %rax
  subq %rax,%rsp
  …
  
  movq tigermain_framesize_global(%rip), %rdi
  addq %rdi,%rsp
  retq
  */
  std::string fn(function_name);
  prologue += fn + ":\n";
  //part1的代码已经手动实现了减去栈的指令
  // prologue += "movq " + fn + "_framesize_global(%rip), %rax\n";
  // prologue += "subq %rax, %rsp\n";

  epilogue += "movq " + fn + "_framesize_global(%rip), %rdi\n";
  epilogue += "addq %rdi, %rsp\n";
  epilogue += "retq\n";

  return new assem::Proc(prologue, body, epilogue);
}

void Frags::PushBack(Frag *frag) { frags_.emplace_back(frag); }

} // namespace frame