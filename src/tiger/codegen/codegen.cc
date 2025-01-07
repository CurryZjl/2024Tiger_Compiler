#include "tiger/codegen/codegen.h"

#include <cassert>
#include <iostream>
#include <sstream>

extern frame::RegManager *reg_manager;
extern frame::Frags *frags;

namespace {

constexpr int maxlen = 1024;

} // namespace

namespace cg {

void CodeGen::Codegen() {
  temp_map_ = new std::unordered_map<llvm::Value *, temp::Temp *>();
  bb_map_ = new std::unordered_map<llvm::BasicBlock *, int>();
  auto *list = new assem::InstrList();

  // firstly get all global string's location
  for (auto &&frag : frags->GetList()) {
    if (auto *str_frag = dynamic_cast<frame::StringFrag *>(frag)) {
      auto tmp = temp::TempFactory::NewTemp();
      list->Append(new assem::OperInstr(
          "leaq " + std::string(str_frag->str_val_->getName()) + "(%rip),`d0",
          new temp::TempList(tmp), new temp::TempList(), nullptr));
      temp_map_->insert({str_frag->str_val_, tmp});
    }
  }

  // move arguments to temp
  auto arg_iter = traces_->GetBody()->arg_begin();
  auto regs = reg_manager->ArgRegs();
  auto tmp_iter = regs->GetList().begin();

  // first arguement is rsp, we need to skip it
  ++arg_iter;

  for (; arg_iter != traces_->GetBody()->arg_end() &&
         tmp_iter != regs->GetList().end();
       ++arg_iter, ++tmp_iter) {
    auto tmp = temp::TempFactory::NewTemp();
    list->Append(new assem::OperInstr("movq `s0,`d0", new temp::TempList(tmp),
                                      new temp::TempList(*tmp_iter), nullptr));
    temp_map_->insert({static_cast<llvm::Value *>(arg_iter), tmp});
  }

  // pass-by-stack parameters
  if (arg_iter != traces_->GetBody()->arg_end()) {
    auto last_sp = temp::TempFactory::NewTemp();
    list->Append(
        new assem::OperInstr("movq %rsp,`d0", new temp::TempList(last_sp),
                             new temp::TempList(reg_manager->GetRegister(
                                 frame::X64RegManager::Reg::RSP)),
                             nullptr));
    list->Append(new assem::OperInstr(
        "addq $" + std::string(traces_->GetFunctionName()) +
            "_framesize_local,`s0",
        new temp::TempList(last_sp),
        new temp::TempList({last_sp, reg_manager->GetRegister(
                                         frame::X64RegManager::Reg::RSP)}),
        nullptr));
    while (arg_iter != traces_->GetBody()->arg_end()) {
      auto tmp = temp::TempFactory::NewTemp();
      list->Append(new assem::OperInstr(
          "movq " +
              std::to_string(8 * (arg_iter - traces_->GetBody()->arg_begin())) +
              "(`s0),`d0",
          new temp::TempList(tmp), new temp::TempList(last_sp), nullptr));
      temp_map_->insert({static_cast<llvm::Value *>(arg_iter), tmp});
      ++arg_iter;
    }
  }

  // construct bb_map
  int bb_index = 0;
  for (auto &&bb : traces_->GetBasicBlockList()->GetList()) {
    bb_map_->insert({bb, bb_index++});
  }

  for (auto &&bb : traces_->GetBasicBlockList()->GetList()) {
    // record every return value from llvm instruction
    for (auto &&inst : bb->getInstList())
      temp_map_->insert({&inst, temp::TempFactory::NewTemp()});
  }

  for (auto &&bb : traces_->GetBasicBlockList()->GetList()) {
    // Generate label for basic block
    list->Append(new assem::LabelInstr(std::string(bb->getName())));

    // Generate instructions for basic block
    for (auto &&inst : bb->getInstList())
      InstrSel(list, inst, traces_->GetFunctionName(), bb);
  }

  assem_instr_ = std::make_unique<AssemInstr>(frame::ProcEntryExit2(
      frame::ProcEntryExit1(traces_->GetFunctionName(), list)));
}

void AssemInstr::Print(FILE *out, temp::Map *map) const {
  for (auto instr : instr_list_->GetList())
    instr->Print(out, map);
  fprintf(out, "\n");
}

void CodeGen::InstrSel(assem::InstrList *instr_list, llvm::Instruction &inst,
                       std::string_view function_name, llvm::BasicBlock *bb) {
  // TODO: your lab5 code here

  switch (inst.getOpcode())
  {
    //1
    case llvm::Instruction::Load: {
        /* 
          %10 = load i32, i32* %N_ptr, align 4
        Get pointer value in load (%N_ptr)
        Get the corresponding temp from temp_map
          Key: %N_ptr; value: t102;
          Key: %10; value: t105
        Load from address value of t102 to t105
        movq (t102),t105

          %10 = load i64, i64* @b_framesize_global, align 4
         */
        llvm::LoadInst *loadInst = llvm::dyn_cast<llvm::LoadInst>(&inst);
        llvm::Value *ptr = loadInst->getPointerOperand();
        llvm::Type *ele_type = loadInst->getPointerOperandType()->getPointerElementType();

        auto dest_it = temp_map_->find(&inst);
        if (dest_it == temp_map_->end()) {
          throw std::runtime_error("Load instruction result not found in temp_map");
        }
        temp::Temp *dest_temp = dest_it->second;

        if(llvm::GlobalValue *global = llvm::dyn_cast<llvm::GlobalValue>(ptr)){
          std::string global_name = global->getName().str();
          instr_list->Append(new assem::OperInstr(
            "movq " + global_name + "(%rip), `d0",
            new temp::TempList(dest_temp), nullptr, nullptr));
        } else {
          auto src_it = temp_map_->find(ptr);
          if (src_it == temp_map_->end()) {
              throw std::runtime_error("Pointer operand not found in temp_map");
          }
          temp::Temp *src_temp = src_it->second;

          // 使用 movq 从内存地址加载值
          instr_list->Append(new assem::OperInstr(
              "movq (`s0), `d0",
              new temp::TempList(dest_temp), new temp::TempList(src_temp), nullptr));
        }
        break;
    }
    //2
    case llvm::Instruction::Add: {
        /* 
        %8 = add i64 %7, -8
        Get Operands of these instructions
          And map them to temporaries
        Using right assembly instruction according to type of operands (eg. addq or leaq)
         */
        llvm::BinaryOperator *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&inst);
        llvm::Value *op1 = binOp->getOperand(0);
        llvm::Value *op2 = binOp->getOperand(1);
        auto it1 = temp_map_->find(op1);
        auto it2 = temp_map_->find(op2);
        auto it3 = temp_map_->find(&inst);
        assert(it3 != temp_map_->end());
        temp::Temp *dest_temp = it3->second;
        //NOTE::区分操作数类型，决定是leaq还是addq  maybe wrong
        if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op1)){
          //如果第一个参数是常数
          //dest = 1 + src 
          int64_t constValue = constInt->getSExtValue();
          assert( it2 != temp_map_->end() );
          temp::Temp *src2_temp = it2->second; // 第二个操作数应该是临时变量
          //1. dest = c
          instr_list->Append(new assem::OperInstr(
          "movq $" + std::to_string(constValue) + ",`d0", new temp::TempList(dest_temp), nullptr, nullptr));
          //2. dest = dest + src
          instr_list->Append(new assem::OperInstr(
            "addq `s0, `d0", 
            new temp::TempList(dest_temp), new temp::TempList({src2_temp, dest_temp}), nullptr));
        }
        else if (llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op2)){
          //第二个参数是常数，很明显这是leaq指令 NOTE::初步认为只有add里面有leaq
          int64_t constValue = constInt->getSExtValue();
          //NOTE 
          assert( it1 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          instr_list->Append(new assem::OperInstr(
            "leaq " + std::to_string(constValue) + "(`s0), `d0", 
            new temp::TempList(dest_temp), new temp::TempList(src1_temp), nullptr));
        } else {
          //dest = src1 + src2
          assert(it1 != temp_map_->end() && it2 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          temp::Temp *src2_temp = it2->second;
          temp::Temp *dest_temp = it3->second;
          //1. dest = src1 我猜寄存器分配的时候会把这个move去掉
          instr_list->Append(new assem::MoveInstr(
          "movq `s0,`d0", new temp::TempList(dest_temp), new temp::TempList(src1_temp)));
          //2. dest = dest + src2
          instr_list->Append(new assem::OperInstr(
              "addq `s0, `d0", new temp::TempList(dest_temp), new temp::TempList({src2_temp, dest_temp}), nullptr));
        }
        
        break;
    }
    case llvm::Instruction::Sub: {
        /* code */
        llvm::BinaryOperator *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&inst);
        llvm::Value *op1 = binOp->getOperand(0);
        llvm::Value *op2 = binOp->getOperand(1);
        auto it1 = temp_map_->find(op1);
        auto it2 = temp_map_->find(op2);
        auto it3 = temp_map_->find(&inst);
        assert(it3 != temp_map_->end());
        temp::Temp *dest_temp = it3->second;
        //NOTE replace _sp with %rsp
        if(IsRsp(it3->first, function_name)){
          temp::Temp *rsp = reg_manager->GetRsp();
          temp_map_->erase(&inst);
          temp_map_->insert({&inst, rsp});
          dest_temp = rsp;
        }
       
        //NOTE::区分操作数类型
        if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op1)){
          //如果第一个参数是常数 dest = c - src2
          int64_t constValue = constInt->getSExtValue();
          assert(constValue == 0);//llvm input
          assert( it2 != temp_map_->end() );
          temp::Temp *src2_temp = it2->second; // 第二个操作数应该是临时变量
          //step1 move const to dest
          instr_list->Append(new assem::OperInstr(
          "movq $"+ std::to_string(constValue) +",`d0", new temp::TempList(dest_temp), nullptr, nullptr));
          //step2 dest = dest - src2
          instr_list->Append(new assem::OperInstr(
            "subq `s0, `d0", 
            new temp::TempList(dest_temp), new temp::TempList({src2_temp, dest_temp}), nullptr));
        }
        else if (llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op2)){
          //第二个参数是常数
          // %22 = sub i32 %21, 1
          int64_t constValue = constInt->getSExtValue();
          //NOTE
          assert( it1 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          instr_list->Append(new assem::MoveInstr(
          "movq `s0,`d0", new temp::TempList(dest_temp), new temp::TempList(src1_temp)));
          instr_list->Append(new assem::OperInstr(
            "subq $" + std::to_string(constValue) + ", `d0", 
            new temp::TempList(dest_temp), new temp::TempList(dest_temp), nullptr));
        } else {
          //dest = src1 - src2
          //special:: %_sp = sub %0, %framesize
          assert(it2 != temp_map_->end());
          if(it1 != temp_map_->end()){
            temp::Temp *src1_temp = it1->second;
            temp::Temp *src2_temp = it2->second;
            temp::Temp *dest_temp = it3->second;
            instr_list->Append(new assem::MoveInstr(
            "movq `s0,`d0", new temp::TempList(dest_temp), new temp::TempList(src1_temp)));
            instr_list->Append(new assem::OperInstr(
                "subq `s0, `d0", new temp::TempList(dest_temp), new temp::TempList({src2_temp, dest_temp}), nullptr));
          } else {
            //it1没有被记录，因为是%0代表rsp
            temp::Temp *src2_temp = it2->second;
            temp::Temp *rsp = reg_manager->GetRsp();
            instr_list->Append(new assem::OperInstr(
                "subq `s0, %rsp",new temp::TempList(rsp) , new temp::TempList({src2_temp, rsp}), nullptr));
          }
          
        }
        break;
    }
    case llvm::Instruction::Mul: {
        /* code */
        llvm::BinaryOperator *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&inst);
        llvm::Value *op1 = binOp->getOperand(0);
        llvm::Value *op2 = binOp->getOperand(1);
        auto it1 = temp_map_->find(op1);
        auto it2 = temp_map_->find(op2);
        auto it3 = temp_map_->find(&inst);
        assert(it3 != temp_map_->end());
        temp::Temp *dest_temp = it3->second;
        //NOTE::区分操作数类型
        if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op1)){
          //如果第一个参数是常数 dest = c * src2
          int64_t constValue = constInt->getSExtValue();
          assert( it2 != temp_map_->end() );
          temp::Temp *src2_temp = it2->second; // 第二个操作数应该是临时变量
          //step1 move const to dest
          instr_list->Append(new assem::OperInstr(
          "movq $"+ std::to_string(constValue) +",`d0", new temp::TempList(dest_temp), nullptr, nullptr));
          //step2 dest = dest * src2
          instr_list->Append(new assem::OperInstr(
            "imulq `s0, `d0", 
            new temp::TempList(dest_temp), new temp::TempList({src2_temp, dest_temp}), nullptr));
        }
        else if (llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op2)){
          //第二个参数是常数
          int64_t constValue = constInt->getSExtValue();
          //NOTE
          assert( it1 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          instr_list->Append(new assem::MoveInstr(
          "movq `s0,`d0", new temp::TempList(dest_temp), new temp::TempList(src1_temp)));
          instr_list->Append(new assem::OperInstr(
            "imulq $" + std::to_string(constValue) + ", `d0", 
            new temp::TempList(dest_temp), new temp::TempList(dest_temp) , nullptr));
        } else {
          //dest = src1 * src2
          assert(it1 != temp_map_->end() && it2 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          temp::Temp *src2_temp = it2->second;
          temp::Temp *dest_temp = it3->second;
          instr_list->Append(new assem::MoveInstr(
          "movq `s0,`d0", new temp::TempList(dest_temp), new temp::TempList(src1_temp)));
          instr_list->Append(new assem::OperInstr(
              "imulq `s0, `d0", new temp::TempList(dest_temp), new temp::TempList({src2_temp, dest_temp}), nullptr));
        }
        break;
    }
    case llvm::Instruction::SDiv: {
        /* code */
        llvm::BinaryOperator *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&inst);
        llvm::Value *op1 = binOp->getOperand(0);
        llvm::Value *op2 = binOp->getOperand(1);
        auto it1 = temp_map_->find(op1);
        auto it2 = temp_map_->find(op2);
        auto it3 = temp_map_->find(&inst);
        assert(it3 != temp_map_->end());
        temp::Temp *dest_temp = it3->second;
        //NOTE::区分操作数类型
        if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op1)){
          //如果第一个参数是常数 dest = c / src2
          int64_t constValue = constInt->getSExtValue();
          assert( it2 != temp_map_->end() );
          temp::Temp *src2_temp = it2->second; // 第二个操作数应该是临时变量
          temp::Temp *rax = reg_manager->GetRax();
          temp::Temp *rdx = reg_manager->GetRdx();
          //step1 move const to rax
          instr_list->Append(new assem::OperInstr(
          "movq $"+ std::to_string(constValue) +",%rax", new temp::TempList(rax), nullptr, nullptr));
          
          //step2 cqto before idivq
          instr_list->Append(new assem::OperInstr(
            "cqto", new temp::TempList(rdx), new temp::TempList(rax), nullptr));
          //step3 dest = rax / src2
          instr_list->Append(new assem::OperInstr(
            "idivq `s0", 
            new temp::TempList({rax, rdx}), new temp::TempList(src2_temp), nullptr));
          //step4 将商储存到dest中
           instr_list->Append(new assem::MoveInstr(
            "movq %rax, `d0", new temp::TempList(dest_temp), new temp::TempList(rax)));
        }
        else if (llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op2)){
          //第二个参数是常数
          int64_t constValue = constInt->getSExtValue();
          temp::Temp *rax = reg_manager->GetRax();
          //NOTE
          assert( it1 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          instr_list->Append(new assem::MoveInstr(
          "movq `s0, %rax", new temp::TempList(rax), new temp::TempList(src1_temp)));
          instr_list->Append(new assem::OperInstr(
            "cqto", nullptr, nullptr, nullptr));
          instr_list->Append(new assem::OperInstr(
            "idivq $" + std::to_string(constValue), 
            nullptr, nullptr, nullptr));
          instr_list->Append(new assem::MoveInstr(
            "movq %rax, `d0", new temp::TempList(dest_temp), new temp::TempList(rax)));
        } else {
          //dest = src1 / src2
          assert(it1 != temp_map_->end() && it2 != temp_map_->end());
          temp::Temp *src1_temp = it1->second;
          temp::Temp *src2_temp = it2->second;
          temp::Temp *dest_temp = it3->second;
          temp::Temp *rax = reg_manager->GetRax();
          instr_list->Append(new assem::MoveInstr(
          "movq `s0, %rax", new temp::TempList(rax), new temp::TempList(src1_temp)));
          instr_list->Append(new assem::OperInstr(
            "cqto", nullptr, nullptr, nullptr));
          instr_list->Append(new assem::OperInstr(
              "idivq `s0", nullptr, new temp::TempList(src2_temp), nullptr));
          instr_list->Append(new assem::MoveInstr(
            "movq %rax, `d0", new temp::TempList(dest_temp), new temp::TempList(rax)));
        }
        break;
    }
    //3
    case llvm::Instruction::PtrToInt: {
        /* code */
        //%13 = ptrtoint i64* %12 to i64
        llvm::PtrToIntInst *p2iInst = llvm::dyn_cast<llvm::PtrToIntInst>(&inst);
        llvm::Value *src = p2iInst->getOperand(0);
        llvm::Value *dst = &inst;
        auto src_it = temp_map_->find(src);
        auto dst_it = temp_map_->find(dst);
        if (src_it == temp_map_->end() || dst_it == temp_map_->end()) {
            throw std::runtime_error("Operands not found in tempmap");
        }
        instr_list->Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(dst_it->second), new temp::TempList(src_it->second)));
        break;
    }
    case llvm::Instruction::IntToPtr: {
        /* code */
        llvm::Value *src = inst.getOperand(0);
        llvm::Value *dst = &inst;
        auto src_it = temp_map_->find(src);
        auto dst_it = temp_map_->find(dst);
        if (src_it == temp_map_->end() || dst_it == temp_map_->end()) {
            throw std::runtime_error("Operands not found in tempmap");
        }
        instr_list->Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(dst_it->second), new temp::TempList(src_it->second)));
        break;
    }
    //4
    case llvm::Instruction::GetElementPtr: {
        /* code */
        //%3 = getelementptr i64, i64* %2, i64 %1
        /*movq t223,t225
          movq t224,%rax
          imul $8, %rax
          addq %rax,t225
        */
        llvm::GetElementPtrInst *gepInst = llvm::dyn_cast<llvm::GetElementPtrInst>(&inst);
        llvm::Value *basePtr = gepInst->getPointerOperand(); //基地址的指针
        auto baseIt = temp_map_->find(basePtr);
        if (baseIt == temp_map_->end()) {
            throw std::runtime_error("gep::Base pointer not found in temp_map");
        }
        temp::Temp *baseTemp = baseIt->second;

        // Initialize the result register
        auto resultIt = temp_map_->find(&inst);
        if (resultIt == temp_map_->end()) {
            throw std::runtime_error("gep::Result not found in temp_map");
        }
        temp::Temp *resultTemp = resultIt->second;
        //Copy the base pointer to the result register
        instr_list->Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(resultTemp), new temp::TempList(baseTemp)));
        // Process each index in the GEP
        //NOTE 参数处理比较复杂
        temp::Temp *rax = reg_manager->GetRax();
        if (gepInst->getNumIndices() == 1){
          llvm::Value *idx = gepInst->getOperand(1); // 索引是第二个操作数
          auto idxIt = temp_map_->find(idx);
          if (idxIt == temp_map_->end()) {
              throw std::runtime_error("Index not found in temp_map");
          }
          temp::Temp *idxTemp = idxIt->second;
          instr_list->Append(new assem::MoveInstr("movq `s0, %rax", new temp::TempList(rax) , new temp::TempList(idxTemp)));
          //NOTE should use getSize(gepInst->getSourceElementType());
          llvm::Type *idxType = gepInst->getOperand(1)->getType();
          uint32_t typeSize = 8;
         
          instr_list->Append(new assem::OperInstr("imulq $" + std::to_string(typeSize) + ", %rax", new temp::TempList(rax), new temp::TempList(rax), nullptr));
          // 将计算出的偏移量加到基地址上
          instr_list->Append(new assem::OperInstr("addq %rax, `d0", new temp::TempList(resultTemp), new temp::TempList({rax, resultTemp}), nullptr));
        } else if (gepInst->getNumIndices() == 2) {
          uint64_t totalOffset = 0;
          llvm::Value *idx1 = gepInst->getOperand(1);
          llvm::Value *idx2 = gepInst->getOperand(2);
          
          if (llvm::ConstantInt *constIdx = llvm::dyn_cast<llvm::ConstantInt>(idx1)) {
              assert(constIdx->getSExtValue() == 0);
              //totalOffset += 0;
          } else {
              throw std::runtime_error("Non-constant index1 in multi-index constant GEP");
          }
          if (llvm::ConstantInt *constIdx = llvm::dyn_cast<llvm::ConstantInt>(idx2)) {
            //NOTE
              if(constIdx->getSExtValue() == 1){
                totalOffset += 4;
              }
          } else {
              throw std::runtime_error("Non-constant index in multi-index constant GEP");
          }

          
          // 将总偏移量加到基地址上
          instr_list->Append(new assem::OperInstr("addq $" + std::to_string(totalOffset) + ", `d0", new temp::TempList(resultTemp), new temp::TempList(resultTemp), nullptr));
        } else {
          throw std::runtime_error("gep::indexs more than 2");
        }
        break;
    }
    //5
    case llvm::Instruction::Store: {
        /* code */
        //store i64 %13, i64* %17, align 4
        llvm::StoreInst *storeInst = llvm::dyn_cast<llvm::StoreInst>(&inst);
        llvm::Value *src = inst.getOperand(0);
        llvm::Value *dst = inst.getOperand(1);
        // 在tempmap中查找对应的临时寄存器
        auto dst_it = temp_map_->find(dst);
        if (dst_it == temp_map_->end()) {
          throw std::runtime_error("store::Dest not found in tempmap");
        }
        temp::Temp *dst_temp = dst_it->second;
        if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(src)){
          int64_t constValue = constInt->getSExtValue();
          instr_list->Append(new assem::OperInstr(
          "movq $" + std::to_string(constValue) + ", (`s0)",
            nullptr, new temp::TempList(dst_temp), nullptr));
        } else {
          auto src_it = temp_map_->find(src);
          if (src_it == temp_map_->end()) {
              throw std::runtime_error("store::Source operand not found in tempmap");
          }
          temp::Temp *src_temp = src_it->second;
          // 生成store汇编指令，将值存储到指针指向的内存地址
          instr_list->Append(new assem::OperInstr(
              "movq `s0, (`s1)",
              nullptr, new temp::TempList({src_temp, dst_temp}), nullptr));
        }
        break;
    }
    //6
    case llvm::Instruction::ZExt: {
        /* code */
        //%43 = zext i1 %42 to i32
        llvm::ZExtInst *zextInst = llvm::dyn_cast<llvm::ZExtInst>(&inst);
        llvm::Value *src = zextInst->getOperand(0);
        llvm::Value *dst = &inst;
        auto src_it = temp_map_->find(src);
        auto dst_it = temp_map_->find(dst);
        if (src_it == temp_map_->end() || dst_it == temp_map_->end()) {
            throw std::runtime_error("ZExt::Operands not found in temp_map_");
        }
        // 由于我们只支持movq，我们可以直接使用它来实现zext的效果
        // 因为movq会将源值直接复制到目标寄存器，对于zext来说，这正是我们需要的
        instr_list->Append(new assem::MoveInstr("movq `s0, `d0", new temp::TempList(dst_it->second), new temp::TempList(src_it->second)));
        break;
    }
    //7
    case llvm::Instruction::Call: {
        /* 
        %84 = call i32 @bsearch(i64 %bsearch_sp, i64 %83)
        Skip the first %bsearch_sp parameter
        Move all pass-by-stack values into stack
        Call the target function
        Get return value from %rax

        Hint: getCalledFunction()->getName() helps get the target function’s name
         */
        llvm::CallInst *callInst = llvm::dyn_cast<llvm::CallInst>(&inst);
        llvm::Function *calledFunc = callInst->getCalledFunction();
        if (!calledFunc) {
            throw std::runtime_error("Indirect function call is not supported");
        }
        std::string funcName = calledFunc->getName().str();
        
        auto regs = reg_manager->ArgRegs();
        auto tmp_iter = regs->GetList().begin();

        size_t paramCount = callInst->arg_size();
        size_t i = 0;
        // first arguement is rsp, we need to skip it
        if(
            funcName != "flush" && funcName != "exit" && funcName != "chr" &&
            funcName != "__wrap_getchar" && funcName != "print" && funcName != "printi" &&
            funcName != "ord" && funcName != "size" && funcName != "concat" &&
            funcName != "substring" && funcName != "alloc_record" && funcName != "init_array" &&
            funcName != "string_equal"
          ) {
            i++;
          }

        temp::TempList *use = new temp::TempList();
        auto caller_saved = reg_manager->CallerSaves();
        temp::TempList *def = new temp::TempList();
        for(auto r : caller_saved->GetList()){
          def->Append(r);
        }

        for (; i < paramCount &&
              tmp_iter != regs->GetList().end();
            ++i, ++tmp_iter) {
          
          use->Append(*tmp_iter);
          
          llvm::Value *argValue = callInst->getArgOperand(i);
          auto it = temp_map_->find(argValue);
          if (it == temp_map_->end()) {
            if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(argValue)){
              int64_t constValue = constInt->getSExtValue();
              instr_list->Append(new assem::OperInstr("movq $"+ std::to_string(constValue) + ", `d0", new temp::TempList(*tmp_iter),
                                            nullptr, nullptr));
            } else {
              throw std::runtime_error("Argument not found in temp_map");
            }
          } else {
            temp::Temp *argTemp = it->second;
            instr_list->Append(new assem::MoveInstr("movq `s0,`d0", new temp::TempList(*tmp_iter),
                                              new temp::TempList(argTemp)));
          }      
        }

        //Call the target function
        // For calls with return values
        if (!callInst->getType()->isVoidTy()) {
            auto it = temp_map_->find(&inst);
            if (it == temp_map_->end()) {
                throw std::runtime_error("Return value not found in temp_map");
            }
            temp::Temp *destTemp = it->second;
            temp::Temp *rax = reg_manager->GetRax();
            instr_list->Append(new assem::OperInstr("callq " + funcName, def, use, nullptr));
            // Move the return value from %rax to the destination temp
            instr_list->Append(new assem::MoveInstr("movq %rax, `d0", new temp::TempList(destTemp), new temp::TempList(rax)));
        } else {
            instr_list->Append(new assem::OperInstr("callq " + funcName, def, use, nullptr));
        }

        break;
    }
    //8
    case llvm::Instruction::Ret: {
        /* code */
        llvm::ReturnInst *retInst = llvm::dyn_cast<llvm::ReturnInst>(&inst);
        llvm::Value *retVal = retInst->getReturnValue();
        temp::Temp *rax = reg_manager->GetRax();
        if(retVal != nullptr){
          if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(retVal)){
            int64_t constValue = constInt->getSExtValue();
            instr_list->Append(new assem::OperInstr(
              "movq $" + std::to_string(constValue) + ", %rax",
                new temp::TempList(rax), nullptr, nullptr));
          } else {
            auto it = temp_map_->find(retVal);
            assert(it != temp_map_->end());
            temp::Temp *src_temp = it->second;
           
            instr_list->Append(new assem::MoveInstr("movq `s0, %rax", new temp::TempList(rax), new temp::TempList(src_temp)));
          }
        
        }
        std::string exitLabelName = std::string(function_name) + "_end";
        temp::Label *exit_label = temp::LabelFactory::NamedLabel(exitLabelName);
        std::vector<temp::Label*> *labels = new std::vector<temp::Label*>();
        labels->push_back(exit_label);
        assem::Targets *jumps = new assem::Targets(labels);
        instr_list->Append(new assem::OperInstr("jmp `j0", nullptr, nullptr, jumps));
        break;
    }
    //9
    case llvm::Instruction::Br: {
        /* code */
        temp::Temp *rax = reg_manager->GetRax();
        if(inst.getNumOperands() == 1){
          //br label %if_then
          llvm::Value *dest = inst.getOperand(0);
          assert(dest->getType()->isLabelTy() && "Expected a label as operand for unconditional br");
          std::string label_name = dest->getName().str();
          temp::Label *label = temp::LabelFactory::NamedLabel(label_name);
          std::vector<temp::Label*> *labels = new std::vector<temp::Label*>();
          labels->push_back(label);
          assem::Targets *jumps = new assem::Targets(labels);
          /*special for phi*/
          int bbIndex = bb_map_->at(bb);
          instr_list->Append(new assem::OperInstr(
              "movq $" + std::to_string(bbIndex) + ", %rax",
                new temp::TempList(rax), nullptr, nullptr));
          instr_list->Append(new assem::OperInstr("jmp `j0", nullptr, nullptr, jumps));
        } else if (inst.getNumOperands() == 3) {
          //br i1 %20, label %if_then, label %if_else
          /* 
          * Get the value of %20 (which is set in icmp instruction)
          * Compare with 1 or 0, and jump to the corresponding label
          */
          llvm::BranchInst *brInst = llvm::dyn_cast<llvm::BranchInst>(&inst);
          assert(brInst->isConditional());
          llvm::Value *cond = brInst->getCondition();
          llvm::Value *label_true_llvm = brInst->getSuccessor(0);
          llvm::Value *label_false_llvm = brInst->getSuccessor(1);
          assert(cond->getType()->isIntegerTy(1) && "Expected i1 as condition for conditional br");
          assert(label_true_llvm->getType()->isLabelTy() && label_false_llvm->getType()->isLabelTy() &&
                "Expected labels as operands for conditional br");

          auto it_cond = temp_map_->find(cond);
          if (it_cond == temp_map_->end()) {
            throw std::runtime_error("Condition not found in temp_map");
          }
          temp::Temp *cond_temp = it_cond->second;

          std::string label_true_name = label_true_llvm->getName().str();
          std::string label_false_name = label_false_llvm->getName().str();
          temp::Label *label_true = temp::LabelFactory::NamedLabel(label_true_name);
          temp::Label *label_false = temp::LabelFactory::NamedLabel(label_false_name);
          int bbIndex = bb_map_->at(bb);
          //生成比较和跳转指令
          instr_list->Append(new assem::OperInstr(
              "movq $" + std::to_string(bbIndex) + ", %rax",
                new temp::TempList(rax), nullptr, nullptr));
          instr_list->Append(new assem::OperInstr("cmpq $0, `s0", nullptr, new temp::TempList(cond_temp), nullptr));
          std::vector<temp::Label*> *labels_true = new std::vector<temp::Label*>();
          labels_true->push_back(label_true);
          assem::Targets *jumps_true = new assem::Targets(labels_true);
          instr_list->Append(new assem::OperInstr("jne `j0", nullptr, nullptr, jumps_true));
          std::vector<temp::Label*> *labels_false = new std::vector<temp::Label*>();
          labels_false->push_back(label_false);
          assem::Targets *jumps_false = new assem::Targets(labels_false);
          instr_list->Append(new assem::OperInstr("jmp `j0", nullptr, nullptr, jumps_false));
        } else {
          throw std::runtime_error("Invalid number of operands for br instruction");
        }
        break;
    }
    //10
    case llvm::Instruction::ICmp: {
        /* code */
        //%20 = icmp eq i64 %19, 0
        llvm::ICmpInst *icmpInst = llvm::dyn_cast<llvm::ICmpInst>(&inst);
        llvm::Value *op1 = icmpInst->getOperand(0);
        llvm::Value *op2 = icmpInst->getOperand(1);
        /*
          注意这里是反的 llvm指令里面，%d = icmp gt i32 %a %b 
          对应汇编会是 
          cmpq b a
          setg d
        */
        auto it1 = temp_map_->find(op1);
        auto it2 = temp_map_->find(op2);
        auto it3 = temp_map_->find(&inst);
        if (it1 == temp_map_->end() || it3 == temp_map_->end()) {
            throw std::runtime_error("ICmp::Operand1 or result not found in temp_map");
        }
        temp::Temp *src1_temp = it1->second;
        
        temp::Temp *dest_temp = it3->second;
        //NOTE::注意
        if(llvm::ConstantInt *constInt = llvm::dyn_cast<llvm::ConstantInt>(op2)){
          int64_t constValue = constInt->getSExtValue();
          instr_list->Append(new assem::OperInstr("cmpq $" +std::to_string(constValue) +", `s0 " , nullptr, new temp::TempList(src1_temp), nullptr));
        } else {
          assert(it2 != temp_map_->end());
          temp::Temp *src2_temp = it2->second;
          instr_list->Append(new assem::OperInstr("cmpq `s0, `s1", nullptr, new temp::TempList({src2_temp, src1_temp}), nullptr));
        }
      
        std::string setInstr;
        switch (icmpInst->getPredicate())
        {
        case llvm::CmpInst::ICMP_EQ:
            setInstr = "sete `d0";
            break;
        case llvm::CmpInst::ICMP_NE:
            setInstr = "setne `d0";
            break;
        case llvm::CmpInst::ICMP_UGT:
            setInstr = "setg `d0";
            break;
        case llvm::CmpInst::ICMP_UGE:
            setInstr = "setge `d0";
            break;
        case llvm::CmpInst::ICMP_ULT:
            setInstr = "setl `d0";
            break;
        case llvm::CmpInst::ICMP_ULE:
            setInstr = "setle `d0";
            break;
        case llvm::CmpInst::ICMP_SGT:
            setInstr = "setg `d0";
            break;
        case llvm::CmpInst::ICMP_SGE:
            setInstr = "setge `d0";
            break;
        case llvm::CmpInst::ICMP_SLT:
            setInstr = "setl `d0";
            break;
        case llvm::CmpInst::ICMP_SLE:
            setInstr = "setle `d0";
            break;
        default:
            throw std::runtime_error("Unsupported icmp predicate");
            break;
        }
        instr_list->Append(new assem::OperInstr("movq $0, `d0", new temp::TempList(dest_temp) , nullptr, nullptr));
        instr_list->Append(new assem::OperInstr(setInstr, new temp::TempList(dest_temp), nullptr, nullptr));
        break;
    }
    //11
    case llvm::Instruction::PHI: {
        /* code */
        llvm::PHINode *phiNode = llvm::dyn_cast<llvm::PHINode>(&inst);
        auto it = temp_map_->find(&inst);
        if(it == temp_map_->end()){
          throw std::runtime_error("phi::Return value not found in temp_map");
        }
        temp::Temp *dest_temp = it->second;
        temp::Temp *rax = reg_manager->GetRax();

        unsigned num = phiNode->getNumIncomingValues();
        assert(num == 2);
        llvm::BasicBlock *pred_bb1 = phiNode->getIncomingBlock(0);
        llvm::Value *incoming_value1 = phiNode->getIncomingValue(0);
        int pred_bb_index1 = bb_map_->at(pred_bb1);
        std::string label1Name = bb->getName().str() +"_phiindex" + std::to_string(pred_bb_index1) + "_phicode" + std::to_string(phi_unicode++);
        temp::Label *label1 = temp::LabelFactory::NamedLabel(label1Name);
        std::vector<temp::Label*> *labels1 = new std::vector<temp::Label*>();
        labels1->push_back(label1);
        assem::Targets *jumps1 = new assem::Targets(labels1);

        llvm::BasicBlock *pred_bb2 = phiNode->getIncomingBlock(1);
        llvm::Value *incoming_value2 = phiNode->getIncomingValue(1);
        int pred_bb_index2 = bb_map_->at(pred_bb2);
        std::string label2Name = bb->getName().str() +"_phiindex" + std::to_string(pred_bb_index2) + "_phicode" + std::to_string(phi_unicode++);
        temp::Label *label2 = temp::LabelFactory::NamedLabel(label2Name);
        std::vector<temp::Label*> *labels2 = new std::vector<temp::Label*>();
        labels2->push_back(label2);
        assem::Targets *jumps2 = new assem::Targets(labels2);

        std::string phiEndName = bb->getName().str() + "_phiend";
        temp::Label *label3 = temp::LabelFactory::NamedLabel(phiEndName);
        std::vector<temp::Label*> *labels3 = new std::vector<temp::Label*>();
        labels3->push_back(label3);
        assem::Targets *jumps3 = new assem::Targets(labels3);

        /*准备工作完成，开始生成指令*/
        
        //1. cmpq index1
        instr_list->Append(new assem::OperInstr(
              "cmpq $" + std::to_string(pred_bb_index1) + ", %rax",
              nullptr, new temp::TempList(rax), nullptr));
        //2. je label1
        instr_list->Append(new assem::OperInstr("je `j0", nullptr, nullptr, jumps1));
        //3. cmpq index2
        instr_list->Append(new assem::OperInstr(
              "cmpq $" + std::to_string(pred_bb_index2) + ", %rax",
              nullptr, new temp::TempList(rax), nullptr));
        //4. je label2
        instr_list->Append(new assem::OperInstr("je `j0", nullptr, nullptr, jumps2));
        //5. set label1
        instr_list->Append(new assem::LabelInstr(label1Name));
        //6. move value1 to dest
        if(llvm::ConstantInt *constInt1 = llvm::dyn_cast<llvm::ConstantInt>(incoming_value1)){
          int64_t constValue = constInt1->getSExtValue();
          instr_list->Append(new assem::OperInstr(
              "movq $" + std::to_string(constValue) + ", `d0",
              new temp::TempList(dest_temp), nullptr, nullptr));
        } else {
          auto iti = temp_map_->find(incoming_value1);
          if (iti == temp_map_->end()) {
              throw std::runtime_error("PHI incoming value1 not found in temp_map");
          }
          temp::Temp *src_temp = iti->second;
          instr_list->Append(new assem::MoveInstr(
              "movq `s0, `d0",
              new temp::TempList(dest_temp), new temp::TempList(src_temp)));
        }
        //7. jmp to end
        instr_list->Append(new assem::OperInstr("jmp `j0", nullptr, nullptr, jumps3));
        //8. set label2
        instr_list->Append(new assem::LabelInstr(label2Name));
        //9. move value2 to dest
        if(llvm::ConstantInt *constInt2 = llvm::dyn_cast<llvm::ConstantInt>(incoming_value2)){
          int64_t constValue = constInt2->getSExtValue();
          instr_list->Append(new assem::OperInstr(
              "movq $" + std::to_string(constValue) + ", `d0",
              new temp::TempList(dest_temp), nullptr, nullptr));
        } else {
          auto iti = temp_map_->find(incoming_value2);
          if (iti == temp_map_->end()) {
            //throw std::runtime_error("PHI incoming value2 not found in temp_map");
            //assert(incoming_value2 == NULL);
            instr_list->Append(new assem::OperInstr(
              "movq $0, `d0",
              new temp::TempList(dest_temp), nullptr, nullptr));
          } else {
            temp::Temp *src_temp = iti->second;
            instr_list->Append(new assem::MoveInstr(
                "movq `s0, `d0",
                new temp::TempList(dest_temp), new temp::TempList(src_temp)));
          }
       
        }
        //10. jmp to end
        instr_list->Append(new assem::OperInstr("jmp `j0", nullptr, nullptr, jumps3));
        //11. set end
        instr_list->Append(new assem::LabelInstr(phiEndName));
        break;
    }
    default:
      throw std::runtime_error(std::string("Unknown instruction: ") +
                           inst.getOpcodeName());
      break;
  }
}

} // namespace cg