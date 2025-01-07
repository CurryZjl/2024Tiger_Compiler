#include "tiger/liveness/flowgraph.h"
#include <iostream>
namespace fg {

void FlowGraphFactory::AssemFlowGraph() {
  /* TODO: Put your lab6 code here */
  auto instr_list = this->instr_list_->GetList();
  FNodePtr last_node_p = nullptr;
  std::list<std::pair<FNodePtr, assem::Targets *>> jump_list;

  for(auto instr : instr_list){
    //控制流图，图节点是每一个指令
    FNodePtr new_node = this->flowgraph_->NewNode(instr);
    if(last_node_p){
      flowgraph_->AddEdge(last_node_p, new_node);
    }
    //如果当前指令是lable指令，需要记录到label_map_
    //Label instr
    if(typeid(*instr) == typeid(assem::LabelInstr)){
      last_node_p = new_node;
      label_map_->emplace(((assem::LabelInstr *)instr)->label_->Name(), new_node);
    }
    else if (typeid(*instr) == typeid(assem::OperInstr) && ((assem::OperInstr *) instr)->jumps_) {
      assem::OperInstr *jump_instr = (assem::OperInstr*) instr;
      std::string instr_str = jump_instr->assem_;
      //jmp
      if(instr_str.substr(0,3) == "jmp"){
        last_node_p = nullptr;
      } else {
      //conditional jump
        last_node_p = new_node;
      }
      assem::Targets *tars = jump_instr->jumps_;
      assert(tars != nullptr);
      jump_list.emplace_back(new_node, tars);
    }
    else {
      //非跳转情况，只需要记录上一个node
      last_node_p = new_node;
    }
  }
  for(auto jump_node : jump_list){
    std::vector<temp::Label *> *labels = jump_node.second->labels_;
    for(auto label : *labels){
      FNodePtr tar_p = label_map_->find(label->Name())->second;
      flowgraph_->AddEdge(jump_node.first, tar_p);
    }
  }
}

} // namespace fg

namespace assem {

temp::TempList *LabelInstr::Def() const { return new temp::TempList(); }

temp::TempList *MoveInstr::Def() const { return dst_; }

temp::TempList *OperInstr::Def() const { return dst_; }

temp::TempList *LabelInstr::Use() const { return new temp::TempList(); }

temp::TempList *MoveInstr::Use() const {
  return (src_) ? src_ : new temp::TempList();
}

temp::TempList *OperInstr::Use() const {
  return (src_) ? src_ : new temp::TempList();
}
} // namespace assem
