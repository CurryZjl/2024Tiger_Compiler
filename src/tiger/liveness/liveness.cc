#include "tiger/liveness/liveness.h"

extern frame::RegManager *reg_manager;

namespace live {

bool MoveList::Contain(INodePtr src, INodePtr dst) {
  return std::any_of(move_list_.cbegin(), move_list_.cend(),
                     [src, dst](std::pair<INodePtr, INodePtr> move) {
                       return move.first == src && move.second == dst;
                     });
}

void MoveList::Delete(INodePtr src, INodePtr dst) {
  assert(src && dst);
  auto move_it = move_list_.begin();
  for (; move_it != move_list_.end(); move_it++) {
    if (move_it->first == src && move_it->second == dst) {
      break;
    }
  }
  move_list_.erase(move_it);
}

MoveList *MoveList::Union(MoveList *list) {
  auto *res = new MoveList();
  for (auto move : move_list_) {
    res->move_list_.push_back(move);
  }
  for (auto move : list->GetList()) {
    if (!res->Contain(move.first, move.second))
      res->move_list_.push_back(move);
  }
  return res;
}

MoveList *MoveList::Intersect(MoveList *list) {
  auto *res = new MoveList();
  for (auto move : list->GetList()) {
    if (Contain(move.first, move.second))
      res->move_list_.push_back(move);
  }
  return res;
}

bool Contain(temp::Temp *reg, temp::TempList *list) {
  if (list == nullptr) 
    return false;
  std::list<temp::Temp *> tmp = list->GetList();
 
  for (auto t : tmp) {
    if (reg == t) {
      return true;
    }
  }
  return false;
}


//return dst - src
temp::TempList *Subtract(temp::TempList *src, temp::TempList *dst) {
  temp::TempList *result = new temp::TempList();
  if (dst == nullptr) 
    return result;
  for (auto t_dst : dst->GetList()) {
    if (!Contain(t_dst, src))
      result->Append(t_dst);
  }
  return result;
}

temp::TempList *Union(temp::TempList *list1, temp::TempList *list2) {
  temp::TempList *result = new temp::TempList();
  if (list2 != nullptr) {
    for (auto t : list2->GetList())
      result->Append(t);
  }

  if (list1 != nullptr) {
    for (auto t : list1->GetList()) {
      if (!Contain(t, list2))
        result->Append(t);
    }
  }
  return result;
}

bool Equal(temp::TempList *list1, temp::TempList *list2) {
  std::list<temp::Temp *> tmp1 = list1->GetList();
  std::list<temp::Temp *> tmp2 = list2->GetList();
  /* Check size first */
  if (tmp1.size() != tmp2.size()) 
    return false;
  /* Then compare each item in list1 and list2 */
  for (auto t1 : tmp1) {
    bool is_find = false;
    for (auto t2 : tmp2) {
      if (t1 == t2) {
        is_find = true;
        break;
      }
    }
    if (!is_find) 
      return false;
  }
  return true;
}

void LiveGraphFactory::LiveMap() {
  /* TODO: Put your lab6 code here */
  auto nodes_list = flowgraph_->Nodes()->GetList();
  //init
  for(auto node : nodes_list){
    in_->Enter(node, new temp::TempList());
    out_->Enter(node, new temp::TempList());
  }
  /*
   in(n) = use(n) Union (out(n) - def(n))
   out(n) = Union(all succ) in(s)
  */
  while (1)
  {
    bool flag = true;
    for(auto node : nodes_list){
      temp::TempList *last_in = in_->Look(node);
      temp::TempList *last_out = out_->Look(node);

      temp::TempList *new_in_def = node->NodeInfo()->Def();
      temp::TempList *new_in_use = node->NodeInfo()->Use();
      temp::TempList *new_in = Union(new_in_use, Subtract(new_in_def, last_out));
      temp::TempList *new_out = new temp::TempList();
      for(auto succ : (*node).Succ()->GetList()){
        temp::TempList *succ_node_in = in_->Look(succ);
        assert(succ_node_in != nullptr);
        temp::TempList *tmp = Union(new_out, succ_node_in);
        //delete new_out;
        new_out = tmp;
      }
      //有任何一次不相等都要进行下一次迭代
      if(!Equal(last_in, new_in) || !Equal(last_out, new_out))
        flag = false;
      in_->Set(node, new_in);
      out_->Set(node, new_out);

      delete last_in;
      delete last_out;
    }
    if(flag)
      break;
  }
  
}

void LiveGraphFactory::InterfGraph() {
  /* TODO: Put your lab6 code here */
  temp::TempList *regs = reg_manager->Registers();
  auto regs_list = regs->GetList();
  regs_list.emplace_back(reg_manager->GetRsp());

  //首先建立所有机器寄存器之间的预着色冲突关系
  for(auto reg : regs_list){
    INodePtr new_node = live_graph_.interf_graph->NewNode(reg);
    temp_node_map_->Enter(reg, new_node);
  }
  for(auto reg_it = regs_list.begin(); reg_it != regs_list.end(); ++reg_it){
    for(auto reg_it_next = std::next(reg_it); reg_it_next != regs_list.end(); ++reg_it_next){
      INodePtr reg_it_p = temp_node_map_->Look(*reg_it);
      INodePtr reg_it_next_p = temp_node_map_->Look(*reg_it_next);
      live_graph_.interf_graph->AddEdge(reg_it_p, reg_it_next_p);
      live_graph_.interf_graph->AddEdge(reg_it_next_p, reg_it_p);
    }
  }
  
  //create all new nodes in interf_graph
  auto nodes_list = flowgraph_->Nodes()->GetList();
  INodePtr rsp_p = temp_node_map_->Look(reg_manager->GetRsp());
  assert(rsp_p != nullptr);
  for(auto node : nodes_list){
    temp::TempList *def_templist = node->NodeInfo()->Def();
    if(def_templist != nullptr){
      for(auto def_temp : def_templist->GetList()){
        INodePtr new_node_p = temp_node_map_->Look(def_temp);
        if(new_node_p == nullptr){
          new_node_p = live_graph_.interf_graph->NewNode(def_temp);
          temp_node_map_->Enter(def_temp, new_node_p);
          // std::printf("Create INode for deftemp: %d \n", new_node_p->NodeInfo()->Int());
          // std::fflush(stdout);
        }

        if(def_temp != reg_manager->GetRsp()){
          live_graph_.interf_graph->AddEdge(new_node_p, rsp_p);
          live_graph_.interf_graph->AddEdge(rsp_p, new_node_p);
        }
      }
    }
    
    temp::TempList *use_templist = node->NodeInfo()->Use();
    if(use_templist != nullptr){
      for(auto use_temp : use_templist->GetList()){
        INodePtr new_node_p = temp_node_map_->Look(use_temp);
        if(new_node_p == nullptr){
          new_node_p = live_graph_.interf_graph->NewNode(use_temp);
          temp_node_map_->Enter(use_temp, new_node_p);
          std::printf("Create INode for usetemp: %d \n", new_node_p->NodeInfo()->Int());
          std::fflush(stdout);
        }

        if(use_temp != reg_manager->GetRsp()){
          live_graph_.interf_graph->AddEdge(new_node_p, rsp_p);
          live_graph_.interf_graph->AddEdge(rsp_p, new_node_p);
        }
      }
    } 
  }

  //add edges
  for(auto node : nodes_list){
    assem::Instr *node_instr = node->NodeInfo();
    temp::TempList *out_templist = out_->Look(node);
    //非move的，out和def冲突
    if(typeid(*node_instr) != typeid(assem::MoveInstr)){
      temp::TempList *node_def = node_instr->Def();
      if(node_def == nullptr)
        continue;
      for(auto def : node_def->GetList()){
        for(auto out_temp : out_templist->GetList()){
          INodePtr def_node = temp_node_map_->Look(def);
          INodePtr out_temp_node = temp_node_map_->Look(out_temp);
          live_graph_.interf_graph->AddEdge(def_node, out_temp_node);
          live_graph_.interf_graph->AddEdge(out_temp_node, def_node);
        }
      }
    }
    else {
      //MoveInstr
      temp::TempList *node_def = node_instr->Def();
      temp::TempList *node_use = node_instr->Use();
      temp::TempList *out_subuse = Subtract(node_use, out_templist);
      assert(node_def != nullptr);
      for(auto def : node_def->GetList()){
        INodePtr def_node = temp_node_map_->Look(def);
        //NOTE
        assert(def_node != nullptr);
        for(auto temp_it : out_subuse->GetList()){
          INodePtr temp_it_node = temp_node_map_->Look(temp_it);
          live_graph_.interf_graph->AddEdge(def_node, temp_it_node);
          live_graph_.interf_graph->AddEdge(temp_it_node, def_node);
        }
      }

      //Add move edges
      assert(node_def->GetList().size() == 1);
      assert(node_use->GetList().size() == 1);
      temp::Temp *dest_temp = node_def->NthTemp(0);
      temp::Temp *use_temp = node_use->NthTemp(0);
      live_graph_.moves->Append(temp_node_map_->Look(use_temp), temp_node_map_->Look(dest_temp));

    }
  }

}

void LiveGraphFactory::Liveness() {
  LiveMap();
  InterfGraph();
}

} // namespace live