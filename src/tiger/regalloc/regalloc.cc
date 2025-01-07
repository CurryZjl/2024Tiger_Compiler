#include "tiger/regalloc/regalloc.h"

#include "tiger/output/logger.h"
#include <iostream>

extern frame::RegManager *reg_manager;
extern std::map<std::string, std::pair<int, int>> frame_info_map;

int count = 0;

namespace ra {
/* TODO: Put your lab6 code here */

RegAllocator::RegAllocator(std::string body_name_str_, std::unique_ptr<cg::AssemInstr> assem_instr_) : body_name_str_(std::move(body_name_str_)), assem_instr(std::move(assem_instr_)){
    result = std::make_unique<Result>();
    //不需要在这里初始化各种变量，因为可能会有多次rewrite后的迭代
}

std::unique_ptr<Result> RegAllocator::TransferResult(){
    result->il_ = assem_instr->GetInstrList();
    result->coloring_ = temp::Map::Empty();
    for(auto nodePair : colorMap){
        result->coloring_->Enter(nodePair.first->NodeInfo(), nodePair.second);
    }
    return std::move(result);
}

void RegAllocator::RegAlloc() {
    Build();
    MakeWorklist();
    while(!simplifyWorklist->GetList().empty() || !worklistMoves->GetList().empty() ||
    !freezeWorklist->GetList().empty() || !spillWorklist->GetList().empty())
    {
        if(!simplifyWorklist->GetList().empty()){
            Simplify();
        } else if (!worklistMoves->GetList().empty()) {
            Coalesce();
        } else if (!freezeWorklist->GetList().empty()) {
            Freeze();
        } else if (!spillWorklist->GetList().empty()) {
            SelectSpill();
        }
    }
    AssignColor();
    if(!spilledNodes->GetList().empty()){
        RewriteProgram();
        RegAlloc();
    }
}

void RegAllocator::Build() {
    /*	
    forall b∈blocks in program
        let live = liveOut(b)
        forall  I∈instruction(b) in reverse order
            if isMoveInstruction(I) then 
                live ← live\use(I)
                forall n∈def(I)∪use(I)
                    moveList[n] ← moveList[n]∪{I}
            workListMoves ← workListMoves∪{I}
            live ← live∪def(I)
            forall d∈def(I)
                forall l∈live
                    AddEdge(l, d)
            live ← use(I)∪(live\def(I))
    */
    /* Liveness Analysis */
    fg::FlowGraphFactory *flowGraphFactory = new fg::FlowGraphFactory(this->assem_instr->GetInstrList());
    flowGraphFactory->AssemFlowGraph();
    fg::FGraphPtr flowGraph = flowGraphFactory->GetFlowGraph();
    live_graph_factory = new live::LiveGraphFactory(flowGraph);
    live_graph_factory->Liveness();
    live_graph = live_graph_factory->GetLiveGraph();
    auto temp_node_map = live_graph_factory->GetTempNodeMap();

    simplifyWorklist = new live::INodeList();
    freezeWorklist = new live::INodeList();
    spillWorklist = new live::INodeList();
    spilledNodes = new live::INodeList();
    coalescedNodes = new live::INodeList();
    coloredNodes = new live::INodeList();
    selectStack = new live::INodeList();

    coalescedMoves = new live::MoveList();
    constrainedMoves = new live::MoveList();
    frozenMoves = new live::MoveList();
    worklistMoves = live_graph->moves;
    activeMoves = new live::MoveList();
    
    for(auto reg: reg_manager->Registers()->GetList()){
        live::INodePtr node = temp_node_map->Look(reg);
        coloredNodes->Append(node);
        colorMap[node] = reg_manager->temp_map_->Look(reg);
    }
    live::INodePtr node_rsp = temp_node_map->Look(reg_manager->GetRsp());
    coloredNodes->Append(node_rsp);
    colorMap[node_rsp] = reg_manager->temp_map_->Look(reg_manager->GetRsp());

    for(auto node : live_graph->interf_graph->Nodes()->GetList()){
        degreeMap[node] = node->Degree();
        live::MoveList *node_move_list = new live::MoveList();
        for(auto move_pair : worklistMoves->GetList()){
            if(move_pair.first == node || move_pair.second == node){
                node_move_list->Append(move_pair.first, move_pair.second);
            }
        }
        moveListMap[node] = node_move_list;
    }
}

void RegAllocator::MakeWorklist() {
    auto nodes = live_graph->interf_graph->Nodes();
    for(auto node : nodes->GetList()){
        if(!coloredNodes->Contain(node)) {
            if(degreeMap[node] >= K) {
                spillWorklist->Append(node);
            } else if(MoveRelated(node)) {
                freezeWorklist->Append(node);
            } else {
                simplifyWorklist->Append(node);
            }
        }
    }
}

live::MoveList *RegAllocator::NodeMoves(live::INodePtr n) {
    return moveListMap[n]->Intersect(activeMoves->Union(worklistMoves));
}

bool RegAllocator::MoveRelated(live::INodePtr n) {
    return !NodeMoves(n)->GetList().empty();
}

void RegAllocator::Simplify() {
    auto node = simplifyWorklist->GetList().front();
    simplifyWorklist->DeleteNode(node);
    selectStack->Prepend(node);
    for(auto adj_node :Adjacent(node)->GetList()){
        DecrementDegree(adj_node);
    }
}

live::INodeListPtr RegAllocator::Adjacent(live::INodePtr n) {
    return n->Adj()->Diff(selectStack->Union(coalescedNodes));
}

void RegAllocator::DecrementDegree(live::INodePtr n){
    degreeMap[n]--;
    if ( degreeMap[n] == K - 1) {
        live::INodeListPtr n_adj_list = Adjacent(n);
        n_adj_list->Append(n);
        EnableMoves(n_adj_list);
        spillWorklist->DeleteNode(n);
        if (MoveRelated(n)) 
            freezeWorklist->Append(n);
        else 
            simplifyWorklist->Append(n);
    }
}

void RegAllocator::EnableMoves(live::INodeListPtr node_list) {
    for(auto node : node_list->GetList()) {
        for(auto move_node_pair : NodeMoves(node)->GetList()) {
            if(activeMoves->Contain(move_node_pair.first, move_node_pair.second)) {
                activeMoves->Delete(move_node_pair.first, move_node_pair.second);
                worklistMoves->Append(move_node_pair.first, move_node_pair.second);
            }
        }
    }
}

void RegAllocator::AssignColor() {
    while(!selectStack->GetList().empty()) {
        auto node = selectStack->GetList().front();
        selectStack->DeleteNode(node);
        std::list<std::string *> okColors;
        for (auto reg : reg_manager->Registers()->GetList()) {
            okColors.push_back(reg_manager->temp_map_->Look(reg));
        }
        for(auto succ : node->Succ()->GetList()) {
            if(coloredNodes->Contain(GetAilas(succ))) {
                auto ok_color_it = okColors.begin();
                auto end_flag = okColors.end();
                while(ok_color_it != end_flag){
                    if(*ok_color_it == colorMap[GetAilas(succ)])
                        break;
                    ++ok_color_it;
                }
                if(ok_color_it != end_flag)
                    okColors.erase(ok_color_it);
            }
        }
        if(okColors.empty()){
            spilledNodes->Append(node);
        } else {
            coloredNodes->Append(node);
            auto c = okColors.front();
            colorMap[node] = c;
        }
    }

    for(auto node : coalescedNodes->GetList()) {
        colorMap[node] = colorMap[GetAilas(node)];
    }
}

live::INodePtr RegAllocator::GetAilas(live::INodePtr n){
    if (coalescedNodes->Contain(n))
        return GetAilas(aliasMap[n]);
    else 
        return n;
}

void RegAllocator::AddWorkList(live::INodePtr u){
    if (!coloredNodes->Contain(u) && !MoveRelated(u) && degreeMap[u] < K) {
        freezeWorklist->DeleteNode(u);
        simplifyWorklist->Append(u);
    }
}

bool RegAllocator::OK(live::INodePtr t, live::INodePtr r){
    auto adj_t = Adjacent(t);
    bool flag = true;
    for (auto adj_node : adj_t->GetList()) {
        if (degreeMap[adj_node] < K || coloredNodes->Contain(adj_node) || adj_node->Adj(r)) 
            continue;
        else {
            flag = false;
            break;
        }
    }
    return flag;
}

bool RegAllocator::Conservative(live::INodeListPtr nodes){
    int k = 0;
    for (auto node : nodes->GetList()) {
        if (degreeMap[node] >= K) k++;
    }
    return (k < K);
}

void RegAllocator::addEdgeAdjacent(live::INodePtr u, live::INodePtr v) {
    if (!u->Adj(v) && u != v) {
        live_graph->interf_graph->AddEdge(u, v);
        live_graph->interf_graph->AddEdge(v, u);
        degreeMap[u]++;
        degreeMap[v]++;
    }
}

void RegAllocator::Combine(live::INodePtr u, live::INodePtr v) {
    if (freezeWorklist->Contain(v)) 
        freezeWorklist->DeleteNode(v);
    else 
        spillWorklist->DeleteNode(v);
    coalescedNodes->Append(v);
    aliasMap[v] = u;
    moveListMap[u] = moveListMap[u]->Union(moveListMap[v]);
    live::INodeListPtr node_list = new live::INodeList();
    node_list->Append(v);
    EnableMoves(node_list);
    for (auto node : Adjacent(v)->GetList()) {
        addEdgeAdjacent(node, u);
        DecrementDegree(node);
    }
    if (degreeMap[u] >= K && freezeWorklist->Contain(u)) {
        freezeWorklist->DeleteNode(u);
        spillWorklist->Append(u);
    }
}

void RegAllocator::Coalesce() {
    auto node_pair = worklistMoves->GetList().front();
    live::INodePtr x = GetAilas(node_pair.first);
    live::INodePtr y = GetAilas(node_pair.second);
    live::INodePtr u, v;
    /* 把v合并到u，注意不可以把reg合并到temp */
    if (coloredNodes->Contain(y)) {
        u = y;
        v = x;
    }
    else {
        u = x;
        v = y;
    }
    worklistMoves->Delete(node_pair.first, node_pair.second);
    if(u == v){
        coalescedMoves->Append(node_pair.first, node_pair.second);
        AddWorkList(u);
    }
    else if (coloredNodes->Contain(v) || u->Adj(v)) {
        coalescedMoves->Append(node_pair.first, node_pair.second);
        AddWorkList(u);
        AddWorkList(v);
    }
    else if (coloredNodes->Contain(u) && OK(v, u) ||
        !coloredNodes->Contain(u) && Conservative(Adjacent(u)->Union(Adjacent(v)))
    ) {
        coalescedMoves->Append(node_pair.first, node_pair.second);
        Combine(u, v);
        AddWorkList(u);
    }
    else {
        activeMoves->Append(node_pair.first, node_pair.second);
    }
}

void RegAllocator::Freeze() {
    /*
    let u∈freezeWorkList 
	freezeWorkList ← freezeWorkList \ {u}
	simplifyWorkList ← simplifyWorkList ∪{u}
	FreezeMoves(u)
    */
    auto u = freezeWorklist->GetList().front();
    freezeWorklist->DeleteNode(u);
    simplifyWorklist->Append(u);
    FreezeMoves(u); 
}

void RegAllocator::RewriteProgram() {
    //throw std::runtime_error("rewriteProgram");
    /*
    Allocate memory locations for each v∈spilledNodes
	Create a new temporary vi for each definition and each use
	In the program (instructions), insert a store after each 
	definition of a vi , a fetch before each use of a vi
	Put All the vi into a set newTemps
	spilledNode ← {}
	initial ← coloredNodes∪coalescedNodes∪newTemp
	coloredNodes ← {}
	coalescedNodes ←{}
    */
    /* Alloc stack space for every spilledNodes */
    //由于在实现中，所有我自己生成的变量已经在栈上，所以不需要做新的alloc
    /*记录要spill的temp的offset，这可以找到它在栈上的location*/
    std::cout << "REWRITE: " << std::to_string(count++) << std::endl;
    std::map<temp::Temp *, int> spill_offset_map;

    for (auto v : spilledNodes->GetList()) {
        frame_info_map[this->body_name_str_].first -= 8;
        frame_info_map[this->body_name_str_].second += 8;
        spill_offset_map[v->NodeInfo()] = frame_info_map[this->body_name_str_].first;
    }
    /* Update assem_instr */
    assem::InstrList *new_assem_list = new assem::InstrList();
    std::string last_label = this->body_name_str_;
    for (auto instr : assem_instr->GetInstrList()->GetList()) {
        /* Check if both def&use are nullptr */
        //开始遍历寻找用到spill temp的指令
        temp::TempList *def_temp_list = instr->Def();
        temp::TempList *use_temp_list = instr->Use();
        if(typeid(*instr) == typeid(assem::LabelInstr)){
            assem::LabelInstr *label_instr = (assem::LabelInstr *) instr;
            last_label = label_instr->assem_;
            std::cout << "LAST_LABEL: " << last_label << std::endl;
        }
        if (def_temp_list == nullptr && use_temp_list == nullptr || def_temp_list != nullptr && def_temp_list->GetList().size() == 0 && use_temp_list != nullptr && use_temp_list->GetList().size() == 0) {
            new_assem_list->Append(instr);
            continue;
        }

        temp::Temp *frame_temp = temp::TempFactory::NewTemp();
        temp::TempList *new_def_list = nullptr;
        temp::TempList *new_use_list = nullptr;
        assem::InstrList *def_assem_list = new assem::InstrList();
        assem::InstrList *use_assem_list = new assem::InstrList();
        temp::Temp *rsp = reg_manager->GetRsp();
        /* If instr->Def() contains vi */
        if (def_temp_list != nullptr && def_temp_list->GetList().size() != 0) {
            for (auto def_temp : def_temp_list->GetList()) {
                /* Spilled nodes */
                if (spill_offset_map.count(def_temp) != 0) {
                    //move:在入口被def
                    int offset = spill_offset_map[def_temp];
                    temp::Temp *new_temp = temp::TempFactory::NewTemp();
                    //func: 里面的特殊情况，因为rsp还没有减去framesize
                    if(last_label == this->body_name_str_){
                        if (typeid(*instr) == typeid(assem::MoveInstr)) {
                            assem::MoveInstr *move_instr = (assem::MoveInstr *) instr;
                            std::cout << "DEF_SPILL_MOVE_CODE: " + move_instr->assem_ + " " + std::to_string(def_temp->Int())  + " use:" + std::to_string(move_instr->src_->NthTemp(0)->Int())<< std::endl;
                            new_use_list = move_instr->Use();

                            def_assem_list->Append(
                                new assem::MoveInstr(
                                    "movq `s0, `d0",
                                    new temp::TempList(new_temp),
                                    new_use_list
                                )
                            );
                        } else if (typeid(*instr) == typeid(assem::OperInstr)) {
                            assem::OperInstr *op_instr = (assem::OperInstr *) instr;
                            std::cout << "DEF_SPILL_MOVE_CODE: " +  op_instr->assem_ + " " + std::to_string(def_temp->Int()) << std::endl;
                            op_instr->dst_ = new temp::TempList(new_temp);
                            instr = op_instr;

                            def_assem_list->Append(instr);
                        } else {
                            throw std::runtime_error("should not be label");
                        }

                        def_assem_list->Append(
                            new assem::OperInstr(
                                "leaq " + std::to_string(offset) + "(%rsp), `d0",
                                new temp::TempList(frame_temp),
                                new temp::TempList(rsp),
                                nullptr
                            )
                        );

                        def_assem_list->Append(
                            new assem::OperInstr(
                                "movq `s0, (`s1)",
                                nullptr, new temp::TempList{new_temp, frame_temp},
                                nullptr
                            )
                        );
                    }
                    else {
                        //内部被def
                        if (typeid(*instr) == typeid(assem::MoveInstr)) {
                            assem::MoveInstr *move_instr = (assem::MoveInstr *) instr;
                            std::cout << "TEST_DEF_SPILL_MOVE_CODE: " + move_instr->assem_ + " " + std::to_string(def_temp->Int())  + " use:" + std::to_string(move_instr->src_->NthTemp(0)->Int())<< std::endl;
                            new_use_list = move_instr->Use();

                            def_assem_list->Append(
                                new assem::MoveInstr(
                                    "movq `s0, `d0",
                                    new temp::TempList(new_temp),
                                    new_use_list
                                )
                            );
                        } else if (typeid(*instr) == typeid(assem::OperInstr)) {
                            assem::OperInstr *op_instr = (assem::OperInstr *) instr;
                            std::cout << "TEST_DEF_SPILL_MOVE_CODE: " +  op_instr->assem_ + " " + std::to_string(def_temp->Int()) << std::endl;
                            op_instr->dst_ = new temp::TempList(new_temp);
                            instr = op_instr;

                            def_assem_list->Append(instr);
                        } else {
                            throw std::runtime_error("should not be label");
                        }

                        uint64_t frame_size = frame_info_map[this->body_name_str_].second / 16 * 16 + 8;

                        def_assem_list->Append(
                            new assem::OperInstr(
                                "leaq " + std::to_string(frame_size) + "(%rsp), `d0",
                                new temp::TempList(frame_temp),
                                new temp::TempList(rsp),
                                nullptr
                            )
                        );

                        def_assem_list->Append(
                            new assem::OperInstr(
                                "movq `s0," + std::to_string(offset) + "(`s1)",
                                nullptr, new temp::TempList{new_temp, frame_temp},
                                nullptr
                            )
                        );
                    }
                  
                }
            }
            
        }
        /* If instr->Use() contains vi */   
        if (use_temp_list != nullptr && use_temp_list->GetList().size() != 0) {
            for (auto use_temp : use_temp_list->GetList()) {
                /* Spilled nodes */
                if (spill_offset_map.count(use_temp) != 0) {
                    int offset = spill_offset_map[use_temp];
                    temp::Temp *new_temp = temp::TempFactory::NewTemp();
                    //这个指令temp确实是在出口被use
                    if (typeid(*instr) == typeid(assem::MoveInstr)) {
                        assem::MoveInstr *move_instr = (assem::MoveInstr *) instr;
                        std::cout << "USE_SPILL_MOVE_CODE: " + move_instr->assem_ + " " + std::to_string(use_temp->Int()) + " def:" + std::to_string(move_instr->dst_->NthTemp(0)->Int()) << std::endl;
                        new_def_list = move_instr->Def();
                        uint64_t frame_size = frame_info_map[this->body_name_str_].second / 16 * 16 + 8;

                        use_assem_list->Append(
                            new assem::OperInstr(
                                "leaq " + std::to_string(frame_size) + "(%rsp), `d0",
                                new temp::TempList(frame_temp),
                                new temp::TempList(rsp),
                                nullptr
                            )
                        );

                        use_assem_list->Append(
                            new assem::OperInstr(
                                "movq "+ std::to_string(offset) +"(`s0), `d0",
                                new temp::TempList(new_temp), 
                                new temp::TempList(frame_temp),
                                nullptr
                            )
                        );

                        use_assem_list->Append(
                            new assem::MoveInstr(
                                "movq `s0, `d0",
                                new_def_list,
                                new temp::TempList(new_temp)
                            )
                        );
                    } else if (typeid(*instr) == typeid(assem::OperInstr)) {
                        //throw std::runtime_error("use not finished");
                        assem::OperInstr *op_instr = (assem::OperInstr *) instr;
                        std::cout << "USE_SPILL_OP_CODE: " + op_instr->assem_ + " " + std::to_string(use_temp->Int()) << std::endl;

                        uint64_t frame_size = frame_info_map[this->body_name_str_].second / 16 * 16 + 8;

                        use_assem_list->Append(
                            new assem::OperInstr(
                                "leaq " + std::to_string(frame_size) + "(%rsp), `d0",
                                new temp::TempList(frame_temp),
                                new temp::TempList(rsp),
                                nullptr
                            )
                        );

                        use_assem_list->Append(
                            new assem::OperInstr(
                                "movq "+ std::to_string(offset) +"(`s0), `d0",
                                new temp::TempList(new_temp), 
                                new temp::TempList(frame_temp),
                                nullptr
                            )
                        );

                        //接下来只要把原本use的told换成tnew
                        temp::TempList *temp_use_list = new temp::TempList();
                        for(auto old_use_t : use_temp_list->GetList()){
                            if(old_use_t != use_temp){
                                temp_use_list->Append(old_use_t);
                            } else {
                                temp_use_list->Append(new_temp);
                            }
                        }
                        op_instr->src_ = temp_use_list;
                        instr = op_instr;
                        use_assem_list->Append(instr);
                        
                    } else {
                        throw std::runtime_error("should not be label");
                    }
                   
                }
            }
        }
        /* Insert new instrs to assem_instr */
        /* 1. Not spilled nodes */
        if (def_assem_list->GetList().size() == 0 
            && use_assem_list->GetList().size() == 0) {
            new_assem_list->Append(instr);
        } 
        /* 2. Spilled nodes */
        else {
            /* Append instrs in use_assem_list */
            if(def_assem_list->GetList().size() != 0 ){
                assert(use_assem_list->GetList().size() == 0);
            }
            if(use_assem_list->GetList().size() != 0){
                assert(def_assem_list->GetList().size() == 0);
            }
            for (auto use_assem_instr : use_assem_list->GetList())
                new_assem_list->Append(use_assem_instr);
            /* Append instrs in def_assem_list */
            for (auto def_assem_instr : def_assem_list->GetList())
                new_assem_list->Append(def_assem_instr);
        }
        /* Realloc some variables */
        delete def_assem_list;
        delete use_assem_list;
    }
    /* Reinitialize assem_instr */
    assem_instr.reset();
    assem_instr = std::move(std::make_unique<cg::AssemInstr>(new_assem_list));
    /* Realloc some variables */
    delete live_graph_factory;
    //delete live_graph;
    delete simplifyWorklist;
    delete freezeWorklist;
    delete spillWorklist;
    delete spilledNodes;
    delete coalescedNodes;
    delete coloredNodes;
    delete selectStack;
    delete constrainedMoves;
    delete frozenMoves;
    delete worklistMoves;
    delete activeMoves;
    degreeMap.clear();
    moveListMap.clear();
    aliasMap.clear();
    colorMap.clear();
}

void RegAllocator::SelectSpill() {
    auto n = spillWorklist->GetList().front();
    spillWorklist->DeleteNode(n);
    simplifyWorklist->Append(n);
    FreezeMoves(n);
}

void RegAllocator::FreezeMoves(live::INodePtr u) {
    /*
    forall m(=copy(x,y))∈NodeMoves(u)
	    if GetAlias(y)=GetAlias(u) then
	        v ← GetAlias(x)
	    else
	        v ← GetAlias(y)
	    activeMoves ← activeMoves \ {m} 
	    frozenMoves ← frozenMoves ∪ {m}
	    if NodeMoves(v) = {}∧ degree[v] < K then
	        freezeWorkList ← freezeWorkList \ {v}
	        simplifyWorkList ← simplifyWorkList ∪ {v} 	
    */
    for(auto node_pair : NodeMoves(u)->GetList()) {
        live::INodePtr v;
        if(GetAilas(node_pair.second) == GetAilas(u)){
            v = GetAilas(node_pair.first);
        }
        else {
            v = GetAilas(node_pair.second);
        }
        activeMoves->Delete(node_pair.first, node_pair.second);
        frozenMoves->Append(node_pair.first, node_pair.second);
        if(NodeMoves(v)->GetList().empty() && degreeMap[v] < K) {
            freezeWorklist->DeleteNode(v);
            simplifyWorklist->Append(v);
        }
    }
}

} // namespace ra