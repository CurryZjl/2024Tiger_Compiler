#ifndef TIGER_REGALLOC_REGALLOC_H_
#define TIGER_REGALLOC_REGALLOC_H_

#include "tiger/codegen/assem.h"
#include "tiger/codegen/codegen.h"
#include "tiger/frame/frame.h"
#include "tiger/frame/temp.h"
#include "tiger/liveness/liveness.h"
#include "tiger/regalloc/color.h"
#include "tiger/util/graph.h"

namespace ra {

class Result {
public:
  temp::Map *coloring_;
  assem::InstrList *il_;

  Result() : coloring_(nullptr), il_(nullptr) {}
  Result(temp::Map *coloring, assem::InstrList *il)
      : coloring_(coloring), il_(il) {}
  Result(const Result &result) = delete;
  Result(Result &&result) = delete;
  Result &operator=(const Result &result) = delete;
  Result &operator=(Result &&result) = delete;
  ~Result() {
    delete coloring_;
    delete il_;
  }
};

class RegAllocator {
  /* TODO: Put your lab6 code here */
public:
  RegAllocator() = default;
  ~RegAllocator() = default;
  RegAllocator(std::string body_name_str_, std::unique_ptr<cg::AssemInstr> assem_instr_);
  std::unique_ptr<ra::Result> TransferResult();
  void RegAlloc();

private:
  const int K = 16;
  std::string body_name_str_;
  std::unique_ptr<Result> result;
  std::unique_ptr<cg::AssemInstr> assem_instr;
  live::LiveGraphFactory *live_graph_factory;
  live::LiveGraph *live_graph;

  /* low degree non-move-related nodes */
  live::INodeListPtr simplifyWorklist;
  /* low degree move-related nodes */
  live::INodeListPtr freezeWorklist;
  /* high degree nodes */
  live::INodeListPtr spillWorklist;
  /* nodes marked for spilling */
  live::INodeListPtr spilledNodes;
  /* nodes that have been coalesced */
  live::INodeListPtr coalescedNodes;
  /* nodes that have benn colored*/
  live::INodeListPtr coloredNodes;
  /* a stack containing nodes deleted from interf_graph */
  live::INodeListPtr selectStack;

  /* move instrs that have been coalesced */
  live::MoveList *coalescedMoves;
  /* constrained move instrs*/
  live::MoveList *constrainedMoves;
  /* frozen move instrs */
  live::MoveList *frozenMoves;
  /* moves enabled for coalescing */  
  live::MoveList *worklistMoves;
  /* move instr not prepared for coalescing */
  live::MoveList *activeMoves;

  /* map: node -> its degree */
  std::map<live::INodePtr, int> degreeMap;
  /* map: node -> its move instrs */
  std::map<live::INodePtr, live::MoveList *> moveListMap;
  /* map: node -> the node coalescing this node */
  std::map<live::INodePtr, live::INodePtr> aliasMap;
  /* map: node -> its color */
  std::map<live::INodePtr, std::string *> colorMap;

  void Build();
  void Simplify();
  void Coalesce();
  void Freeze();
  void RewriteProgram();
  void SelectSpill();

  void MakeWorklist();
  void AssignColor();
  bool MoveRelated(live::INodePtr n);
  live::MoveList *NodeMoves(live::INodePtr n);
  live::INodeListPtr Adjacent(live::INodePtr n);
  void DecrementDegree(live::INodePtr n);
  void EnableMoves(live::INodeListPtr node_list);
  void FreezeMoves(live::INodePtr n);

  /*Util for Coalesce*/
  live::INodePtr GetAilas(live::INodePtr n);
  void AddWorkList(live::INodePtr u);
  bool OK(live::INodePtr t, live::INodePtr r);
  bool Conservative(live::INodeListPtr nodes);
  void Combine(live::INodePtr u, live::INodePtr v);
  void addEdgeAdjacent(live::INodePtr u, live::INodePtr v);
};

} // namespace ra

#endif