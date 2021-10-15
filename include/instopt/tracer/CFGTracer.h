#pragma once
// ===============================================================================================================================

#include "instopt/tracer/BlockView.h"
#include <forward_list>

#include <llvm/Support/GraphWriter.h>
#include <llvm/Support/DOTGraphTraits.h>
#include <vexllvm/genllvm.h>

#include "instopt/engine/state_explorer.h"

class GraphView {
  using _jmps = std::forward_list<Addr>;
  template <typename Addr> friend class PathExplorer;

  // spin_mutex translate_mutex;
  TR::vex_context &m_vctx;
  using BBKey = std::pair<Addr, size_t>;

  class BBKeyHash {
  public:
    size_t operator()(const BBKey &name) const {
      return std::hash<size_t>()(name.first ^ name.second);
    }
  };

public:
  using BlocksTy = typename std::unordered_map<BBKey, BlockView, BBKeyHash>;
  using MutiBlocksTy =
      typename std::unordered_map<Addr,
                                  std::shared_ptr<std::vector<BlockView>>>;

private:
  BlocksTy m_blocks;
  MutiBlocksTy m_mutiBlocks;

public:
  class ExplodedGraph {
  public:
    GraphView &graph_view;

    using nodes_iterator = GraphView::BlocksTy::iterator;
    using NodeRef = const BlockView *;

    // std::vector<NodeRef> node;
    std::vector<NodeRef> nodes;
    ExplodedGraph(GraphView &GV) : graph_view(GV) {
      auto &blocks = graph_view.get_blocks();
      nodes.reserve(blocks.size());
      auto it = blocks.begin();
      for (; it != blocks.end(); it++) {
        auto sub_ep = it->first.first;
        auto check_sum = it->first.second;
        const BlockView &basic_irsb_chunk = it->second;
        // basic_irsb_chunk.ppBlock(m_vctx, log);
        nodes.emplace_back(&basic_irsb_chunk);
      }
    }
  };

  std::shared_ptr<spdlog::logger> log;
  GraphView(TR::vex_context &vctx);

  ~GraphView() {}

  std::shared_ptr<TR::TraceInterface> mk_explore();

  const BlocksTy &get_blocks() { return m_blocks; };
  const MutiBlocksTy &get_MutiBlocks() { return m_mutiBlocks; };

  void ppGraphView(bool treebuild = false);

  std::string creat_graph(const char *dotName = "CFG");
  void simplify();
  llvm::Function *emitOneBlock(BlockView BV);

  BlockView *add_block(irsb_chunk irsb_chunk, BlockView *next);
  BlockView *add_block(BBKey &bk, BlockView bv);

  void add_exit(irsb_chunk irsb_chunk, Addr code_ea, Addr next);
  void state_task(TR::State &s);
  void explore_block(TR::State *s);

  auto mk_irsb_chunk_key(irsb_chunk irsb_chunk) {
    auto ea = irsb_chunk->get_bb_base();
    auto checksum = irsb_chunk->get_checksum();
    return BBKey(std::make_pair(ea, checksum));
  }
  void mark_is_fork_ea(irsb_chunk irsb_chunk, Addr code_ea) {
    auto key = mk_irsb_chunk_key(irsb_chunk);
    auto it = m_blocks.find(key);
    if (it == m_blocks.end()) {
      vassert(0);
      // m_blocks.emplace(key, BlockView(irsb_chunk));
    } else {
      it->second.makr_fork_ea(code_ea);
    }
  }

  bool check_is_fork_ea(irsb_chunk irsb_chunk, Addr code_ea) {
    auto key = mk_irsb_chunk_key(irsb_chunk);
    auto it = m_blocks.find(key);

    if (it == m_blocks.end()) {
      vassert(0);
      // m_blocks.emplace(key, BlockView(irsb_chunk));
      return false;
    } else {
      return it->second.check_fork_ea(code_ea);
    }
  }

  bool is_block_exist(irsb_chunk irsb_chunk) {
    auto key = mk_irsb_chunk_key(irsb_chunk);
    auto it = m_blocks.find(key);
    return it != m_blocks.end();
  }
};


class explorer : public TR::TraceInterface {
  GraphView &m_gv;
  UInt m_IMark_stmtn;
  irsb_chunk bck_irsb;

public:
  explorer(GraphView &gv) : m_gv(gv) {}
  void update_block_chain(irsb_chunk curr) {
    if (bck_irsb) {
      m_gv.add_block(bck_irsb, m_gv.add_block(curr, nullptr));
    } else {
      m_gv.add_block(curr, nullptr);
    }
    bck_irsb = curr;
  }
  virtual void traceStart(TR::State &s, HWord ea) override;
  virtual void traceIRSB(TR::State &s, HWord ea, irsb_chunk &) override;
  virtual void traceIRStmtStart(TR::State &s, irsb_chunk &,
                                UInt stmtn) override;
  virtual void traceIRStmtEnd(TR::State &s, irsb_chunk &irsb,
                              UInt stmtn) override;
  virtual void traceIRnext(TR::State &s, irsb_chunk &irsb,
                           const tval &next) override;
  virtual void traceIrsbEnd(TR::State &s, irsb_chunk &) override;
  virtual void traceFinish(TR::State &s, HWord ea) override;

  virtual std::shared_ptr<TraceInterface> mk_new_TraceInterface() override {
    return std::make_shared<explorer>(m_gv);
  }
  virtual ~explorer() {}
};
