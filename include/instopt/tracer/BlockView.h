#pragma once
#include "instopt/engine/state_explorer.h"
#include <set>
#include <vector>

class BlockView {
  irsb_chunk m_ic;
  std::set<BlockView *> m_nexts;
  std::vector<Addr> m_fork_ea;
  BlockView(irsb_chunk &ic) : m_ic(ic) {}

public:
  class BlockViewKeyHash {
  public:
    size_t operator()(const BlockView *&name) const {
      return std::hash<size_t>()(name->m_ic->get_bb_base() ^
                                 name->m_ic->get_checksum());
    }
  };

public:
  BlockView(irsb_chunk &ic, BlockView *next) : m_ic(ic) { add_next(next); }
  BlockView(const BlockView &B)
      : m_ic(B.m_ic), m_nexts(B.m_nexts), m_fork_ea(B.m_fork_ea) {}
  void operator=(const BlockView &B) {
    this->~BlockView();
    new (this) BlockView(B);
  }
  ~BlockView() {}
  static BlockView mk_root(irsb_chunk &ic) { return BlockView(ic); }
  irsb_chunk get_irsb_chunk() const { return m_ic; }
  void add_next(BlockView *next) {
    if (next) {
      m_nexts.emplace(next);
    }
  }
  inline const std::set<BlockView *> &get_nexts() const { return m_nexts; }

  void ppBlock(TR::vex_context &vctx, std::shared_ptr<spdlog::logger> log,
               bool treebuild = false);

  void makr_fork_ea(Addr ea) {
    auto bb_ea = m_ic->get_bb_base();
    auto bb_sz = m_ic->get_bb_size();
    vassert(bb_ea <= ea && bb_ea + bb_sz >= ea);
    m_fork_ea.emplace_back(ea);
  }

  bool check_fork_ea(Addr ea) {
    return std::find(m_fork_ea.begin(), m_fork_ea.end(), ea) != m_fork_ea.end();
  }
};