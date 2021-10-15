#pragma once

#include "instopt/tracer/CFGTracer.h"
#include <llvm/Support/GraphWriter.h>
#include <llvm/Support/DOTGraphTraits.h>
#include <vexllvm/vexhelpers.h>
#include <vexllvm/vexsb.h>

// ===============================================================================================================================

namespace llvm {
template <>
struct DOTGraphTraits<GraphView::ExplodedGraph *>
    : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool simple = false) : DefaultDOTGraphTraits(simple) {}

private:
  bool IsSimple;

protected:
  bool isSimple() { return IsSimple; }

public:
  /// getGraphName - Return the label for the graph as a whole.  Printed at the
  /// top of the graph.
  ///
  template <typename GraphType>
  static std::string getGraphName(const GraphType &G) {
    return "";
  }

  /// getGraphProperties - Return any custom properties that should be included
  /// in the top level graph structure for dot.
  ///
  template <typename GraphType>
  static std::string getGraphProperties(const GraphType &) {
    // return "graph [rankdir=LR];";
    return "";
  }

  /// renderGraphFromBottomUp - If this function returns true, the graph is
  /// emitted bottom-up instead of top-down.  This requires graphviz 2.0 to work
  /// though.
  static bool renderGraphFromBottomUp() { return false; }

  /// isNodeHidden - If the function returns true, the given node is not
  /// displayed in the graph.
  template <typename GraphType>
  static bool isNodeHidden(const void *, const GraphType &) {
    return false;
  }


  /// isNodeHidden - If the function returns true, the given node is not
  /// displayed in the graph.
  static bool isNodeHidden(const void*) {
      return false;
  }

  /// getNodeLabel - Given a node and a pointer to the top level graph, return
  /// the label to print in the node.
  template <typename GraphType>
  std::string getNodeLabel(const void *n, const GraphType &G) {
    const BlockView *node = static_cast<const BlockView *>(n);
    std::stringstream st;
    irsb_chunk irsb = node->get_irsb_chunk();
    st << " ea:" << std::hex << irsb->get_bb_base() << std::hex
       << " sz:" << irsb->get_bb_size() << "\n"
       << irsb->get_checksum();
    return st.str();
  }

  // getNodeIdentifierLabel - Returns a string representing the
  // address or other unique identifier of the node. (Only used if
  // non-empty.)
  template <typename GraphType>
  static std::string getNodeIdentifierLabel(const void *n, const GraphType &G) {
    const BlockView *node = static_cast<const BlockView *>(n);
    std::shared_ptr<spdlog::logger> log;
    // ppIR pp(log, spdlog::level::off);
    // irsb_chunk ic = node->get_irsb_chunk();
    // auto bb_ea = ic->get_bb_base();
    // auto bb_sz = ic->get_bb_size();
    //// pp.vex_printf("sub_0x%llx : \n\t/*\n\t* checksum:%16llx
    ///sz:%x\n\t*/{\n", bb_ea, ic->get_checksum(), bb_sz);
    // auto bb = ic->get_irsb();
    // int i;
    // for (i = 0; i < bb->stmts_used; i++) {
    //     pp.vex_printf("\t");
    //     pp.ppIRStmt(bb->stmts[i]);
    //     pp.vex_printf("\n");
    // }
    // pp.vex_printf("\tPUT(%d) = ", bb->offsIP);
    // pp.ppIRExpr(bb->next);
    // return pp.str();
    return "";
  }

  template <typename GraphType>
  static std::string getNodeDescription(const void *, const GraphType &) {
    return "";
  }

  /// If you want to specify custom node attributes, this is the place to do so
  ///
  template <typename GraphType>
  static std::string getNodeAttributes(const void *, const GraphType &) {
    return "";
  }

  /// If you want to override the dot attributes printed for a particular edge,
  /// override this method.
  template <typename EdgeIter, typename GraphType>
  static std::string getEdgeAttributes(const void *, EdgeIter,
                                       const GraphType &) {
    return "";
  }

  /// getEdgeSourceLabel - If you want to label the edge source itself,
  /// implement this method.
  template <typename EdgeIter>
  static std::string getEdgeSourceLabel(const void *, EdgeIter) {
    return "";
  }

  /// edgeTargetsEdgeSource - This method returns true if this outgoing edge
  /// should actually target another edge source, not a node.  If this method is
  /// implemented, getEdgeTarget should be implemented.
  template <typename EdgeIter>
  static bool edgeTargetsEdgeSource(const void *, EdgeIter) {
    return false;
  }

  /// getEdgeTarget - If edgeTargetsEdgeSource returns true, this method is
  /// called to determine which outgoing edge of Node is the target of this
  /// edge.
  template <typename EdgeIter>
  static EdgeIter getEdgeTarget(const void *, EdgeIter I) {
    return I;
  }

  /// hasEdgeDestLabels - If this function returns true, the graph is able
  /// to provide labels for edge destinations.
  static bool hasEdgeDestLabels() { return false; }

  /// numEdgeDestLabels - If hasEdgeDestLabels, this function returns the
  /// number of incoming edge labels the given node has.
  static unsigned numEdgeDestLabels(const void *) { return 0; }

  /// getEdgeDestLabel - If hasEdgeDestLabels, this function returns the
  /// incoming edge label with the given index in the given node.
  static std::string getEdgeDestLabel(const void *, unsigned) { return ""; }

  /// addCustomGraphFeatures - If a graph is made up of more than just
  /// straight-forward nodes and edges, this is the place to put all of the
  /// custom stuff necessary.  The GraphWriter object, instantiated with your
  /// GraphType is passed in as an argument.  You may call arbitrary methods on
  /// it to add things to the output graph.
  ///
  template <typename GraphType, typename GraphWriter>
  static void addCustomGraphFeatures(const GraphType &, GraphWriter &) {}
};

template <> struct GraphTraits<GraphView::ExplodedGraph *> {
public:
  using GraphTy = GraphView::ExplodedGraph *;

  using NodeRef = const BlockView *;
  using nodes_iterator = std::vector<NodeRef>::iterator;

  using ChildIteratorType =
      std::set<BlockView *, BlockView::BlockViewKeyHash>::iterator;

  static nodes_iterator nodes_begin(GraphTy n) { return n->nodes.begin(); }

  static nodes_iterator nodes_end(GraphTy n) { return n->nodes.end(); }

  static ChildIteratorType child_begin(NodeRef nr) {
    return nr->get_nexts().begin();
  }

  static ChildIteratorType child_end(NodeRef nr) {
    return nr->get_nexts().end();
  }



  /*static NodeRef child_it_get(ChildIteratorType&) {

  }

  static std::string Nodekey(NodeRef nr) {
      std::stringstream s;
      s << nr.first.first << "-" << nr.first.second;
      return s.str();
  }

  static const void* NodePointer(NodeRef nr) {
      return nullptr;
  }*/
};
}; // namespace llvm
