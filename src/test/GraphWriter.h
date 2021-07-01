
#ifndef LLVM_SUPPORT_GRAPHWRITER_H 
#define LLVM_SUPPORT_GRAPHWRITER_H 

#include "GraphTraits.h" 
#include "DOTGraphTraits.h" 
#include <algorithm> 
#include <cstddef> 
#include <iterator> 
#include <string> 
#include <type_traits> 
#include <vector>

namespace llvm {

    namespace DOT {  // Private functions... 
        std::string EscapeString(const std::string& Label);
    } // end namespace DOT 

    /// A raw_ostream that writes to an std::string.  This is a simple adaptor 
   /// class. This class does not encounter output errors. 
    using raw_ostream = std::ofstream;
    using raw_string_ostream = std::stringstream;

template<typename GraphType>
class GraphWriter {
    using raw_ostream = std::stringstream;
    raw_ostream& O;
    const GraphType& G;

    using DOTTraits = DOTGraphTraits<GraphType>;
    using GTraits = GraphTraits<GraphType>;
    using NodeRef = typename GTraits::NodeRef;
    using node_iterator = typename GTraits::nodes_iterator;
    using child_iterator = typename GTraits::ChildIteratorType;
    DOTTraits DTraits;


    // Writes the edge labels of the node to O and returns true if there are any 
      // edge labels not equal to the empty string "". 
    bool getEdgeSourceLabels(raw_ostream& O, NodeRef Node) {
        child_iterator EI = GTraits::child_begin(Node);
        child_iterator EE = GTraits::child_end(Node);
        bool hasEdgeSourceLabels = false;

        for (unsigned i = 0; EI != EE && i != 64; ++EI, ++i) {
            std::string label = DTraits.getEdgeSourceLabel(Node, EI);

            if (label.empty())
                continue;

            hasEdgeSourceLabels = true;

            if (i)
                O << "|";

            O << "<s" << i << ">" << DOT::EscapeString(label);
        }

        if (EI != EE && hasEdgeSourceLabels)
            O << "|<s64>truncated...";

        return hasEdgeSourceLabels;
    }

public:
    GraphWriter(raw_ostream& o, const GraphType& g, bool SN) : O(o), G(g) {
        DTraits = DOTTraits(SN);
    }

    void writeGraph(const std::string& Title = "") {
        // Output the header for the graph... 
        writeHeader(Title);

        // Emit all of the nodes in the graph... 
        writeNodes();

        // Output any customizations on the graph 
        DOTGraphTraits<GraphType>::addCustomGraphFeatures(G, *this);

        // Output the end of the graph 
        writeFooter();
    }

    void writeHeader(const std::string& Title) {
        std::string GraphName = DTraits.getGraphName(G);

        if (!Title.empty())
            O << "digraph \"" << DOT::EscapeString(Title) << "\" {\n";
        else if (!GraphName.empty())
            O << "digraph \"" << DOT::EscapeString(GraphName) << "\" {\n";
        else
            O << "digraph unnamed {\n";

        if (DTraits.renderGraphFromBottomUp())
            O << "\trankdir=\"BT\";\n";

        if (!Title.empty())
            O << "\tlabel=\"" << DOT::EscapeString(Title) << "\";\n";
        else if (!GraphName.empty())
            O << "\tlabel=\"" << DOT::EscapeString(GraphName) << "\";\n";
        O << DTraits.getGraphProperties(G);
        O << "\n";
    }

    void writeFooter() {
        // Finish off the graph 
        O << "}\n";
    }

    void writeNodes() {
        // Loop over the graph, printing it out... 
        for (const auto Node : nodes<GraphType>(G))
            if (!isNodeHidden(Node))
                writeNode(Node);
    }

    bool isNodeHidden(NodeRef Node) {
        return DTraits.isNodeHidden(Node);
    }

    void writeNode(NodeRef Node) {
        std::string NodeAttributes = DTraits.getNodeAttributes(Node, G);

        O << "\tNode" << static_cast<const void*>(Node) << " [shape=record,";
        if (!NodeAttributes.empty()) O << NodeAttributes << ",";
        O << "label=\"{";

        if (!DTraits.renderGraphFromBottomUp()) {
            O << DOT::EscapeString(DTraits.getNodeLabel(Node, G));

            // If we should include the address of the node in the label, do so now. 
            std::string Id = DTraits.getNodeIdentifierLabel(Node, G);
            if (!Id.empty())
                O << "|" << DOT::EscapeString(Id);

            std::string NodeDesc = DTraits.getNodeDescription(Node, G);
            if (!NodeDesc.empty())
                O << "|" << DOT::EscapeString(NodeDesc);
        }

        std::string edgeSourceLabels;
        raw_string_ostream EdgeSourceLabels(edgeSourceLabels);
        bool hasEdgeSourceLabels = getEdgeSourceLabels(EdgeSourceLabels, Node);

        if (hasEdgeSourceLabels) {
            if (!DTraits.renderGraphFromBottomUp()) O << "|";

            O << "{" << EdgeSourceLabels.str() << "}";

            if (DTraits.renderGraphFromBottomUp()) O << "|";
        }

        if (DTraits.renderGraphFromBottomUp()) {
            O << DOT::EscapeString(DTraits.getNodeLabel(Node, G));

            // If we should include the address of the node in the label, do so now. 
            std::string Id = DTraits.getNodeIdentifierLabel(Node, G);
            if (!Id.empty())
                O << "|" << DOT::EscapeString(Id);

            std::string NodeDesc = DTraits.getNodeDescription(Node, G);
            if (!NodeDesc.empty())
                O << "|" << DOT::EscapeString(NodeDesc);
        }

        if (DTraits.hasEdgeDestLabels()) {
            O << "|{";

            unsigned i = 0, e = DTraits.numEdgeDestLabels(Node);
            for (; i != e && i != 64; ++i) {
                if (i) O << "|";
                O << "<d" << i << ">"
                    << DOT::EscapeString(DTraits.getEdgeDestLabel(Node, i));
            }

            if (i != e)
                O << "|<d64>truncated...";
            O << "}";
        }

        O << "}\"];\n";   // Finish printing the "node" line 

        // Output all of the edges now 
        child_iterator EI = GTraits::child_begin(Node);
        child_iterator EE = GTraits::child_end(Node);
        for (unsigned i = 0; EI != EE && i != 64; ++EI, ++i)
            if (!DTraits.isNodeHidden(*EI))
                writeEdge(Node, i, EI);
        for (; EI != EE; ++EI)
            if (!DTraits.isNodeHidden(*EI))
                writeEdge(Node, 64, EI);
    }

    void writeEdge(NodeRef Node, unsigned edgeidx, child_iterator EI) {
        if (NodeRef TargetNode = *EI) {
            int DestPort = -1;
            if (DTraits.edgeTargetsEdgeSource(Node, EI)) {
                child_iterator TargetIt = DTraits.getEdgeTarget(Node, EI);

                // Figure out which edge this targets... 
                unsigned Offset =
                    (unsigned)std::distance(GTraits::child_begin(TargetNode), TargetIt);
                DestPort = static_cast<int>(Offset);
            }

            if (DTraits.getEdgeSourceLabel(Node, EI).empty())
                edgeidx = -1;

            emitEdge(static_cast<const void*>(Node), edgeidx,
                static_cast<const void*>(TargetNode), DestPort,
                DTraits.getEdgeAttributes(Node, EI, G));
        }
    }




    /// emitSimpleNode - Outputs a simple (non-record) node 
    void emitSimpleNode(const void* ID, const std::string& Attr,
        const std::string& Label, unsigned NumEdgeSources = 0,
        const std::vector<std::string>* EdgeSourceLabels = nullptr) {
        O << "\tNode" << ID << "[ ";
        if (!Attr.empty())
            O << Attr << ",";
        O << " label =\"";
        if (NumEdgeSources) O << "{";
        O << DOT::EscapeString(Label);
        if (NumEdgeSources) {
            O << "|{";

            for (unsigned i = 0; i != NumEdgeSources; ++i) {
                if (i) O << "|";
                O << "<s" << i << ">";
                if (EdgeSourceLabels) O << DOT::EscapeString((*EdgeSourceLabels)[i]);
            }
            O << "}}";
        }
        O << "\"];\n";
    }

    /// emitEdge - Output an edge from a simple node into the graph... 
    void emitEdge(const void* SrcNodeID, int SrcNodePort,
        const void* DestNodeID, int DestNodePort,
        const std::string& Attrs) {
        if (SrcNodePort > 64) return;             // Eminating from truncated part? 
        if (DestNodePort > 64) DestNodePort = 64;  // Targeting the truncated part? 

        O << "\tNode" << SrcNodeID;
        if (SrcNodePort >= 0)
            O << ":s" << SrcNodePort;
        O << " -> Node" << DestNodeID;
        if (DestNodePort >= 0 && DTraits.hasEdgeDestLabels())
            O << ":d" << DestNodePort;

        if (!Attrs.empty())
            O << "[" << Attrs << "]";
        O << ";\n";
    }

    /// getOStream - Get the raw output stream into the graph file. Useful to 
    /// write fancy things using addCustomGraphFeatures(). 
    raw_ostream& getOStream() {
        return O;
    }
};


};

#endif