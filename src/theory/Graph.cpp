/*
 * Graph.cpp
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#include "Graph.h"

namespace Vlab {
namespace Theory {

int Graph::name_counter = 0;

Graph::Graph() :
      startNode (nullptr), sinkNode (nullptr) {
}

Graph::~Graph() {
  // TODO Auto-generated destructor stub
}

void Graph::setStartNode(GraphNode_ptr node) {
  startNode = node;
  addNode(node);
}

GraphNode_ptr Graph::getStartNode() {
  return startNode;
}

void Graph::setSinkNode(GraphNode_ptr node) {
  sinkNode = node;
  addNode(node);
}

GraphNode_ptr Graph::getSinkNode() {
  return sinkNode;
}

GraphNode_ptr Graph::getNode(int id) {
  GraphNode_ptr node = nullptr;
  auto it = nodes.find(id);
  if (it != nodes.end()) {
    node = it->second;
  }
  return node;
}

bool Graph::addNode(GraphNode_ptr node) {
  auto result = nodes.insert(std::make_pair(node->getID(), node));
  return result.second;
}

void Graph::addFinalNode(GraphNode_ptr node) {
  finalNodes.insert(node);
  addNode(node);
}

GraphNodeSet& Graph::getFinalNodes() {
  return finalNodes;
}

int Graph::getNumOfNodes() {
  return nodes.size();
}

GraphNodeMap& Graph::getNodeMap() {
  return nodes;
}

void Graph::removeNode(GraphNode_ptr node) {
  nodes.erase(node->getID());
  finalNodes.erase(node);
  for (auto prev_node : node->getPrevNodes()) {
    prev_node->getNextNodes().erase(node);
    for (auto& it : prev_node->getEdgeFlagMap()) {
      it.second.erase(node);
    }
  }
}

void Graph::removeNodes(GraphNodeSet& nodes) {
  for (auto& node : nodes) {
    removeNode(node);
    delete node;
  }
}

void Graph::resetFinalNodesToFlag(int flag) {
  finalNodes.clear();
  for (auto& entry : nodes) {
    if (entry.second->hasEdgeFlag(flag)) {
      finalNodes.insert(entry.second);
    }
  }
}

bool Graph::isStartNode(GraphNode_ptr node) {
  return (startNode == node);
}

bool Graph::isSinkNode(GraphNode_ptr node) {
  return (sinkNode == node);
}

bool Graph::isFinalNode(GraphNode_ptr node) {
  auto it = finalNodes.find(node);
  return (it != finalNodes.end());
}

void Graph::toDot(bool print_sink, std::ostream& out) {

  print_sink = print_sink || (nodes.size() == 1 and finalNodes.size() == 0);
  out << "digraph MONA_DFA {\n"
      " rankdir = LR;\n "
      " center = true;\n"
      " size = \"700.5,1000.5\";\n"
      " edge [fontname = Courier];\n"
      " node [height = .5, width = .5];\n"
      " node [shape = doublecircle];";

  for (auto& node : finalNodes) {
      out << " " << node->getID() << ";";
  }

  out << "\n node [shape = circle];";

  for (auto& entry : nodes) {
    if ((not print_sink) && sinkNode == entry.second) {
      continue;
    }
    out << " " << entry.first << ";";
  }

  out << "\n init [shape = plaintext, label = \"\"];\n" <<
      " init -> " << startNode->getID() << ";\n";

  for (auto& entry : nodes) {
    if ((not print_sink) && sinkNode == entry.second) {
      continue;
    }
    for (auto& next_node : entry.second->getNextNodes()) {
      if ((not print_sink) && sinkNode == next_node) {
        continue;
      }
      out << " " << entry.first << " -> " << next_node->getID();
      int node_flag = entry.second->getEdgeFlag(next_node);
      if ( node_flag != 0 ) {
        out << "[label = \"" << node_flag << "\"]";
      }
      out << ";\n";
    }
  }
  out << "}" << std::endl;
}

int Graph::inspectGraph(bool print_sink) {
  std::stringstream file_name;
  file_name << "./output/inspect_graph_" << name_counter++ << ".dot";
  std::string file = file_name.str();
  std::ofstream outfile(file.c_str());
  if (!outfile.good()) {
    std::cout << "cannot open file: " << file_name << std::endl;
    exit(2);
  }
  toDot(print_sink, outfile);
  std::string dot_cmd("xdot " + file + " &");
  return std::system(dot_cmd.c_str());
}

} /* namespace Theory */
} /* namespace Vlab */


