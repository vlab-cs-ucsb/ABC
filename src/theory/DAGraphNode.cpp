/*
 * DAGraphNode.cpp
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#include "DAGraphNode.h"

namespace Vlab {
namespace Theory {

DAGraphNode::DAGraphNode(int id) :
      id (id), flag (0) { }

DAGraphNode::~DAGraphNode() {
}

int DAGraphNode::getID() {
  return id;
}

int DAGraphNode::getFlag() {
  return flag;
}

void DAGraphNode::setFlag(int f) {
  flag = f;
}

void DAGraphNode::addSubNode(GraphNode_ptr node) {
  if (node->getFlag() > flag) {
    flag = node->getFlag();
  }
  nodes.insert(node);
}

GraphNodeSet& DAGraphNode::getSubNodes() {
  return nodes;
}

GraphNodeSet DAGraphNode::getNextSubNodes() {
  GraphNodeSet next_sub_nodes;
  for (GraphNode_ptr node : nodes) {
    for (GraphNode_ptr next_node : node->getNextNodes()) {
      if (nodes.find(next_node) == nodes.end()) {
        next_sub_nodes.insert(next_node);
      }
    }
  }
  return next_sub_nodes;
}

GraphNodeSet DAGraphNode::getPrevSubNodes() {
  GraphNodeSet prev_sub_nodes;
  for (GraphNode_ptr node : nodes) {
    for (GraphNode_ptr prev_node : node->getPrevNodes()) {
      if (nodes.find(prev_node) == nodes.end()) {
        prev_sub_nodes.insert(prev_node);
      }
    }
  }
  return prev_sub_nodes;
}

GraphNodeSet DAGraphNode::getOutGoingSubNodes() {
  GraphNodeSet out_sub_nodes;
  for (GraphNode_ptr node : nodes) {
    for (GraphNode_ptr next_node : node->getNextNodes()) {
      if (nodes.find(next_node) == nodes.end()) {
        out_sub_nodes.insert(node);
      }
    }
  }
  return out_sub_nodes;
}

GraphNodeSet DAGraphNode::getInComingSubNodes() {
  GraphNodeSet in_sub_nodes;
  for (GraphNode_ptr node : nodes) {
    for (GraphNode_ptr prev_node : node->getPrevNodes()) {
      if (nodes.find(prev_node) == nodes.end()) {
        in_sub_nodes.insert(node);
      }
    }
  }
  return in_sub_nodes;
}

void DAGraphNode::addNextNode(DAGraphNode_ptr scc_node) {
  nextSCCNodes.insert(scc_node);
}

void DAGraphNode::addPrevNode(DAGraphNode_ptr scc_node) {
  prevSCCNodes.insert(scc_node);
}

DAGraphNodeSet& DAGraphNode::getNextNodes() {
  return nextSCCNodes;
}

DAGraphNodeSet& DAGraphNode::getPrevNodes() {
  return prevSCCNodes;
}

void DAGraphNode::setEdgeFlag(int f, DAGraphNode_ptr scc_node) {
  flag = f;
  flagNodesMap[f].insert(scc_node);
}

bool DAGraphNode::hasEdgeFlag(int f) {
  if (flag == f) {
    return true;
  }
  return (flagNodesMap.find(f) != flagNodesMap.end());
}

int DAGraphNode::getEdgeFlag(DAGraphNode_ptr scc_node) {
  for (auto& it : flagNodesMap) {
    if (it.second.find(scc_node) != it.second.end()) {
      return it.first;
    }
  }
  return 0;
}

DAGraphNodeSet& DAGraphNode::getFlagNodes(int f) {
  return flagNodesMap[f];
}

GraphNodeSet DAGraphNode::getFlagSubNodes(int f) {
  GraphNodeSet sub_flag_nodes;
  for (GraphNode_ptr node : nodes) {
    GraphNodeSet node_flags = node->getFlagNodes(f);
    sub_flag_nodes.insert(node_flags.begin(), node_flags.end());
  }
  return sub_flag_nodes;
}

std::map<int, DAGraphNodeSet>& DAGraphNode::getFlagNodeMap() {
  return flagNodesMap;
}

} /* namespace Theory */
} /* namespace Vlab */
