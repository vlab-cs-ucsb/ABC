/*
 * GraphNode.cpp
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#include "GraphNode.h"

namespace Vlab {
namespace Theory {


GraphNode::GraphNode(int id)
  : id (id), flag (0) {
}

GraphNode::~GraphNode() {

}

int GraphNode::getID() {
  return id;
}

int GraphNode::getFlag() {
  return flag;
}

void GraphNode::setFlag(int f) {
  flag = f;
}

void GraphNode::addEdgeFlag(int f, GraphNode_ptr node) {
  flag = f;
  flagNodesMap[f].insert(node);
}

int GraphNode::getEdgeFlag(GraphNode_ptr node) {
  for (auto& it : flagNodesMap) {
    if (it.second.find(node) != it.second.end()) {
      return it.first;
    }
  }
  return 0;
}

bool GraphNode::isFlaggedEdge(int f, GraphNode_ptr node) {
  auto it = flagNodesMap.find(f);
  return (it->second.find(node) != it->second.end());
}

bool GraphNode::hasEdgeFlags() {
  return (flagNodesMap.size() != 0);
}

bool GraphNode::hasEdgeFlag(int f) {
  return (flagNodesMap.find(f) != flagNodesMap.end());
}

bool GraphNode::hasEdgeFlag(int f, GraphNode_ptr node) {
  auto it = flagNodesMap.find(f);
  if (it == flagNodesMap.end()) {
    return false;
  }
  return (it->second.find(node) != it->second.end());
}

void GraphNode::removeEdgeFlag(int f, GraphNode_ptr node) {
  auto it = flagNodesMap.find(f);
  it->second.erase(node);
  if (it->second.size() == 0) {
    flagNodesMap.erase(it);
  }

}

GraphNodeSet& GraphNode::getFlagNodes(int f) {
  return flagNodesMap[f];
}

std::map<int, GraphNodeSet>& GraphNode::getEdgeFlagMap() {
  return flagNodesMap;
}

void GraphNode::addNextNode(GraphNode_ptr node) {
  nextNodes.insert(node);
}

void GraphNode::addPrevNode(GraphNode_ptr node) {
  prevNodes.insert(node);
}

GraphNodeSet& GraphNode::getNextNodes() {
  return nextNodes;
}

bool GraphNode::hasNextNode(GraphNode_ptr node) {
  return (nextNodes.find(node) != nextNodes.end());
}

GraphNodeSet& GraphNode::getPrevNodes() {
  return prevNodes;
}

} /* namespace Theory */
} /* namespace Vlab */
