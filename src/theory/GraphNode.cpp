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

void GraphNode::addNextNode(GraphNode_ptr node) {
  nextNodes.insert(node);
}

void GraphNode::addPrevNode(GraphNode_ptr node) {
  prevNodes.insert(node);
}

GraphNodeSet& GraphNode::getNextNodes() {
  return nextNodes;
}

GraphNodeSet& GraphNode::getPrevNodes() {
  return prevNodes;
}

} /* namespace Theory */
} /* namespace Vlab */
