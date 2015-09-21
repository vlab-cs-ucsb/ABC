/*
 * Graph.h
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#ifndef THEORY_GRAPH_H_
#define THEORY_GRAPH_H_

#include <iostream>
#include <sstream>
#include <fstream>
#include <map>

#include "GraphNode.h"

namespace Vlab {
namespace Theory {

class Graph;
typedef Graph* Graph_ptr;
typedef std::map<int, GraphNode_ptr> GraphNodeMap;

class Graph {
public:
  Graph();
  virtual ~Graph();

  void setStartNode(GraphNode_ptr);
  GraphNode_ptr getStartNode();
  void setSinkNode(GraphNode_ptr);
  GraphNode_ptr getSinkNode();
  GraphNode_ptr getNode(int id);
  bool addNode(GraphNode_ptr);
  void addFinalNode(GraphNode_ptr);
  GraphNodeSet& getFinalNodes();

  int getNumOfNodes();
  GraphNodeMap& getNodeMap();

  void removeNode(GraphNode_ptr);
  void removeNodes(GraphNodeSet&);
  void resetFinalNodesToFlag(int flag);

  bool isStartNode(GraphNode_ptr);
  bool isSinkNode(GraphNode_ptr);
  bool isFinalNode(GraphNode_ptr);

  void toDot(bool print_sink = false, std::ostream& out = std::cout);
  void inspectGraph(bool print_sink = false);

protected:
  GraphNode_ptr startNode;
  GraphNode_ptr sinkNode;
  GraphNodeSet finalNodes;
  GraphNodeMap nodes;

private:
  static int name_counter;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_GRAPH_H_ */
