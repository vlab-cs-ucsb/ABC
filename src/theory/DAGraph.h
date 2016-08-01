/*
 * DAGraph.h
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#ifndef THEORY_DAGRAPH_H_
#define THEORY_DAGRAPH_H_

#include <iostream>
#include <sstream>
#include <fstream>
#include <map>
#include <stack>

#include "DAGraphNode.h"
#include "Graph.h"

namespace Vlab {
namespace Theory {

class DAGraph;
typedef DAGraph* DAGraph_ptr;
typedef std::map<int, DAGraphNode_ptr> DAGraphNodeMap;

class DAGraph {
public:
  DAGraph();
  DAGraph(Graph_ptr graph);
  virtual ~DAGraph();

  void setStartNode(DAGraphNode_ptr);
  DAGraphNode_ptr getStartNode();
  void setSinkNode(DAGraphNode_ptr);
  DAGraphNode_ptr getSinkNode();
  DAGraphNode_ptr getNode(int id);
  bool addNode(DAGraphNode_ptr);
  void addFinalNode(DAGraphNode_ptr);
  DAGraphNodeSet& getFinalNodes();
  void resetFinalNodesToFlag(int flag);

  DAGraphNodeMap& getNodeMap();

  bool isMemberOfSCC(GraphNode_ptr, DAGraphNode_ptr);
  void removeNode(DAGraphNode_ptr);
  Graph_ptr getRawGraph();
  GraphNodeSet selectSubFinalNodes(GraphNodeSet& nodes);

  void toDot(bool print_sink = false, std::ostream& out = std::cout);
  int inspectGraph(bool print_sink = false);

protected:
  Graph_ptr graph;
  DAGraphNode_ptr startNode;
  DAGraphNode_ptr sinkNode;
  DAGraphNodeSet finalNodes;
  DAGraphNodeMap nodes;
  std::map<GraphNode_ptr, DAGraphNode_ptr> subNodes;

private:
  void findSCCs(int u, int *disc, int *low, std::stack<int> *st, bool *is_stack_member, int& time);
  static int name_counter;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_DAGRAPH_H_ */
