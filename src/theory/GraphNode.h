/*
 * GraphNode.h
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#ifndef THEORY_GRAPHNODE_H_
#define THEORY_GRAPHNODE_H_

#include <set>
#include <map>

namespace Vlab {
namespace Theory {

class GraphNode;
typedef GraphNode* GraphNode_ptr;
typedef std::set<GraphNode_ptr> GraphNodeSet;

class GraphNode {
public:
  GraphNode(int id);
  virtual ~GraphNode();

  int getID();
  int getFlag();
  void setFlag(int f);
  void addEdgeFlag(int f, GraphNode_ptr node);
  int getEdgeFlag(GraphNode_ptr node);
  bool isFlaggedEdge(int f, GraphNode_ptr node);
  bool hasEdgeFlags();
  bool hasEdgeFlag(int f);
  bool hasEdgeFlag(int f, GraphNode_ptr node);
  void removeEdgeFlag(int f, GraphNode_ptr node);
  GraphNodeSet& getFlagNodes(int f);
  std::map<int, GraphNodeSet>& getEdgeFlagMap();
  void addNextNode(GraphNode_ptr node);
  void addPrevNode(GraphNode_ptr node);
  GraphNodeSet& getNextNodes();
  GraphNodeSet& getPrevNodes();
  bool hasNextNode(GraphNode_ptr node);

protected:
  int id;
  int flag;
  GraphNodeSet nextNodes;
  GraphNodeSet prevNodes;
  std::map<int, GraphNodeSet> flagNodesMap;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_GRAPHNODE_H_ */
