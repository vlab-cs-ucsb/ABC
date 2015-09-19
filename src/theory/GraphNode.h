/*
 * GraphNode.h
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#ifndef THEORY_GRAPHNODE_H_
#define THEORY_GRAPHNODE_H_

#include <set>

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
  void addNextNode(GraphNode_ptr node);
  void addPrevNode(GraphNode_ptr node);
  GraphNodeSet& getNextNodes();
  GraphNodeSet& getPrevNodes();

protected:
  int id;
  int flag;
  GraphNodeSet nextNodes;
  GraphNodeSet prevNodes;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_GRAPHNODE_H_ */
