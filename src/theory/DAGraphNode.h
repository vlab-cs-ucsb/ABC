/*
 * DAGraphNode.h
 *
 *  Created on: Sep 16, 2015
 *      Author: baki
 */

#ifndef THEORY_DAGRAPHNODE_H_
#define THEORY_DAGRAPHNODE_H_

#include <set>

#include "GraphNode.h"

namespace Vlab {
namespace Theory {

class DAGraphNode;
typedef DAGraphNode* DAGraphNode_ptr;
typedef std::set<DAGraphNode_ptr> DAGraphNodeSet;

class DAGraphNode {
public:
  DAGraphNode(int id);
  virtual ~DAGraphNode();

  int getID();
  int getFlag();
  void setFlag(int f);
  void addSubNode(GraphNode_ptr node);
  GraphNodeSet& getSubNodes();
  GraphNodeSet getNextSubNodes();
  GraphNodeSet getPrevSubNodes();
  void addNextNode(DAGraphNode_ptr scc_node);
  void addPrevNode(DAGraphNode_ptr scc_node);
  DAGraphNodeSet& getNextNodes();
  DAGraphNodeSet& getPrevNodes();

  bool hasFlag(int f);

protected:
  int id;
  int flag;
  GraphNodeSet nodes;
  DAGraphNodeSet nextSCCNodes;
  DAGraphNodeSet prevSCCNodes;
};

} /* namespace Theory */
} /* namespace Vlab */

#endif /* THEORY_DAGRAPHNODE_H_ */
