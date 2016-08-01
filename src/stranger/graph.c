/*
 * Stranger
 * Copyright (C) 2013-2014 University of California Santa Barbara.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the  Free Software
 * Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335,
 * USA.
 *
 * Authors: Muath Alkhalaf
 */
 
#include "stranger.h"
#include "stranger_lib_internal.h"
#include "utility.h"
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <limits.h>
#include "locale.h"

/**********************************************************************/
/*                  Getting transition relation                       */
/**********************************************************************/
/*
 TODO: should return transition relation with the sink in it then add a function to
 remove the sink.
 This will break Tarjan length algorithm so it should be changed to take relation
 after removing the sink.
 it will also break pre_add_slashes which should not do any shifting
 */
pTransitionRelation dfaGetTransitionRelation(DFA *M){
    unsigned state, degree, nextState, i;
    state = degree = nextState = 0;
    paths state_paths, pp;
    
    int sink = find_sink(M);
    assert(sink >= 0);//assert that there is a sink
    
    pTransitionRelation p_transitionRelation = (pTransitionRelation) malloc(sizeof(transitionRelation));
    p_transitionRelation->reverse = false;
    p_transitionRelation->selfCycles = false;
    p_transitionRelation->sink = (unsigned)sink;
    p_transitionRelation->num_of_nodes = M->ns - 1;
    p_transitionRelation->num_of_edges = 0;
    p_transitionRelation->adjList = (unsigned**) malloc((size_t)
                                                        (p_transitionRelation->num_of_nodes) * sizeof(unsigned*));
    mem_zero(p_transitionRelation->adjList, (size_t) p_transitionRelation->num_of_nodes * sizeof(unsigned*) );
    p_transitionRelation->degrees = (t_st_word*) malloc((size_t)
                                                             (p_transitionRelation->num_of_nodes) * sizeof(t_st_word));
    mem_zero(p_transitionRelation->degrees, (size_t) p_transitionRelation->num_of_nodes * sizeof(t_st_word));
    bool *nextStates = (bool*) malloc((size_t) (p_transitionRelation->num_of_nodes) * sizeof(bool));
    
    unsigned numOfAcceptStates = 0;
    // a heuristic assuming 1/20th of states are accepting
    unsigned acceptSizeTemp = (M->ns < 100)? 4 : roundToNextPow2(M->ns / 20);
    p_transitionRelation->acceptsSize = (p_transitionRelation->num_of_nodes < acceptSizeTemp)? p_transitionRelation->num_of_nodes : acceptSizeTemp;
    p_transitionRelation->accepts = (unsigned *) mem_alloc((size_t) p_transitionRelation->acceptsSize * sizeof(unsigned));
    mem_zero(p_transitionRelation->accepts, (size_t) p_transitionRelation->acceptsSize * sizeof(unsigned));
    
    for (i = 0; i < M->ns; i++){
        if (M->f[i] == 1){
            p_transitionRelation->accepts[numOfAcceptStates++] = (i < sink)? i : i - 1;
            if (numOfAcceptStates == p_transitionRelation->acceptsSize){
                unsigned acceptSizeTemp = p_transitionRelation->acceptsSize * 2;
                p_transitionRelation->acceptsSize = (p_transitionRelation->num_of_nodes < acceptSizeTemp)? p_transitionRelation->num_of_nodes : acceptSizeTemp;
                p_transitionRelation->accepts = (unsigned*) mem_resize(p_transitionRelation->accepts, (size_t) p_transitionRelation->acceptsSize * sizeof(unsigned));
                mem_zero(p_transitionRelation->accepts + numOfAcceptStates, (size_t) (p_transitionRelation->acceptsSize - numOfAcceptStates) * sizeof(unsigned));
            }
        }
        
        if (sink == i)
            continue;
        else if (sink < i)
            state = i - 1;//shift state
        else
            state = i;
//        printf("i = %d for state = %u\n", i, state);
        /*******************  find node degree *********************/
        memset(nextStates, false, sizeof(bool) * (p_transitionRelation->num_of_nodes));
        state_paths = pp = make_paths(M->bddm, M->q[i]);
        while (pp) {
            if (pp->to == i)
                p_transitionRelation->selfCycles = true;
            unsigned to = (sink < pp->to)? pp->to - 1 : pp->to;
            if (pp->to != sink){
                if (nextStates[to] == false){
                    nextStates[to] = true;
                    p_transitionRelation->degrees[state]++;
                    p_transitionRelation->num_of_edges++;
                }
            }
            pp = pp->next;
        }
        kill_paths(state_paths);
        /*******************  allocate node's adjacency list and fill it up *********************/
        if (p_transitionRelation->degrees[state] == 0) {
            p_transitionRelation->adjList[state]  = NULL;
        }
        else {
            p_transitionRelation->adjList[state] = (unsigned *) malloc((size_t) (p_transitionRelation->degrees[state]) * sizeof(unsigned) );
            mem_zero(p_transitionRelation->adjList[state],(size_t) (p_transitionRelation->degrees[state]) * sizeof(unsigned));
            for (nextState = 0, degree = 0; nextState < p_transitionRelation->num_of_nodes; nextState++) {
                if (nextStates[nextState] == true){
                    assert(degree < p_transitionRelation->degrees[state]);
                    p_transitionRelation->adjList[state][degree] = nextState;
                    degree++;
                }
            }
        }
    }
    
    p_transitionRelation->acceptsSize = numOfAcceptStates;
    p_transitionRelation->accepts = (unsigned*) mem_resize((p_transitionRelation->accepts), ((p_transitionRelation->acceptsSize) * sizeof(unsigned)));

    qsort(p_transitionRelation->accepts, p_transitionRelation->acceptsSize, sizeof(unsigned), intcmpfunc);
    
    free(nextStates);
    return p_transitionRelation;
}

pTransitionRelation dfaGetReverseTransitionRelation(DFA *M){
    assert(M != NULL);
    return get_reverse_transition_relation_helper(M, NULL);
}

pTransitionRelation dfaReverseTransitionRelation(pTransitionRelation p_transitionRelation){
    assert(p_transitionRelation != NULL);
    return get_reverse_transition_relation_helper(NULL, p_transitionRelation);
}

pTransitionRelation get_reverse_transition_relation_helper(DFA *M, pTransitionRelation p_transitionRelation){
    unsigned state, degree, nextStateIndex, nextState;
    state = degree = nextStateIndex = nextState = 0;
    
    assert(!(M == NULL && p_transitionRelation == NULL));
    assert(!(M != NULL && p_transitionRelation != NULL));
    
    p_transitionRelation = (M == NULL)? p_transitionRelation : dfaGetTransitionRelation(M);
    
    const unsigned num_of_nodes = (M == NULL)? p_transitionRelation->num_of_nodes : M->ns - 1;
    assert(num_of_nodes == p_transitionRelation->num_of_nodes);
    
    
    unsigned **reverseAdjList = (unsigned**) malloc((size_t)
                                                    num_of_nodes * sizeof(unsigned*));
    mem_zero(reverseAdjList, (size_t) num_of_nodes * sizeof(unsigned*) );
    t_st_word *reverseDegrees = (t_st_word*) malloc((size_t)
                                                              num_of_nodes * sizeof(t_st_word));
    mem_zero(reverseDegrees, (size_t) num_of_nodes * sizeof(t_st_word));
    
    /*******************  find node degree *********************/
    for (state = 0; state < num_of_nodes; state++){
        unsigned *nextStates = p_transitionRelation->adjList[state];
        t_st_word nextStatesSize = p_transitionRelation->degrees[state];
        for (nextStateIndex = 0; nextStateIndex < nextStatesSize; nextStateIndex++){
            nextState = nextStates[nextStateIndex];
            reverseDegrees[nextState]++;
        }
    }
    
    /*******************  allocate node's adjacency list and fill up *********************/
    t_st_word *degreeCounters = (t_st_word *) malloc((size_t) num_of_nodes * sizeof(t_st_word));
    mem_zero(degreeCounters, (size_t) num_of_nodes * sizeof(t_st_word));
    
    for (state = 0; state < num_of_nodes; state++){
        unsigned *nextStates = p_transitionRelation->adjList[state];
        t_st_word nextStatesSize = p_transitionRelation->degrees[state];
        for (nextStateIndex = 0; nextStateIndex < nextStatesSize; nextStateIndex++){
            nextState = nextStates[nextStateIndex];
            t_st_word degree = reverseDegrees[nextState];
            //start state may have reverse degree of 0
            if (degree != 0){
                //first time then allocate reverse adjList
                if (reverseAdjList[nextState] == NULL){
                    reverseAdjList[nextState] = (unsigned *) mem_alloc((size_t) degree * sizeof(unsigned));
                    mem_zero(reverseAdjList[nextState], (size_t) degree * sizeof(unsigned));
                    
                }
                t_st_word degreeCounter = degreeCounters[nextState]++;
                reverseAdjList[nextState][degreeCounter] = state;
            }
        }
    }
    
    pTransitionRelation p_reverseTransitionRelation = (pTransitionRelation) malloc(sizeof(transitionRelation));
    p_reverseTransitionRelation->reverse = true;
    p_reverseTransitionRelation->sink = p_transitionRelation->sink;
    p_reverseTransitionRelation->num_of_nodes = num_of_nodes;
    p_reverseTransitionRelation->adjList = reverseAdjList;
    p_reverseTransitionRelation->degrees = reverseDegrees;
    p_reverseTransitionRelation->acceptsSize = 0;
    p_reverseTransitionRelation->accepts = NULL;

    if (M != NULL)
        dfaFreeTransitionRelation(p_transitionRelation);
    free(degreeCounters);
    
    return p_reverseTransitionRelation;
}


bool dfaIsNextState(pTransitionRelation p_transitionRelation, unsigned currentState, unsigned nextState){
    assert(p_transitionRelation->reverse == false);
    unsigned nextStateIndex;
    for (nextStateIndex = 0; nextStateIndex < p_transitionRelation->degrees[currentState]; nextStateIndex++){
        if (p_transitionRelation->adjList[currentState][nextStateIndex] == currentState) {
            return true;
        }
    }
    return false;
}

bool dfaIsPrevState(pTransitionRelation p_transitionRelation, unsigned currentState, unsigned prevState){
    assert(p_transitionRelation->reverse == true);
    if (p_transitionRelation->reverse){
        unsigned nextStateIndex;
        for (nextStateIndex = 0; nextStateIndex < p_transitionRelation->degrees[currentState]; nextStateIndex++){
            if (p_transitionRelation->adjList[currentState][nextStateIndex] == currentState) {
                return true;
            }
        }
    }
    return false;
}


void dfaFreeTransitionRelation(pTransitionRelation p_transitionRelation){
    int state;

    for (state = 0; state < p_transitionRelation->num_of_nodes; state++){
    	if (p_transitionRelation->degrees[state] > 0)
            free(p_transitionRelation->adjList[state]);
    }

    free(p_transitionRelation->adjList);
    free(p_transitionRelation->degrees);
    if (p_transitionRelation->acceptsSize > 0)
        free(p_transitionRelation->accepts);
    free(p_transitionRelation);
}


unsigned dfaGetDegree(DFA *M, unsigned state){
    int ssink = find_sink(M);
    unsigned sink;
    if (ssink == -1)
        sink = UINT_MAX;
    else
        sink = ssink;
    assert(state != sink);
    
    paths state_paths, pp;
    unsigned nextStatesSize = 16, nextStatesIndex = 0, degree = 0;
    unsigned *nextStates = (unsigned*) malloc((size_t) (nextStatesSize) * sizeof(unsigned));
    mem_zero(nextStates, (size_t) (nextStatesSize) * sizeof(unsigned));
    /*******************  find node degree *********************/
    state_paths = pp = make_paths(M->bddm, M->q[state]);
    while (pp) {
        if (pp->to != sink){
            bool found = false;
            for (nextStatesIndex = 0; nextStatesIndex < degree; nextStatesIndex++) {
                if (pp->to == nextStates[nextStatesIndex]){
                    found = true;
                    break;
                }
            }
            if (!found){
                if (degree < nextStatesSize){
                    nextStates[degree] = pp->to;
                }
                else {
                    unsigned oldSize = nextStatesSize;
                    nextStatesSize *= 2;
                    nextStates = (unsigned*) mem_resize(nextStates, (size_t)(nextStatesSize) * sizeof(unsigned));
                    mem_zero(nextStates + oldSize, (size_t) (nextStatesSize - oldSize) * sizeof(unsigned));
                    nextStates[degree] = pp->to;
                }
                degree++;
            }
        }
        pp = pp->next;
    }
    kill_paths(state_paths);
    free(nextStates);
    return degree;
}

unsigned dfaGetMaxDegree(DFA *M, unsigned *p_maxState){
    int ssink = find_sink(M);
    unsigned sink;
    if (ssink == -1)
        sink = UINT_MAX;
    else
        sink = ssink;
    
    unsigned state = 0, maxState = 0, maxDegree = 0, degree = 0;
    
    for (state = 0; state < M->ns; state++){
        degree = dfaGetDegree(M, state);
        if (maxDegree < degree){
            maxDegree = degree;
            maxState = state;
        }
    }
    
    *p_maxState = maxState;
    return maxDegree;
}

void dfaShiftTransitionRelation(pTransitionRelation p_transitionRelation, int sink){
    assert(p_transitionRelation != NULL);
    int i, j;

    p_transitionRelation->num_of_nodes++;
    p_transitionRelation->degrees = mem_resize(p_transitionRelation->degrees, p_transitionRelation->num_of_nodes * sizeof(t_st_word));
    p_transitionRelation->adjList = mem_resize(p_transitionRelation->adjList, p_transitionRelation->num_of_nodes * sizeof(unsigned*));

    for (i = p_transitionRelation->num_of_nodes - 1; i >= 0; i--){
        if (i > sink) {
            p_transitionRelation->adjList[i] = p_transitionRelation->adjList[i - 1];
            p_transitionRelation->degrees[i] = p_transitionRelation->degrees[i - 1];
        }
        else if (i == sink){
            p_transitionRelation->adjList[i] = NULL;
            p_transitionRelation->degrees[i] = 0;
        }
        if (p_transitionRelation->degrees[i] == 0){
            continue;
        }
        for (j = 0; j < p_transitionRelation->degrees[i]; j++){
            p_transitionRelation->adjList[i][j] = (p_transitionRelation->adjList[i][j] < p_transitionRelation->sink) ? p_transitionRelation->adjList[i][j] : p_transitionRelation->adjList[i][j] + 1;
        }
    }

}

void dfaPrintTransitionRelation(pTransitionRelation p_transitionRelation){
    assert(p_transitionRelation != NULL);
    printf("**********************************\n");
    printf("*     Transition Relation        *\n");
    printf("**********************************\n");
    printf("from | to\n");
    printf("-----|----------------------------\n");
    unsigned i, j,state;
    for (i = 0; i < p_transitionRelation->num_of_nodes; i++){
        state = (i < p_transitionRelation->sink)? i : i + 1;
        printf("%5u| ",state);
        if (p_transitionRelation->degrees[i] == 0){
            printf("\n");
            continue;
        }
        for (j = 0; j < p_transitionRelation->degrees[i]; j++){
            state = (p_transitionRelation->adjList[i][j] < p_transitionRelation->sink) ? p_transitionRelation->adjList[i][j] : p_transitionRelation->adjList[i][j] + 1;
            if (j == 0)
                printf("%u", state);
            else
                printf(", %u", state);
        }
        printf("\n");
    }
    printf("----------------------------------\n");
}

void dfaPrintTransitionRelationNoShift(pTransitionRelation p_transitionRelation){
    assert(p_transitionRelation != NULL);
    printf("**********************************\n");
    printf("*     Transition Relation        *\n");
    printf("**********************************\n");
    printf("from | to\n");
    printf("-----|----------------------------\n");
    unsigned i, j,state;
    for (i = 0; i < p_transitionRelation->num_of_nodes; i++){
        state = i;
        printf("%5u| ",state);
        if (p_transitionRelation->degrees[i] == 0){
            printf("\n");
            continue;
        }
        for (j = 0; j < p_transitionRelation->degrees[i]; j++){
            state = p_transitionRelation->adjList[i][j];
            if (j == 0)
                printf("%u", state);
            else
                printf(", %u", state);
        }
        printf("\n");
    }
    printf("----------------------------------\n");
}



/****************** Find Strongly Connected Component ****************/

#define WHITE 0
#define GRAY 1
#define BLACK 2

int numOfNodes;  // number of nodes
int numOfEdges;  // number of edges
struct edge {
    int tail,head,type;
};
typedef struct edge edgeType;
edgeType *edgeTab;
int *firstEdge;  // Table indicating first in range of edges with a common tail

int *vertexStatus,*secondDFSrestarts;

int tailThenHead(const void* xin, const void* yin)
// Used in calls to qsort() and bsearch() for dfa_to_graph()
{
    int result;
    edgeType *x,*y;
    
    x=(edgeType*) xin;
    y=(edgeType*) yin;
    result = x->tail - y->tail;
    if (result!=0)
        return result;
    else
        return x->head - y->head;
}

bool dfa_to_graph(DFA *M)
{
    int i,j;
    bool selfCyclesFound = false;
    pTransitionRelation p_transitionRelation = dfaGetTransitionRelation(M);
    //if we detect a self cycle then that is enough to abort looking for cycles
    if (p_transitionRelation->selfCycles) {
    	dfaFreeTransitionRelation(p_transitionRelation);
    	return true;
    }
        
//    dfaPrintTransitionRelation(p_transitionRelation);
    numOfNodes = p_transitionRelation->num_of_nodes;
    numOfEdges = p_transitionRelation->num_of_edges;

//    printf("Number of vertices = %d ,edges = %d\n",numOfNodes,numOfEdges);

    edgeTab=(edgeType*) malloc((size_t) numOfEdges * sizeof(edgeType));
    if (!edgeTab)
    {
        printf("edgeTab malloc failed %dn",__LINE__);
        exit(0);
    }
    
    // read edges
    int e = 0;
    for (i=0; i < numOfNodes; i++)
    {
        unsigned *nodeAdjList = p_transitionRelation->adjList[i];
        for (j = 0; j < p_transitionRelation->degrees[i]; j++){
            edgeTab[e].tail=i;
            edgeTab[e].head=nodeAdjList[j];
            e++;
        }
    }
    assert(e == numOfEdges);
    
    // sort edges
    qsort(edgeTab,numOfEdges,sizeof(edgeType),tailThenHead);
    
    // Coalesce duplicates into a single edge
    j=0;
    for (i=1; i<numOfEdges; i++)
        if (edgeTab[j].tail==edgeTab[i].tail
            && edgeTab[j].head==edgeTab[i].head) {

        }
        else
        {
            j++;
            edgeTab[j].tail=edgeTab[i].tail;
            edgeTab[j].head=edgeTab[i].head;
        }
    numOfEdges=j+1;
    
    // For each vertex as a tail, determine first in range of edgeTab entries
    firstEdge=(int*) malloc((numOfNodes+1)*sizeof(int));
    if (!firstEdge)
    {
        printf("malloc failed %dn",__LINE__);
        exit(0);
    }
    j=0;
    for (i=0; i<numOfNodes; i++)
    {
        firstEdge[i]=j;
        for ( ;
             j<numOfEdges && edgeTab[j].tail==i;
             j++)
            ;
    }
    firstEdge[numOfNodes]=numOfEdges;
    
    dfaFreeTransitionRelation(p_transitionRelation);
    return false;
}

int finishIndex;

void DFSvisit(int node)
{
    int i,v;
    
    vertexStatus[node]=GRAY;
    
    for (i=firstEdge[node];i<firstEdge[node+1];i++)
    {
        v=edgeTab[i].head;
        if (vertexStatus[v]==WHITE)
            DFSvisit(v);
    }
    vertexStatus[node]=BLACK;
    secondDFSrestarts[--finishIndex]=node;
}

void reverseEdges()
{
    int a,b,i,j;
    
    for (i=0; i<numOfEdges; i++)
    {
        a=edgeTab[i].tail;
        b=edgeTab[i].head;
        edgeTab[i].tail=b;
        edgeTab[i].head=a;
    }
    
    // sort edges
    qsort(edgeTab,numOfEdges,sizeof(edgeType),tailThenHead);
    
    // For each vertex as a tail, determine first in range of edgeTab entries
    if (!firstEdge)
    {
        printf("malloc failed %dn",__LINE__);
        exit(0);
    }
    j=0;
    for (i=0; i<numOfNodes; i++)
    {
        firstEdge[i]=j;
        for ( ;
             j<numOfEdges && edgeTab[j].tail==i;
             j++)
            ;
    }
    firstEdge[numOfNodes]=numOfEdges;
}

//returns true if it is called more than once. This indicates
//an SCC of more than one node
bool DFSvisit2(int node, int sink)
{
    int i,v;
    bool multipleCalls = false;
//    int state = (node < sink)? node : node + 1;
//    printf("%d\n",state); // Indicate that node is in SCC for this restart
    vertexStatus[node]=GRAY;
    
    for (i=firstEdge[node];i<firstEdge[node+1];i++)
    {
        v=edgeTab[i].head;
        if (vertexStatus[v]==WHITE){
            multipleCalls = true;
            DFSvisit2(v, sink);
        }
    }
    vertexStatus[node]=BLACK;
    return multipleCalls;
}

bool isLengthFiniteTarjan(DFA *M, int var, int *indices)
{
    if (check_emptiness_minimized(M) || checkOnlyEmptyString(M, var, indices)) {
        return true;
    }

    int node;
    int SCCcount=0;
    bool sccFound = false;
    
    // we need sink just for printing
    int sink = find_sink(M);
    assert(sink >= 0);
    
    // convert dfa->graph, if there is any self cycle, stop and return
    if (dfa_to_graph(M)){
        return false;
    }

    
    vertexStatus=(int*) malloc(numOfNodes*sizeof(int));
    secondDFSrestarts=(int*) malloc(numOfNodes*sizeof(int));
    if (!vertexStatus || !secondDFSrestarts)
    {
        printf("malloc failedn");
        exit(0);
    }
    // DFS code
    for (node=0;node<numOfNodes;node++)
        vertexStatus[node]=WHITE;
    finishIndex=numOfNodes;
    for (node=0;node<numOfNodes;node++)
        if (vertexStatus[node]==WHITE)
            DFSvisit(node);
    
    reverseEdges();
    
    // DFS code
    for (node=0;node<numOfNodes;node++)
        vertexStatus[node]=WHITE;
    for (node=0;node<numOfNodes;node++)
        if (vertexStatus[secondDFSrestarts[node]]==WHITE)
        {
            SCCcount++;
//            printf("Strongly Connected Component %d\n",SCCcount);
            if(DFSvisit2(secondDFSrestarts[node], sink) == true){
//                printf("Found a real SCC on node %d\n", node);
                sccFound = true;
            }
            
        }
    
    free(edgeTab);
    free(firstEdge);
    free(vertexStatus);
    free(secondDFSrestarts);
    return !sccFound;
}


typedef struct _NodeLengths {
    unsigned *lengths;
    unsigned size;
    unsigned index;
    bool visited;
    unsigned long long numOfPaths;
} NodeLengths, *P_NodeLengths;

void freeNodeLengths(P_NodeLengths nodeLengths){
    if (nodeLengths->size > 0)
        free(nodeLengths->lengths);
    free(nodeLengths);
}


bool isNewLength(P_NodeLengths nodeLengths, unsigned len){
    int i;
    for (i = 0; i < nodeLengths->index; i++){
        if (len == nodeLengths->lengths[i])
            return false;
    }
    return true;
}

void addLengthToNodeLengths(P_NodeLengths nodeLengths, unsigned len){
    assert(!(nodeLengths->index > 0 && nodeLengths->lengths == NULL));
    //if first time visiting this node then init nodeLengths then add len
    if (nodeLengths->lengths == NULL){
        fflush(stdout);
        nodeLengths->index = 0;
        nodeLengths->size = 32;
        nodeLengths->lengths = (unsigned*) mem_alloc((size_t) nodeLengths->size * sizeof(unsigned));
        mem_zero(nodeLengths->lengths, (size_t) nodeLengths->size * sizeof(unsigned));
        nodeLengths->lengths[nodeLengths->index] = len;
        (nodeLengths->index)++;
    }
    else {
        //add new length
        if (isNewLength(nodeLengths, len)){
            nodeLengths->lengths[nodeLengths->index] = len;
            (nodeLengths->index)++;
            //need resize
            if (nodeLengths->index == nodeLengths->size){
                nodeLengths->size *= 2;
//                printf("new size = %u\n", nodeLengths->size);
                nodeLengths->lengths = (unsigned*) mem_resize(nodeLengths->lengths, (size_t) nodeLengths->size * sizeof(unsigned));
                mem_zero(nodeLengths->lengths + nodeLengths->index, (size_t) (nodeLengths->size - nodeLengths->index) * sizeof(unsigned));
            }
        }
    }
}

void getLengthsHelper(DFA *M, pTransitionRelation p_transitionRelation, unsigned currentNode, P_NodeLengths * nodesLengths){
//    printf("%u, ", (currentNode < p_transitionRelation->sink)?currentNode : currentNode + 1);

    //if current state is accept state then register length before moving on with DFS
    if (findStateBS(p_transitionRelation->accepts, currentNode, 0, p_transitionRelation->acceptsSize - 1)){
        addLengthToNodeLengths(nodesLengths[currentNode], 0);
    }
    
    unsigned succNodeIndex;
    // if current node has out edges
    if (p_transitionRelation->degrees[currentNode] > 0){
        for (succNodeIndex = 0; succNodeIndex < p_transitionRelation->degrees[currentNode]; succNodeIndex++){
            unsigned succNode = p_transitionRelation->adjList[currentNode][succNodeIndex];
            //first time to see next node --> carry on DFS
            if (nodesLengths[succNode]->visited == false){
                nodesLengths[succNode]->visited = true;
                getLengthsHelper(M, p_transitionRelation, succNode, nodesLengths);
            }
            int i;
            assert(nodesLengths[succNode] != NULL);
            for (i = 0; i < nodesLengths[succNode]->index; i++ ){
                addLengthToNodeLengths(nodesLengths[currentNode], nodesLengths[succNode]->lengths[i] + 1);
            }
            //avoid overflow
            if(nodesLengths[succNode]->numOfPaths < (ULONG_MAX - nodesLengths[currentNode]->numOfPaths))
                nodesLengths[currentNode]->numOfPaths += nodesLengths[succNode]->numOfPaths;
            else
                nodesLengths[currentNode]->numOfPaths = ULONG_MAX;
        }
        if (nodesLengths[currentNode]->index > 0){
            nodesLengths[currentNode]->lengths = (unsigned*) mem_resize(nodesLengths[currentNode]->lengths, (size_t) nodesLengths[currentNode]->index * sizeof(unsigned));
            nodesLengths[currentNode]->size = nodesLengths[currentNode]->index;
        }
    }
    else
        nodesLengths[currentNode]->numOfPaths = 1;
}

/**
 Returns a set of integers representing all possible lengths of the
 strings that are elements of L(M).
 This only works if the graph does not have cycles in it.
 If this hits a cycle then it will not halt.
 Call isLengthFiniteTarjan first and make sure it returns 
 true before calling this
 */
P_DFAFiniteLengths dfaGetLengthsFiniteLang(DFA *M, int var, int *indices){
    P_DFAFiniteLengths pDFAFiniteLengths = (P_DFAFiniteLengths) mem_alloc(sizeof(DFAFiniteLengths));
    pDFAFiniteLengths->size = 0;
    pDFAFiniteLengths->lengths = NULL;
    if (check_emptiness(M, var, indices)){
        return pDFAFiniteLengths;
    }
    else if (checkOnlyEmptyString(M, var, indices)){
        pDFAFiniteLengths->size = 1;
        pDFAFiniteLengths->lengths = (unsigned*) mem_alloc((size_t) pDFAFiniteLengths->size * sizeof(unsigned));
        pDFAFiniteLengths->lengths[0] = 0;
        return pDFAFiniteLengths;
    }
    
    pTransitionRelation p_transitionRelation = dfaGetTransitionRelation(M);
//    dfaPrintTransitionRelation(p_transitionRelation);
    unsigned startState = (M->s < p_transitionRelation->sink)? M->s : M->s + 1;
    int i;
    P_NodeLengths * nodesLengths = (P_NodeLengths *) mem_alloc((size_t) p_transitionRelation->num_of_nodes * sizeof(P_NodeLengths));
    mem_zero(nodesLengths, (size_t)p_transitionRelation->num_of_nodes * sizeof(P_NodeLengths));
    

    for (i = 0; i < p_transitionRelation->num_of_nodes; i++){
        nodesLengths[i] = (P_NodeLengths) mem_alloc(sizeof(NodeLengths));
        nodesLengths[i]->size = 0;
        nodesLengths[i]->index = 0;
        nodesLengths[i]->lengths = NULL;
        nodesLengths[i]->visited = false;
        nodesLengths[i]->numOfPaths = 0;
    }

    getLengthsHelper(M, p_transitionRelation, startState, nodesLengths);

    
    pDFAFiniteLengths->size = nodesLengths[0]->size;
    pDFAFiniteLengths->lengths = nodesLengths[0]->lengths;
    
//    printf("\n\nnumber of paths for start state = %s\n", commaprint(nodesLengths[0]->numOfPaths));
    free(nodesLengths[0]);
    for (i = 1; i < p_transitionRelation->num_of_nodes; i++){
//        int j;
//        printf("lengths for node %u:", (i < p_transitionRelation->sink)? i : i + 1);
//        for (j = 0; j < nodesLengths[i]->index; j++){
//            printf("%u, ", nodesLengths[i]->lengths[j]);
//        }
//        printf("\n");
//        printf("for state %u number of paths = %s\n", (i < p_transitionRelation->sink)? i : i + 1, commaprint(nodesLengths[i]->numOfPaths));
        freeNodeLengths(nodesLengths[i]);
    }
    free(nodesLengths);
    dfaFreeTransitionRelation(p_transitionRelation);
    
    assert(pDFAFiniteLengths->size > 0);
    assert(pDFAFiniteLengths->lengths != NULL);
    
    return pDFAFiniteLengths;
}




