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
 * Authors: Fang Yu, Muath Alkhalaf, Abdulbaki Aydin, Lucas Bang
 */

#ifdef __cplusplus
extern "C" {
#endif
    
#ifndef __STRANGER_H
#define __STRANGER_H
    
#include "mona/mem.h"
#include "assert.h"
    //for external.c
#include "mona/bdd_external.h"
    //for bddDump
#include "mona/bdd_dump.h"
#include "mona/dfa.h"
#include <stdbool.h>
    
    
    //PRINT DFA
#define _FANG_DFA_DEBUG 0

#define DEBUG_SIZE_INFO 0
    /*===================================================================*/
    /* 8 bits for ASCII and 1 bit reserved for replacement
     */
    
#define NUMBEROFVARIABLES 10
#define NUM_ASCII_TRACKS 8
#if NUM_ASCII_TRACKS == 8
    typedef unsigned char t_st_word;
#elif NUM_ASCII_TRACKS == 16
    typedef unsigned short t_st_word;
#else
    typedef unsigned t_st_word;
#endif
    /*===================================================================*/
    /* Mask option value
     */
#define	MASK_CONSTRUCT		1
#define	MASK_UNION		2
#define	MASK_INTERSECT		4
#define	MASK_NEGATE		8
#define MASK_CONCAT		16
#define MASK_REPLACE		32
#define MASK_EMPTYCHECK		64
#define MASK_INTERCHECK		128
#define MASK_EQUALCHECK		256
#define MASK_INCLUDECHECK	512
#define MASK_TEST		1024
    
    
    /*=====================================================================*/
    /* Data structure for tracing DFA
     */
    
    struct int_type{
        int value;
        struct int_type	*next;
    };
    
    struct int_list_type{
        int count;
        struct	int_type	*head;
        struct	int_type	*tail;
    };
    
    
    /*=====================================================================*/
    /* Data structure for semilinearset
     */
    
    struct semilinear_type {
        int R;
        int C;
        int* r;
        int *c;
        int nc;
        int nr;
        
    };
    
    
    struct binary_state_type{
        int t;
        int v;
        int b;
        int d1;
        int d0;
        
        
    };
    
    /*=====================================================================*/
    /* Data structure for constructing an automaton from another one
     */
    
    typedef struct  {
        int source;
        int dest;
        unsigned char first;
        unsigned char last;
    } transition;
    
    /*=====================================================================*/
    /* Data structure for constructing automaton transition relation
     */
    
    /**
     adjacency list is used here since graph is sparce
     **/
    typedef struct transitionRelation_{
        unsigned **adjList;
        t_st_word *degrees;
        unsigned num_of_nodes;
        unsigned num_of_edges;
        bool reverse;
        bool selfCycles;
        unsigned sink;
        unsigned start;
        unsigned *accepts;
        unsigned acceptsSize;
    } transitionRelation, *pTransitionRelation;
    
    pTransitionRelation dfaGetTransitionRelation(DFA *M);
    pTransitionRelation dfaGetReverseTransitionRelation(DFA *M);
    pTransitionRelation dfaReverseTransitionRelation(pTransitionRelation p_transitionRelation);
    pTransitionRelation get_reverse_transition_relation_helper(DFA *M, pTransitionRelation p_transitionRelation);
    bool dfaIsNextState(pTransitionRelation p_transitionRelation, unsigned currentState, unsigned nextState);
    bool dfaIsPrevState(pTransitionRelation p_transitionRelation, unsigned currentState, unsigned prevState);
    void dfaFreeTransitionRelation(pTransitionRelation p_transitionRelation);
    unsigned dfaGetDegree(DFA *M, unsigned state);
    unsigned dfaGetMaxDegree(DFA *M, unsigned *p_maxState);
    void dfaShiftTransitionRelation(pTransitionRelation p_transitionRelation, int sink);
    void dfaPrintTransitionRelation(pTransitionRelation p_transitionRelation);
    void dfaPrintTransitionRelationNoShift(pTransitionRelation p_transitionRelation);


    /*=====================================================================*/
    /* Function Helpers
     */
    typedef enum {ENT_COMPAT, ENT_QUOTES, ENT_NOQUOTES} hscflags_t;


    //*====================================================================
    /* Construct functions
     */
    
    int* allocateAscIIIndexWithExtraBit(int length);
    
    // A DFA that accepts nothing (empty language or phi)
    DFA *dfaASCIINonString(int var, int *indices);
    
    // A DFA that accepts all strings except 11111111 and 111111110
    // used when needed language is Sigma*
    DFA *dfaAllStringASCIIExceptReserveWords(int var, int *indices);
    
    // A DFA that accepts only empty string (epsilon)
    DFA *dfaASCIIOnlyNullString(int var, int *indices);
    
    /**
     * outputs a DFA M that accepts string value of *reg
     * outputs DFA M where L(M) = {*reg}
     */
    DFA *dfa_construct_string(char *reg, int var, int *indices);
    
    /*
     * outputs a DFA M that accepts the set of string values in array set
     * outputs DFA M where L(M) = {s: s elementOf set}
     */
    DFA* dfa_construct_set_of_strings(char** set, int size, int var, int* indices);
    
    
    DFA *dfa_construct_string_closure(char *reg, int var, int *indices);
    
    //Construct DFA accepts one character within [a-b]
    
    DFA *dfa_construct_range(char a, char b, int var, int *indices);
    

    /**
     Constructs and automaton that accepts any string s where |s| is in the
     set "lengths".
     Lengths must be a set of integers with at least one element.
     If the set is sorted incrementally (from smallest to largest)  then set "sorted" to true to avoid internal sorting
     */
    DFA *dfaSigmaLengthsSet(unsigned *lengths, const unsigned size, bool sorted, int var, int *indices);
    
    
    /**
     Given a set of finite lengths fl, returns an automaton M` where for all w element_of L(M)
     if |w| is in fl then w is element_of L(M`)
     If the list fl is sorted incrementally (from smallest to largest) set ordered to true.
     */
    DFA *dfaRestrictByFiniteLengths(DFA *M, unsigned *lengths, const unsigned size, bool sorted, int var, int *indices);
    //Construct DFA From another automaton
    // n_state is the number of states
    // accept_states is a string where if the char at position i is + then state i is accepting, if it is - it is not accepting
    // n_trans is the number of transitions in the transitions array
    // Each transition in the transition array has a source state, destination state and a range of characters (the range is between firt and last)
    // The transition array must be sorted based on the source state
    // We create an extra sink state which is the state labeled n_states (so the constructed automaton has n_states+1 states)
    DFA *dfa_construct_from_automaton(int n_states,  int n_trans, transition* transitions, char* accept_states, int var, int *indices);
    
    // not needed anymore. better use the below dfa_union_with_emptycheck
    DFA *dfa_union(DFA *M1, DFA *M2);
    
    /*
     * checks if one of the two is empty string to call
     * union_with_empty other wise it just does the union
     * regardless.
     */
    DFA *dfa_union_with_emptycheck(DFA* M1, DFA* M2, int var, int* indices);
    
    //Given M, output a dfa accepting L(M) u \{\empty\}
    // not needed anymore. better use the above dfa_union_with_emptycheck
    DFA *dfa_union_add_empty_M(DFA *M, int var, int *indices);
    
    DFA *dfa_intersect(DFA *M1, DFA *M2);
    
    DFA *dfa_negate(DFA *M1, int var, int *indices);
    
    DFA *dfa_concat(DFA *M1, DFA *M2, int var, int *indices);
    
    // DO NOT USE THIS CONCAT. INSTEAD use dfa_concat. That one considers the empty string first then calls this one
    DFA *dfa_concat_extrabit(DFA *M1, DFA *M2, int var, int *indices);
    
    DFA *dfa_shift_empty_M(DFA *M, int var, int *indices);

    //M1: subject automaton that replace will occur on
    //M2: search automaton representing the pattern that we will match against
    //str: the replace string
    // replace ALL strings that match L(M2) in L(M1) with string str
    DFA *dfa_replace_extrabit(DFA *M1, DFA *M2, char *str, int var, int *indices);
    
    /**
     * General replace
     * M1: subject automaton that replace will occur on
     * M2: search automaton representing the pattern that we will match against
     * M3: the replace language
     * replace ALL strings that match L(M2) in L(M1) with L(M3)
     */
    DFA *dfa_general_replace_extrabit(DFA* M1, DFA* M2, DFA* M3, int var, int* indices);

    DFA *dfa_replace_step3_general_replace(DFA *M, DFA* Mr, int var, int *indices);

    DFA *dfa_closure_extrabit(DFA *M1,int var,int *indices); // added by Muath to be used by java StrangerLibrary
    
    DFA *dfaWiden(DFA *a, DFA *d); // added by Muath to be used by java StrangerLibrary
    
    DFA* dfa_pre_concat_const(DFA* ML, char* str, int pos, int var, int* indices);
    DFA* dfa_pre_concat(DFA* ML, DFA* MR, int pos, int var, int* indices);
    DFA* dfa_pre_replace_str(DFA* M1, DFA* M2, char *str, int var, int* indices);
    
    //Given M, output a DFA accepting S*.w.S* where w \in M
    DFA *dfa_star_M_star(DFA *M, int var, int *indices);
    
    // A DFA that accepts only one arbitrary character
    DFA *dfaDot(int var, int *indices);
    
    // A DFA that accepts only emty or one arbitrary character
    DFA *dfaQuestionMark(int var, int *indices);
    
    // A DFA that accepts everything within the length from c1 to c2
    //c2 = -1, indicates unbounded upperbound
    //c1 = -1, indicates unbounded lowerbound
    DFA *dfaSigmaC1toC2(int c1, int c2, int var, int* indices);
    
    //Output M' so that L(M')={w| w'\in \Sigma*, ww' \in L(M), c_1 <= |w|<=c_2 }
    DFA *dfa_Prefix(DFA *M, int c1, int c2, int var, int* indices);
    
    DFA *dfa_Suffix(DFA *M, int c1, int c2, int var, int *indices);
    
    //Checking function
    /**
     if automaton is guaranteed to be minimized then this check
     is very quick
     */
    bool check_emptiness_minimized(DFA *M);
    
    int check_emptiness(DFA *M1, int var, int *indices);
    
    int check_equivalence(DFA *M1, DFA *M2, int var, int *indices);
    
    int check_intersection(DFA *M1,DFA *M2,int var,int *indices);// added by Muath to be used by java StrangerLibrary
    
    /*
     * returns true if M2 includes M1 i.e.
     * L(M1) subset_of L(M2)
     */
    int check_inclusion(DFA *M1,DFA *M2,int var,int *indices);// added by Muath to be used by java StrangerLibrary
    
    /**
     if L(M) is a singleton set, it will return the string element
     in this set otherwise it will return NULL.
     NULL means not singleton (either empty language or accepts more
     than one string
     */
    char *isSingleton(DFA *M, int var, int *indices);
    
    int checkMembership(DFA* M, char* string, int var, int* indices);
    
    /**
     * A string automaton that accepts anything between start and end
     * start = -1 , no lower bound
     * end = -1, no upper bound
     * start = end = -1, non accepting automaton
     * Baki
     */
    DFA *dfaStringAutomatonL1toL2(int start, int end, int var, int* indices);
    /**
     * returns true (1) if {|w| < n: w elementOf L(M) && n elementOf Integers}
     * In other words length of all strings in the language is bounded by a value n
     */
    int isLengthFinite(DFA* M, int var, int* indices);
    int isLengthFiniteDFS(DFA* M, int var, int *indices);
    bool isLengthFiniteTarjan(DFA *M, int var, int *indices);
    
    typedef struct _DFAFiniteLengths {
        unsigned *lengths;
        unsigned size;
    } DFAFiniteLengths, *P_DFAFiniteLengths;
    /**
     returns a list of all length of strings of the language along with the list size.
     must call isLengthFiniteTarjan and make sure it returns true
     otherwise this method will not terminate.
     */
    P_DFAFiniteLengths dfaGetLengthsFiniteLang(DFA *M, int var, int *indices);
    /*
     * checks if dfa accepts empty string
     */
    int checkEmptyString(DFA *M);
    
    /*
     * check if dfa accepts only empty string
     */
    int checkOnlyEmptyString(DFA *M, int var, int* indices);

    // generating an example i.e. an element of L(M)
    // Could return null in case solution is empty string or there
    // is no solution
    char *dfaGenerateExample(DFA* M, int var, unsigned indices[]);
    
    DFA *dfaRemoveSpace(DFA* M, int var, int* indices);
    
    int dfaPrintBDD(DFA *a, char *filename, int var);
    void dfaPrintGraphvizAsciiRange(DFA *a, int no_free_vars, int *offsets, int printSink);
    void dfaPrintGraphvizAsciiRangeFile(DFA *a, const char *filename, int no_free_vars, int *offsets, int printSink);
    void dfaPrintGraphvizFile(DFA *a, const char *filename, int no_free_vars, unsigned *offsets);
    void dfaExportBddTable(DFA *a, char *file_name, int var);
    DFA *dfaImportBddTable(char* file_name, int var) ;

    void __export(bdd_manager *bddm, unsigned p, Table *table);

    // Outputs M` that represents the length of automaton M
    //Output M, so that L(M)={|w|| w \in L(M1)}
    //Need to use extra bit to model NFA to DFA
    //NOTE: Add 1 to all symbols
    // 1. Duplicate paths (0->k, k is not sink) with extra bit set to 1 for each symbol.
    // 2. Project all bits except extra bit away
    DFA *dfa_string_to_unaryDFA(DFA* M, int var, int *indices);
    
    DFA *dfa_restrict_by_unaryDFA(DFA *M, DFA* uL, int var, int *indices);
    
    // Given an automaton M1, where M represents length of M1 this will return
    // a finite number of pairs (q, p) each representing (an infinite/finite) number of
    // possible lengths for L(M1) in the format p+q*i for all integers i
    // If q is always 0 it means that there is a finite number of possible lengths
    // Example1: given an automaton M1 we get {(2,0), (3, 0)} ==> length of all words
    // in L(M1) is divisable by either 2 or 3 (2*i+0, 3*i+0 for all integers i)
    // Example2: given an automaton M2 we get {(0,3), (0,5), (0,10)} ==> length of all words
    // in L(M1) is either 3, 5 or 10 (2*i+0, 3*i+0 for all integers i)
    // Notice that if q is always 0 for an automaton M, L(M) is finite
    // To get semilinear set for an auto M1 first get M = dfa_string_to_unaryDFA(M1) and then
    // pass the result M here
    struct semilinear_type* getSemilinerSetCoefficients(DFA *M);
    DFA* dfa_semiliner_to_binaryDFA(struct semilinear_type *S);
    
    void print_semilinear_coefficients(struct semilinear_type* S);
    
    DFA* dfaMysqlEscapeString(DFA* inputAuto, int var, int* indices);

    DFA* dfaPreMysqlEscapeString(DFA* inputAuto, int var, int* indices);

    DFA* dfaAddSlashes(DFA* inputAuto, int var, int* indices);
    
    DFA* dfaPreAddSlashes(DFA* inputAuto, int var, int* indices);
    
    DFA* dfaPreToUpperCase(DFA* M, int var, int* indices);
    
    DFA* dfaPreToLowerCase(DFA* M, int var, int* indices);
    
    DFA* dfaToUpperCase(DFA* M, int var, int* indices);
    
    DFA* dfaToLowerCase(DFA* M, int var, int* indices);
    
    DFA *dfaLeftTrim(DFA *M, char c, int var, int *oldindices);
    
    DFA *dfaRightTrim(DFA *M, char c, int var, int *oldindices);
    
    DFA *dfaPreLeftTrim(DFA *M, char c, int var, int *oldIndices);
    
    DFA *dfaPreRightTrim(DFA *M, char c, int var, int *oldIndices);
    
    DFA* dfaTrim(DFA* inputAuto, char c, int var, int* indices);
    
    /**
     * trims a list of characters stored in array chars[].
     * num is the size of array chars
     */
    DFA* dfaTrimSet(DFA* inputAuto, char chars[], int num, int var, int* indices);
    
    DFA* dfaPreTrim(DFA* inputAuto, char c, int var, int* indices);
    
    /**
     * pretrims a list of characters stored in array chars[].
     * num is the size of array chars
     */
    DFA* dfaPreTrimSet(DFA* inputAuto, char chars[], int num, int var, int* indices);
    
    DFA *dfa_escape(DFA *M, int var, int *oldindices, char escapeChar, char *escapedChars, unsigned numOfEscapedChars);
    DFA *dfa_pre_escape(DFA *M, int var, int *indices, char escapeChar, char *escapedChars, unsigned numOfEscapedChars);
    DFA *dfa_replace_char_with_string(DFA *M, int var, int *oldIndices, char replacedChar, char *string);
    DFA *dfa_pre_replace_char_with_string(DFA *M, int var, int *oldIndices, char replacedChar, char *string);
    DFA *dfaHtmlSpecialChars(DFA *inputAuto, int var, int *indices, hscflags_t flags);
    DFA *dfaPreHtmlSpecialChars(DFA *inputAuto, int var, int *indices, hscflags_t flags);
    
    //Utility function
    int getVar();
    int* getIndices();
    void setPreciseWiden();
    void setCoarseWiden();
    void flush_output();
    DFA *test_project(DFA *M, int var, int *oldindices, int len, int fast);
    
    
    int main_test (int argc, const char *argv[]);
    
    // BAKI DEBUG
    struct int_list_type *reachable_closure(DFA *M, int start, int var, int *indices);

#endif
    
#ifdef __cplusplus
}
#endif
