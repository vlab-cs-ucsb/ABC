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
 * Authors: Fang Yu
 */
 
/************************************************************

Backward Analysis

1. dfa_pre_concat(DFA* ML, DFA* MR, int pos, int var, int* indices)
2. dfa_pre_concat_const(DFA* ML, char* str, int pos, int var, int* indices)
3. dfa_pre_replace(DFA* M1, DFA* M2, char* str, int var, int* indices)

*************************************************************/

//for external.c
#include "mona/bdd_external.h"
#include "mona/mem.h"
//for bddDump
#include "mona/bdd_dump.h"
#include "stranger.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
//for arithmetic automata
#include <math.h>
#include "stranger_lib_internal.h"


//pos == 1, return the preimage of X for XL := X. XR
//pos == 2. return the preimage of X for XL := XR. X
 DFA* dfa_pre_concat(DFA* ML, DFA* MR, int pos, int var, int* indices){

  assert(pos==1 || pos ==2); //Computing pre-image for concatenation of two arguments
  DFA* Mtrans;
  DFA* M1;
  DFA* M2;
  DFA* result;
  DFA* Ma = dfaAllStringASCIIExceptReserveWords(var, indices);

  if(check_emptiness(MR, var, indices)) return dfaCopy(ML);

  if(pos==1){
    M1 = mdfaOneToManyTrackNoLambda(ML, 3, 0, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(M1);
    M2 = mdfaGPrefixM(MR, 0, 1, 2, 3, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(M2);
    Mtrans = dfa_intersect(M1,M2);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(Mtrans);
    dfaFree(M1);
    dfaFree(M2);
    result = dfaGetTrack(Mtrans, pos, 3, var, indices);
  }else{
    // Mtrans = mdfaMEqualLRR(ML, MR, Ma, 0, 1, 2, 3, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(ML);
    M1 = mdfaOneToManyTrackNoLambda(ML, 3, 0, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(M1);

    M2 = mdfaGSuffixM(MR, 0, 1, 2, 3, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(M2);
    Mtrans = dfa_intersect(M1,M2);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(Mtrans);
    dfaFree(M1);
    dfaFree(M2);
    result = dfaGetTrackNoPreLambda(Mtrans, pos, 3, var, indices);
  }


  dfaFree(Mtrans);
  dfaFree(Ma);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : pre_concat : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
  return dfaMinimize(result);
 }



//pos == 1, return the preimage of X for XL := X. XR
//pos == 2. return the preimage of X for XL := XR. X
DFA* dfa_pre_concat_const(DFA* ML, char* str, int pos, int var, int* indices){
  assert(1==pos || pos==2); //Computing pre-image for concatenation of two arguments
  DFA* Mtrans;
  DFA* result;
  DFA* suf;
  DFA* pre;
  DFA* Ma = dfaAllStringASCIIExceptReserveWords(var, indices);
  int n = (int)strlen(str);
  if(n==0) return dfaCopy(ML);
  if(pos==1){ //Precise Construction
	pre = dfa_intersect(ML, dfa_concat_extrabit(Ma, dfa_construct_string(str, var, indices), var, indices));
    Mtrans = mdfaMEqualLRc(pre, Ma, str, 0, 1, 2, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(Mtrans);
    result = dfaGetTrack(Mtrans, pos, 2, var, indices);
    if(_FANG_DFA_DEBUG) dfaPrintVerbose(result);
    dfaFree(pre);
	 //return dfa_pre_concat(ML, dfa_construct_string(str, var, indices), pos, var, indices);
  }else if(pos==2){ //Approximation: Using LRR construction
    suf = dfa_concat_extrabit(dfa_construct_string(str, var, indices), Ma, var, indices);
    Mtrans = dfa_intersect(ML, suf);
    result = dfa_Suffix(Mtrans, n, n, var, indices);
    dfaFree(suf);
  }else{
    printf("\n\nError on dfa_pre_concat_const: pos ==1 or pos ==2!\n\n");
    exit(0);
  }
  dfaFree(Ma);
  dfaFree(Mtrans);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : pre_const_concat : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
  return dfaMinimize(result);
 }

DFA* dfa_pre_replace(DFA* M1, DFA* M2, DFA* M3, int var, int* indices){

  return dfa_general_replace_extrabit(M1, M3, dfa_union(M2, M3), var, indices);
}

DFA* dfa_pre_replace_str(DFA* M1, DFA* M2, char *str, int var, int* indices){

  DFA *result=NULL;
  DFA *M3 = dfa_construct_string(str, var, indices);
  if((str ==NULL)||strlen(str)==0){
    //printf("Replacement [%s]!\n", str);
    result = dfa_insert_everywhere(M1, M2, var, indices);
  }else {
    //printf("Replacement [%s]!\n", str);
    result = dfa_general_replace_extrabit(M1, M3, dfa_union(M2, M3), var, indices);
  }
  dfaFree(M3);
  return result;
}

