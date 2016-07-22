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

/*****************************************

Vulnerability Signature for Multiple inputs

*****************************************/

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



//index starts from 0
//m = input tracks + output track (number of inputs + 1)
//track i is associated with input i. track m-1 is the output track
// for each input we call this function to initilize the input automaton where i_track is the input index (order) starting from 0
// For one dependency graph we need to be consistent with the track number (i_track) -- m, var , indicex are always the same for the same sink
// Only used for input for constants use mdfaSignatureConstant
DFA *mdfaSignatureInput(int i_track, int m, int var, int* indices){

 char *exeps;
 int len = m*var;
 char *str;

 int* mindices =allocateMultipleAscIIIndex(m, var);
 int i, j, n, shift;
 int nump = 1<<var;
 char *lambda = bintostr((unsigned long) (nump-1), var);

 dfaSetup(2,len,mindices);
 exeps=(char *)malloc((len+1)*sizeof(char));
 exeps[len]='\0';
 dfaAllocExceptions(nump-1);
 for(i=0; i<nump-1; i++){
   str = bintostr((unsigned long) i, var);
   for(n=0; n<m; n++){
     shift = n*var;
     if(n==i_track || n==(m-1))
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]=lambda[j];
     }
   }//end for
   assert(len == n*var);
   //exeps[len]='\0';
   dfaStoreException(0, exeps);
 }

 dfaStoreState(1);
 dfaAllocExceptions(0);
 dfaStoreState(1);
 free(exeps);
 return dfaMinimize(dfaBuild("+-"));
}



//Extend M to m track DFA where the m-1 th track is equal to M, and the rest is set to \lambda
// M represent the automaton for the constant which is a regular single track automaton
DFA *mdfaSignatureConstant( DFA* M, int m, int var, int* indices){
//m-track, the m-1_th track is accepted by L(M)

  DFA *result;
  trace_descr tp;
  paths state_paths, pp;
  int i, j, n, shift;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps, k, numOfAddedPaths;
  char *statuces;
  int nump = 1<<var;
  char* lambda = bintostr((unsigned long) (nump-1), var);
  int len = m*var;
  int* mindices =allocateMultipleAscIIIndex(m, var);

  max_exeps=1<<var; //remain the same as M
  sink=find_sink(M);
  assert(sink >-1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(M->ns, len, mindices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));

  //construct the added paths
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  //printf("\n\n INIT %d \n\n", M1->s);

  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	to_states[k]=pp->to;

	for(n=0; n<m; n++){
	  shift = n*var;
	  if(n==m-1){
	    for (j = 0; j < var; j++) {
	      //the following for loop can be avoided if the indices are in order
	      for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	      if (tp) {
		if (tp->value) exeps[k*(len+1)+shift+j]='1';
		else exeps[k*(len+1)+shift+j]='0';
	      }
	      else
		exeps[k*(len+1)+shift+j]='X';
	    }
	  }
	  else{
	    for(j=0; j<var; j++)
	      exeps[k*(len+1)+shift+j]=lambda[j];
	  }
	}//end for
	assert(len == n*var);
	exeps[k*(len+1)+len]='\0';
        k++;
      }
      pp = pp->next;
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);
    if(M->f[i]==-1)
      statuces[i]='-';
    else if(M->f[i]==1)
      statuces[i]='+';
    else
      statuces[i]='-';
    kill_paths(state_paths);
  }
  statuces[i]='\0';
  result = dfaBuild(statuces);
  free(exeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);

} //end SignatureConstant


