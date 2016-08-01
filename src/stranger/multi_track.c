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

/**********************************************************

MULTI-TRACK STRING AUTOMATA

1. DFA *dfaLambdaPlus(var, indices)
2. DFA *dfaAppendLambda(DFA* M, var, indices)
3. DFA *mdfaOneToManyTrack( DFA* M_i, m, i, var, indices) //m-track, the i_th track is accepted by L(M_i).\lambda+
3.1 DFA *mdfaOneToManyPlusTrack( DFA* M_i, m, k, var, indices) //m+k track
4. DFA *mdfaMEqualLR(DFA *M_1, DFA *M_2, i, j, m, var, indices) //return x_i = x_j, x_i \in L(M_1), x_j \in L(M_2)
4.1 DFA *mdfaMEqual(i, j, m, var, indices) //return x_i = x_j
5. DFA *mdfaMEqualLRc(DFA *M_1, DFA *M_2, DFA *M_3, i, j, m, var, indices) //return x_i = x_jc
6. DFA *mdfaMEqualLRR(DFA *M_1, DFA *M_2, DFA *M_3, i, j, k, m, var, indices) //return x_k = x_ix_j
7. DFA *mdfaMExistQuantification(DFA *M, m, var, indices) //project away n+1_th track (used for x_k) \exists x_k. M
8. DFA *dfaGetkTrack(DFA *M, m, k, var, indices) //project away all tracks except k
***************************************************************/


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




//add one extra bit (for dfa_xxx_extrabit)
int* allocateMultipleAscIIIndex(int m, int length){
  int i;
  int* indices;
  indices = (int *) malloc((length*m+2)*sizeof(int));
  indices[length*m+1]='\0';
  for(i=0; i<=m*length; i++)
    indices[i]=i;
  return indices;
}

// M is the multitrack dfa (result of intersection with attack pattern) and m is number of tracks, var and indices are the original var and indices
DFA *dfaRemoveLastTrack(DFA *M, int m, int var, int* indices){
  DFA *result = dfaCopy(M);
  DFA *temp;
  int i, j;
  int flag =0;
  i=m-1;
  for (j=var-1; j>=0; j--){
    //dfaPrintVerbose(result);
    temp = dfaProject(result, i*var+j);
    //printf("\n Get track %d: project away the track %d\n", i_track, i);
    dfaFree(result);
    result=dfaMinimize(temp);
  }
  return result;
}


char *getLambda(int var){
  return getSharp1(var); //11111111
}

DFA *dfaLambdaStar(int var, int* indices){

  char *lambda;
  lambda = getLambda(var);
  dfaSetup(3,var,indices);
  dfaAllocExceptions(1);
  dfaStoreException(1, lambda);
  dfaStoreState(2);
  dfaAllocExceptions(1);
  dfaStoreException(1, lambda);
  dfaStoreState(2);
  dfaAllocExceptions(0);
  dfaStoreState(2);

  return dfaBuild("++-");
}


// A DFA that accepts all strings except lambda
DFA *dfaNoLambda(int var, int *indices){

  dfaSetup(2,var,indices);
  dfaAllocExceptions(1);
  dfaStoreException(1, getLambda(var));
  dfaStoreState(0);
  dfaAllocExceptions(0);
  dfaStoreState(1);
  return dfaBuild("+-");
}


DFA *dfaAppendLambda(DFA* M, int var, int* indices){
  return dfa_concat_extrabit(M, dfaLambdaStar(var, indices), var, indices);
}

//This will return enpty instead of catching prefix.
DFA *dfaRemoveLambdaSet(DFA* M, int var, int* indices){
  return dfa_intersect(M, dfaNoLambda(var, indices));
}

//set less significant bit less priority, and sequential ordered
int* allocateMutipleAscIIIndex(int m, int length){
  int i;
  int* indices;
  indices = (int *) malloc(length*m*sizeof(int));
  for(i=0; i<m*length; i++)
    indices[i]=i;
  return indices;
}

//set less significant bit less priority, and sequential ordered
int* allocateIFirstMutipleAscIIIndex(int m, int i_track, int length){
  int i;
  int* indices;
  indices = (int *) malloc(length*m*sizeof(int));
  assert(i_track<m);
  for(i=0; i<m*length; i++)
    indices[i]=i;
  for(i=0; i<length; i++){
    indices[i]=indices[i_track*length+i];
    indices[i_track*length+i] = i;
  }
  return indices;
}


//m is number of tracks
// i_track indicate the i_th track
//Construct m-track automaton M^m from one track automaton M.
// (*,..., a, ...*)...(*,...,\lambda, ...*)*\in L(M^m) iff a... \in L(M)
DFA *mdfaOneToManyTrack( DFA* M1, int m, int i_track, int var, int* indices){ //m-track, the i_th track is accepted by L(M_i).\lambda+

  DFA *result;
  trace_descr tp;
  paths state_paths, pp;
  int i, j, n, shift;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps, k;
  char *statuces;
  int len = m*var;
  int* mindices =allocateMutipleAscIIIndex(m, var);
  DFA* M = dfaAppendLambda(M1, var, indices);

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
	  if(n==i_track){
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
	      exeps[k*(len+1)+shift+j]='X';
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
      statuces[i]='0';
    kill_paths(state_paths);
  }
  statuces[i]='\0';
  result = dfaBuild(statuces);
  dfaFree(M);
  free(exeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);

} //end one to many

// we here extend the single track automaton M into multitrack one where m is the number of tracks and i_track is the track the has the original value of M
// for attack pattern we use i_track = m-1 to intersect the output track with the attack pattern
// var and indices are the original ones for the single track automaton
DFA *mdfaOneToManyTrackNoLambda( DFA* M, int m, int i_track, int var, int* indices){ //m-track, the i_th track is accepted by L(M_i).\lambda+

  DFA *result;
  trace_descr tp;
  paths state_paths, pp;
  int i, j, n, shift;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps, k;
  char *statuces;
  int len = m*var;
  int* mindices =allocateMutipleAscIIIndex(m, var);

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
	  if(n==i_track){
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
	      exeps[k*(len+1)+shift+j]='X';
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
      statuces[i]='0';
    kill_paths(state_paths);
  }
  statuces[i]='\0';
  result = dfaBuild(statuces);
  free(exeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);

} //end one to many no lambda


DFA *mdfaMDuplicate(DFA* M, int i_track, int j_track, int m, int var, int* indices){

  DFA *result;
  DFA *tmpM;
  trace_descr tp;
  paths state_paths, pp;
  int i, j, n, shift;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps, k;
  char *statuces;
  int len = m*var;
  int* mindices = allocateMutipleAscIIIndex(m, var);

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
	  if(n==i_track){
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
	  }else if(n==j_track){
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
	      exeps[k*(len+1)+shift+j]='X';
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
    else
      statuces[i]='0';
    kill_paths(state_paths);
  }
  statuces[i]='\0';
  tmpM = dfaMinimize(dfaBuild(statuces));
  result = dfaAppendLambda(tmpM, len, mindices);
  dfaFree(tmpM);
  free(exeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);

} //end mdfaMEqual





DFA *mdfaMDuplicateLR(DFA *M1, DFA *M2, int i_track, int j_track, int m, int var, int* indices){
  //DFA* M = dfa_intersect(M1, M2);
  return mdfaMDuplicate(dfa_intersect(M1,M2), i_track, j_track, m, var, indices);
}


//track i is equal to track j
DFA *mdfaGEqual(int i_track, int j_track, int m, int var, int* indices){

 char *exeps;
 int len = m*var;
 char *str;
 int* mindices =allocateMutipleAscIIIndex(m, var);
 int i, j, n, shift;
 int nump = 1<<var;
 dfaSetup(3,len,mindices);
 exeps=(char *)malloc((len+1)*sizeof(char));
 exeps[len]='\0';
 dfaAllocExceptions(nump);
 for(i=0; i<nump-1; i++){
   str = bintostr((unsigned long) i, var);
   for(n=0; n<m; n++){
     shift = n*var;
     if(n==i_track || n==j_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]='X';
     }
   }//end for
   assert(len == n*var);
   //exeps[len]='\0';
   dfaStoreException(0, exeps);
 }
 assert(i==nump-1); //Add lambda
 str = bintostr((unsigned long) i, var);
 for(n=0; n<m; n++){
   shift = n*var;
   if(n==i_track || n==j_track)
     for (j = 0; j < var; j++)
       exeps[shift+j]=str[j];
   else{
     for(j=0; j<var; j++)
       exeps[shift+j]='X';
   }
 }//end for
 assert(len == n*var);
 //exeps[len]='\0';
 dfaStoreException(1, exeps);
 dfaStoreState(2);
 dfaAllocExceptions(1);
 dfaStoreException(1, exeps);
 dfaStoreState(2);
 dfaAllocExceptions(0);
 dfaStoreState(2);
 free(exeps);
 return dfaMinimize(dfaBuild("++-"));
}


//track j is the prefix of track i
DFA* mdfaGPrefix(int i_track, int j_track, int m, int var, int* indices){

 char *exeps;
 int len = m*var;
 char *str;
 char *lambda;
 int* mindices =allocateMutipleAscIIIndex(m, var);
 int i, j, n, shift;
 int nump = 1<<var; //add (***lambda***)
 dfaSetup(3,len,mindices);
 exeps=(char *)malloc((len+1)*sizeof(char));
 exeps[len]='\0';
 dfaAllocExceptions(2*nump-1);
 for(i=0; i<nump-1; i++){
   str = bintostr((unsigned long) i, var);
   for(n=0; n<m; n++){
     shift = n*var;
     if(n==i_track || n==j_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]='X';
     }
   }//end for
   assert(len == n*var);
   //exeps[len]='\0';
   dfaStoreException(0, exeps);
 }
 assert(i==nump-1);
 lambda = bintostr((unsigned long) i, var);

 // Add \Sigma\{lambda}, lambda;
 for(i=0; i<nump-1; i++){
   str = bintostr((unsigned long) i, var);
   for(n=0; n<m; n++){
     shift = n*var;
     if(n==i_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else if(n==j_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=lambda[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]='X';
     }
   }//end for
   assert(len == n*var);
   //exeps[len]='\0';
   dfaStoreException(0, exeps);
 }

 // Add lambda, lambda
 for(n=0; n<m; n++){
   shift = n*var;
   if(n==i_track || n==j_track)
     for (j = 0; j < var; j++)
       exeps[shift+j]=lambda[j];
   else{
     for(j=0; j<var; j++)
       exeps[shift+j]='X';
   }
 }//end for
 assert(len == n*var);
 //exeps[len]='\0';
 dfaStoreException(1, exeps);
 dfaStoreState(2);
 dfaAllocExceptions(1);
 dfaStoreException(1, exeps);
 dfaStoreState(2);
 dfaAllocExceptions(0);
 dfaStoreState(2);
 free(exeps);
 free(lambda);
 return dfaMinimize(dfaBuild("++-"));
} //End Prefix


//track j is the prefix of track i and  the rest is equal to str
//
// delta(0, ww) =0
// delta(0,tail[0]) =1 ,...delta(n-1, tail[n-1])=n;
// delta(n, \lambda\lambda) = n
// else go to n+1
// status:---------+-
// n = strlen(tail)

DFA* mdfaGPrefixConst(int i_track, int j_track, char* tail, int m, int var, int* indices){

 char *exeps;
 int len = m*var;
 char *str;
 char *lambda;
 int* mindices =allocateMutipleAscIIIndex(m, var);
 int i, j, n, shift, k;
 int nump = 1<<var; //add (***lambda***)
 int strlength = strlen(tail);
 int ns = 2+ strlength;
 char *statuces;

 //no tail: retun general prefix
 if(strlength==0) return mdfaGPrefix(i_track, j_track, m, var, indices);

 statuces=(char *)malloc((ns+1)*sizeof(char));
 dfaSetup(ns,len,mindices);
 exeps=(char *)malloc((len+1)*sizeof(char));
 exeps[len]='\0';
 dfaAllocExceptions(nump);
 for(i=0; i<nump-1; i++){
   str = bintostr((unsigned long) i, var);
   for(n=0; n<m; n++){
     shift = n*var;
     if(n==i_track || n==j_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]='X';
     }
   }//end for
   assert(len == n*var);
   //exeps[len]='\0';
   dfaStoreException(0, exeps);
 }
 assert(i==nump-1);

 lambda = bintostr((unsigned long) i, var);
 //lambda = getLambda(var);  (Assume 111111111),
 //FANG WARNING: changing lambda may raise errors

 str = bintostr((unsigned long) tail[0], var); // the binary encoding of th ekth character

 for(n=0; n<m; n++){
   shift = n*var;
     if(n==i_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else if(n==j_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=lambda[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]='X';
     }
 }//end for
 assert(len == n*var);
 //exeps[len]='\0';
 dfaStoreException(1, exeps);
 dfaStoreState(strlength+1);

 for(k=1; k<strlength; k++){
   str = bintostr((unsigned long) tail[k], var);
   for(n=0; n<m; n++){
     shift = n*var;
     if(n==i_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=str[j];
     else if(n==j_track)
       for (j = 0; j < var; j++)
	 exeps[shift+j]=lambda[j];
     else{
       for(j=0; j<var; j++)
	 exeps[shift+j]='X';
     }
   }//end for
   assert(len == n*var);
   dfaAllocExceptions(1);
   dfaStoreException(k+1, exeps);
   dfaStoreState(strlength+1);
 }

 dfaAllocExceptions(1);
// Add lambda, lambda
 for(n=0; n<m; n++){
   shift = n*var;
   if(n==i_track || n==j_track)
     for (j = 0; j < var; j++)
       exeps[shift+j]=lambda[j];
   else{
     for(j=0; j<var; j++)
       exeps[shift+j]='X';
   }
 }//end for
 assert(len == n*var);
 //exeps[len]='\0';
 dfaStoreException(strlength, exeps);
 dfaStoreState(strlength+1);

 dfaAllocExceptions(0);
 dfaStoreState(strlength+1);
 free(exeps);
 free(lambda);

 for(i =0; i<ns; i++){
   if(i==strlength) statuces[i] = '+';
   else statuces[i] = '-';
 }
 statuces[i]='\0';
 assert(i==ns);
 return dfaMinimize(dfaBuild(statuces));
} //End PrefixConst


//XXR is equal to mdfaGPrefixM + lambda tail

//track j is the prefix of track i and  the rest (track k) is accepted by M
// i: aaaaaaa
// j: aaallll
// k: lllaaaa
//
// delta(0, (w,w,\lambda)) =0
// delta(i,(a,\lambda,a)) =delta_M(i,a)
// status:M->F

DFA* mdfaGPrefixM(DFA* M, int i_track, int j_track, int k_track, int m, int var, int* indices){

  //for new numpath
  char *numexeps;
  int len = m*var;
  char *str;

  int* mindices =allocateMutipleAscIIIndex(m, var);
  int i, j, n, shift, k, tmp, ni;
  int nump = 1<<var; //add (***lambda***)

 //char* lambda = getLambda(var);  (Assume 111111111),
 //FANG WARNING: changing lambda may raise errors
  char *lambda = bintostr((unsigned long) nump-1, var);

  int ns = M->ns;
  int sink = find_sink(M);
  int iniflag = check_init_reachable(M, var, indices);



  //for original transitions
  DFA *result;
  trace_descr tp;
  paths state_paths, pp;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;

  assert(iniflag==0 || iniflag==1);

  //init is reachable, need to distinguish initial state
  ns = ns+iniflag; //add a new initial state if needed


  max_exeps=1<<var; //remain the same as M
  assert(sink >-1); //assume there is a sink state in M

  dfaSetup(ns, len, mindices);

  //used to traverse M
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));


  //traverse M
  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	to_states[k]=pp->to + iniflag; //shift one state if init is reachable

	for(n=0; n<m; n++){
	  shift = n*var;
	  if(n==i_track||n==k_track){
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
	  else if (n==j_track){ //Put Lambda
	    for(j=0; j<var; j++)
	      exeps[k*(len+1)+shift+j]=lambda[j];
	  }
	  else{ //Put don't care
	    for(j=0; j<var; j++)
	      exeps[k*(len+1)+shift+j]='X';
	  }
	}//end for
	assert(len == n*var);
	exeps[k*(len+1)+len]='\0';
        k++;
      }
      pp = pp->next;
    }//end while

    if(i==0){
      //build a new initial state by adding num paths
      numexeps=(char *)malloc((len+1)*sizeof(char));
      numexeps[len]='\0';
      dfaAllocExceptions(nump-1+k); //nump-1 + k

      //add (n, n, lambda)
      for(ni=0; ni<nump-1; ni++){
	str = bintostr((unsigned long) ni, var);
	for(n=0; n<m; n++){
	  shift = n*var;
	  if(n==i_track || n==j_track)
	    for (j = 0; j < var; j++)
	      numexeps[shift+j]=str[j];
	  else if (n==k_track){ //Put Lambda
	    for(j=0; j<var; j++)
	      numexeps[shift+j]=lambda[j];
	  }else{
	    for(j=0; j<var; j++)
	      numexeps[shift+j]='X';
	  }
	}//end for
	assert(len == n*var);
	//exeps[len]='\0';
	dfaStoreException(0, numexeps);
      }
      //add k (a, lambda, a)
      tmp = k; //tmp is used to duplicate the original initial state if needed
      for(k--;k>=0;k--)
	dfaStoreException(to_states[k],exeps+k*(len+1));
      dfaStoreState(sink);
      statuces[0]=(M->f[M->s]==1)?'+':'-';

      if(iniflag){ //duplicate the original initial state
	k = tmp;
	dfaAllocExceptions(k);
	for(k--;k>=0;k--)
	  dfaStoreException(to_states[k],exeps+k*(len+1));
	dfaStoreState(sink);
	statuces[0+iniflag]=statuces[0];
      }
    }
    else{ //build the rest states (after state 0,and state 1 if iniflag==1 )
      dfaAllocExceptions(k);
      for(k--;k>=0;k--)
	dfaStoreException(to_states[k],exeps+k*(len+1));
      dfaStoreState(sink);
      statuces[i+iniflag]=(M->f[i]==1)?'+':'-';
    }

    kill_paths(state_paths);
  }//end for traverse M

  assert(i+iniflag == ns);

  statuces[i+iniflag]='\0';
  result = dfaBuild(statuces);
  free(exeps);
  free(numexeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);


}// end dfaGPrefixM



//XRX is equal to mdfaGSuffixM + lambda tail
//track k is the suffix of track i and the prefix (track j) is accepted by M
// i: aaaaaaaa
// j: aaaallll
// k: llllaaaa
//
// add a new state n
// forall accepting state f, delta(f, (w,\lambda, w)) = n
// delta(n, (w,\lambda,w)) = n
// delta(i,(a,a,\lambda)) =delta_M(i,a)
// status:M->F and n

DFA* mdfaGSuffixM(DFA* M, int i_track, int j_track, int k_track, int m, int var, int* indices){

  //for new numpath
  char *numexeps;
  int len = m*var;
  char *str;

  int* mindices =allocateMutipleAscIIIndex(m, var);
  int i, j, n, shift, k, ni;
  int nump = 1<<var; //add (***lambda***)

 //char* lambda = getLambda(var);  (Assume 111111111),
 //FANG WARNING: changing lambda may raise errors
  char *lambda = bintostr((unsigned long) nump-1, var);

  int ns = M->ns + 1; // add one final state for (w, \lambda, w)
  int sink = find_sink(M);


  //for original transitions
  DFA *result;
  trace_descr tp;
  paths state_paths, pp;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;

  //for new numpath
  numexeps=(char *)malloc((len+1)*sizeof(char));
  numexeps[len]='\0';

  //for traversing M
  max_exeps=1<<var; //remain the same as M
  assert(sink >-1); //assume there is a sink state in M
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));


  dfaSetup(ns, len, mindices);

  //traverse M
  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	to_states[k]=pp->to; //shift one state if init is reachable

	for(n=0; n<m; n++){
	  shift = n*var;
	  if(n==i_track||n==j_track){
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
	  else if (n==k_track){ //Put Lambda
	    for(j=0; j<var; j++)
	      exeps[k*(len+1)+shift+j]=lambda[j];
	  }
	  else{ //Put don't care
	    for(j=0; j<var; j++)
	      exeps[k*(len+1)+shift+j]='X';
	  }
	}//end for
	assert(len == n*var);
	exeps[k*(len+1)+len]='\0';
        k++;
      }
      pp = pp->next;
    }//end while

    if(M->f[i]!=1){
      dfaAllocExceptions(k);
      for(k--;k>=0;k--)
	dfaStoreException(to_states[k],exeps+k*(len+1));
      dfaStoreState(sink);
      statuces[i]='-';
    }
    else{
      dfaAllocExceptions(nump-1+k);
      //add (n,\lambda, n)
      for(ni=0; ni<nump-1; ni++){
	str = bintostr((unsigned long) ni, var);
	for(n=0; n<m; n++){
	  shift = n*var;
	  if(n==i_track || n==k_track)
	    for (j = 0; j < var; j++)
	      numexeps[shift+j]=str[j];
	  else if (n==j_track){ //Put Lambda
	    for(j=0; j<var; j++)
	      numexeps[shift+j]=lambda[j];
	  }else{
	    for(j=0; j<var; j++)
	      numexeps[shift+j]='X';
	  }
	}//end for
	assert(len == n*var);
	//exeps[len]='\0';
	dfaStoreException(M->ns, numexeps); //new state is M->ns
      }
      for(k--;k>=0;k--)
	dfaStoreException(to_states[k],exeps+k*(len+1));
      dfaStoreState(sink);
      statuces[i]='+';
    }
    kill_paths(state_paths);
  }//end for traverse M

  //build the added final state
  dfaAllocExceptions(nump-1);
  //add (n,\lambda, n)
  for(ni=0; ni<nump-1; ni++){
    str = bintostr((unsigned long) ni, var);
    for(n=0; n<m; n++){
      shift = n*var;
      if(n==i_track || n==k_track)
	for (j = 0; j < var; j++)
	  numexeps[shift+j]=str[j];
      else if (n==j_track){ //Put Lambda
	for(j=0; j<var; j++)
	  numexeps[shift+j]=lambda[j];
      }else{
	for(j=0; j<var; j++)
	  numexeps[shift+j]='X';
      }
    }//end for
    assert(len == n*var);
    //exeps[len]='\0';
    dfaStoreException(M->ns, numexeps); //new state is M->ns
  }
  dfaStoreState(sink);
  assert(i==M->ns);
  statuces[i]='+';

  statuces[ns]='\0';
  result = dfaBuild(statuces);
  free(exeps);
  free(numexeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);

}// end dfaGSuffixM


//return x_i = x_j (Precise)
//x_i \in L(M1), x_j \in L(M2)
DFA* mdfaMEqualLR(DFA *M1, DFA *M2, int i_track, int j_track, int m, int var, int* indices){
  DFA* mtmp1 = mdfaOneToManyTrack(M1, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(M2, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGEqual(i_track, j_track, m, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  return mtmp3;
}


//return x_i = x_jc (Precise)
//x_i \in L(M1), x_j \in L(M2)
DFA* mdfaMEqualLRc(DFA *M1, DFA *M2, char* str, int i_track, int j_track, int m, int var, int* indices){
  DFA* tmp = dfa_intersect(M1, dfa_concat_extrabit(M2, dfa_construct_string(str, var, indices), var, indices));
  DFA* mtmp1 = mdfaOneToManyTrack(tmp, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(M2, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);

  //dfaPrintVerbose(mtmp1);
  //dfaPrintVerbose(mtmp2);
  //dfaPrintVerbose(mtmp3);

  dfaFree(tmp);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGPrefixConst(i_track, j_track, str, m, var, indices);
  //dfaPrintVerbose(mtmp1);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  return mtmp3;
}

//X means no condition
DFA* mdfaMEqualXRc(DFA *M2, char* str, int i_track, int j_track, int m, int var, int* indices){
  DFA* tmp = dfa_concat_extrabit(M2, dfa_construct_string(str, var, indices), var, indices);
  DFA* mtmp1 = mdfaOneToManyTrack(tmp, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(M2, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(tmp);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGPrefixConst(i_track, j_track, str, m, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  return mtmp3;
}


//X means no condition
//Xi = concat(Xj, c)
DFA* mdfaMEqualXXc(char* str, int i_track, int j_track, int m, int var, int* indices){
  DFA* Ma = dfaAllStringASCIIExceptReserveWords(var, indices);
  DFA* tmp = dfa_concat_extrabit(Ma, dfa_construct_string(str, var, indices), var, indices);
  DFA* mtmp1 = mdfaOneToManyTrack(tmp, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(Ma, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(tmp);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGPrefixConst(i_track, j_track, str, m, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  dfaFree(Ma);
  return mtmp3;
}

//X means no condition
//Xi = concat(c, Xj) (Approximation)
DFA* mdfaMEqualXcX(char* str, int i_track, int j_track, int m, int var, int* indices){
  DFA* Ma = dfaAllStringASCIIExceptReserveWords(var, indices);
  DFA* tmp = dfa_concat_extrabit(dfa_construct_string(str, var, indices), Ma, var, indices);
  DFA* mtmp1 = mdfaOneToManyTrack(tmp, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(Ma, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(tmp);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGPrefix(i_track, j_track, m, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  dfaFree(Ma);
  return mtmp3;
}






//return x_i = x_jx_k (Approximation)
//x_i \in L(M1), x_j \in L(M2), x_k \in L(M3)
DFA* mdfaMEqualLRR(DFA *M1, DFA *M2, DFA *M3, int i_track, int j_track, int k_track, int m, int var, int* indices){
  DFA* tmp = dfa_intersect(M1, dfa_concat_extrabit(M2, M3, var, indices));
  DFA* mtmp1 = mdfaOneToManyTrack(tmp, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(M2, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);
  //dfaPrintVerbose(tmp);
  //dfaPrintVerbose(mtmp1);
  //dfaPrintVerbose(mtmp2);
  //dfaPrintVerbose(mtmp3);

 dfaFree(tmp);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaOneToManyTrack(M3, m, k_track, var, indices);

  //dfaPrintVerbose(mtmp1);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGPrefix(i_track, j_track, m, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  return mtmp3;
}

//return x_i = x_jx_k (Approximation) Xi is unrestricted
//x_i \in L(M1), x_j \in L(M2), x_k \in L(M3)
DFA* mdfaMEqualXRR(DFA *M2, DFA *M3, int i_track, int j_track, int k_track, int m, int var, int* indices){
  DFA* tmp = dfa_concat_extrabit(M2, M3, var, indices);
  DFA* mtmp1 = mdfaOneToManyTrack(tmp, m, i_track, var, indices);
  DFA* mtmp2 = mdfaOneToManyTrack(M2, m, j_track, var, indices);
  DFA* mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(tmp);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaOneToManyTrack(M3, m, k_track, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  mtmp1 = mdfaGPrefix(i_track, j_track, m, var, indices);
  mtmp2 = mtmp3;
  mtmp3 = dfa_intersect(mtmp1, mtmp2);
  dfaFree(mtmp1);
  dfaFree(mtmp2);
  return mtmp3;
}

int isIncludeLambda(char *str, char* lambda, int var){
  int i;
  for(i=0; i<var; i++){
    if(str[i]!='X' && str[i]!=lambda[i]) return 0;
  }
  return 1;
}

int isEqual2Lambda(char *str, char* lambda, int var){
  int i;
  for(i=0; i<var; i++)
    if(str[i]!=lambda[i]) return 0;
  return 1;
}




DFA *dfaRemoveLambda(DFA* M, int var, int* indices){
  DFA *result;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k;
  char *exeps;
  char *symbol;
  int *to_states;
  int sink;
  long max_exeps;
  char *statuces;
  char* lambda = getLambda(var);

  max_exeps=1<<var; //maybe exponential
  sink=find_sink(M);

  //Add hacking. If there is no sink, return everything
  if(sink <= -1) return dfaAllStringASCIIExceptReserveWords(var, indices);

  assert(sink >-1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(M->ns, var, indices);
  exeps=(char *)malloc(max_exeps*(var+1)*sizeof(char));
  symbol=(char *)malloc((var+1)*sizeof(char));
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));
  symbol[var]='\0';
  for (i = 0; i < M->ns; i++) {
    if(M->f[i]==1) statuces[i] = '+';
    else statuces[i]='-';
    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
    	if(pp->to!=sink){

    		for (j = 0; j < var;  j++) {
    			//the following for loop can be avoided if the indices are in order
    			for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

    			if (tp) {
    				if (tp->value) symbol[j]='1';
    				else symbol[j]='0';
    			}
    			else
    				symbol[j]='X';
    		}
    		if(isEqual2Lambda(symbol, lambda, var)){
    			statuces[i]='+';
    		}else{
    			for(j = 0; j<var; j++) exeps[k*(var+1)+j]=symbol[j];
    			exeps[k*(var+1)+var]='\0';
    			to_states[k]=pp->to;
    			k++;
    		}
    	}
    	pp = pp->next;
    }//end while

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(var+1));
    dfaStoreState(sink);

    kill_paths(state_paths);
  }//end for
  statuces[i]='\0';
  result = dfaBuild(statuces);
  if(_FANG_DFA_DEBUG) dfaPrintVerbose(result);
  free(exeps);
  free(symbol);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);
}



DFA *dfaRemovePreLambda(DFA *M, char* lambda, int var, int *oldindices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;
  int aux=0;
  struct int_list_type *states=NULL;
  struct int_type *tmpState=NULL;

  int maxCount = 0;

  int *indices = oldindices; //indices is updated if you need to add auxiliary bits

  paths state_paths, pp;
  trace_descr tp;

  int i, j, z;

  char *exeps;
  int *to_states;
  long max_exeps, k;
  char *statuces;
  int len=var;
  int sink;

  char *auxbit=NULL;

  char *symbol;

  symbol=(char *)malloc((var+1)*sizeof(char));

  states = reachable_states_lambda_in_nout(M, lambda, var);
  if(states == NULL) return dfaASCIIOnlyNullString(var, indices);

  maxCount = states->count;

  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    aux = get_hsig(maxCount);
    if(_FANG_DFA_DEBUG) printf("\n There are %d reachable states, need to add %d auxiliary bits\n", maxCount, aux);
    auxbit = (char *) malloc(aux*sizeof(char));
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
  }



  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  assert(sink >-1);

  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i


  dfaSetup(M->ns+1, len, indices); //add one new initial state
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+2)*sizeof(char));

  //printf("Before Replace Char\n");
  //dfaPrintVerbose(M);

  k=0;
  //setup for the initial state
  tmpState = states->head;
	for (z = 1; z <= states->count; z++) {
		state_paths = pp = make_paths(M->bddm, M->q[tmpState->value]);
		while (pp) {
			if (pp->to != sink) {
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);

					if (tp) {
						if (tp->value)
							symbol[j] = '1';
						else
							symbol[j] = '0';
					} else
						symbol[j] = 'X';
				}
				symbol[j] = '\0';

				if (!isIncludeLambda(symbol, lambda, var)) { // Only Consider Non-lambda case
					to_states[k] = pp->to + 1;
					for (j = 0; j < var; j++)
						exeps[k * (len + 1) + j] = symbol[j];

					set_bitvalue(auxbit, aux, z); // aux = 3, z=4, auxbit 001
					for (j = var; j < len; j++) { //set to xxxxxxxx100
						exeps[k * (len + 1) + j] = auxbit[len - j - 1];
					}
					exeps[k * (len + 1) + len] = '\0';
					k++;
				}
			} //end if
			pp = pp->next;
		} //end while
		kill_paths(state_paths);
		tmpState = tmpState->next;
	} //end for

  dfaAllocExceptions(k);
  for(k--;k>=0;k--)
    dfaStoreException(to_states[k],exeps+k*(len+1));
  dfaStoreState(sink+1);

  if(check_accept(M, states))	statuces[0]='+';
  else 	statuces[0]='-';



  //for the rest of states (shift one state)
	for (i = 0; i < M->ns; i++) {

		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;

		while (pp) {
			if (pp->to != sink) {
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp =
							tp->next)
						;

					if (tp) {
						if (tp->value)
							symbol[j] = '1';
						else
							symbol[j] = '0';
					} else
						symbol[j] = 'X';
				}

				if (!isEqual2Lambda(symbol, lambda, var)) { // Only Consider Non-lambda case
					to_states[k] = pp->to + 1;
					for (j = 0; j < var; j++)
						exeps[k * (len + 1) + j] = symbol[j];
					for (j = var; j < len; j++) { //set to xxxxxxxx100
						exeps[k * (len + 1) + j] = '0';
					}
					exeps[k * (len + 1) + len] = '\0';
					k++;
				}

			}
			pp = pp->next;
		} //end while

		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink + 1);

		if (M->f[i] == 1)
			statuces[i + 1] = '+';
		else
			statuces[i + 1] = '-';
		kill_paths(state_paths);
	}

	statuces[M->ns + 1] = '\0';
	result = dfaBuild(statuces);
	//	dfaPrintVerbose(result);
	for (i = 0; i < aux; i++) {
		j = len - i - 1;
		tmpM = dfaProject(result, (unsigned) j);
		dfaFree(result);
		result = dfaMinimize(tmpM);
		dfaFree(tmpM);
		//		printf("\n After projecting away %d bits", j);
		//		dfaPrintVerbose(result);
	}
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);

  if(maxCount>0) free(auxbit);

  free_ilt(states);

  return dfaMinimize(result);

}








DFA *dfaGetTrack(DFA *M, int i_track, int m, int var, int* indices){
  DFA *result = M;
  DFA *temp;
  int i, j;
  int flag =0;
  int* map =allocateIFirstMutipleAscIIIndex(m, i_track, var);
  for(i=m-1; i>=0; i--){
    if(i!=i_track){
      for (j=var-1; j>=0; j--){
	//dfaPrintVerbose(result);
	temp = dfaProject(result, i*var+j);
	//printf("\n Get track %d: project away the track %d\n", i_track, i);
	if(flag)
	  dfaFree(result);
	result=dfaMinimize(temp);
	flag = 1;
	dfaFree(temp);
      }
    }
  }

  //printf("\n End of projection");
  //dfaPrintVerbose(result);

  dfaReplaceIndices(result, map);
  //dfaPrintVerbose(M);
  //dfaPrintVerbose(result);
  return dfaRemoveLambda(result, var, indices);
}


DFA *dfaGetTrackNoPreLambda(DFA *M, int i_track, int m, int var, int* indices){
  DFA *result = M;
  DFA *temp;
  int i, j;
  int flag =0;
  int* map =allocateIFirstMutipleAscIIIndex(m, i_track, var);
  for(i=m-1; i>=0; i--){
    if(i!=i_track){
      for (j=var-1; j>=0; j--){
	//dfaPrintVerbose(result);
	temp = dfaProject(result, i*var+j);
	//printf("\n Get track %d: project away the track %d\n", i_track, i);
	if(flag)
	  dfaFree(result);
	result=dfaMinimize(temp);
	flag = 1;
	dfaFree(temp);
      }
    }
  }

  //printf("\n End of projection");
  //dfaPrintVerbose(result);

  dfaReplaceIndices(result, map);
  //dfaPrintVerbose(result);
  return dfaRemovePreLambda(result, getLambda(var), var, indices);
}





DFA* mdfa_project(DFA* M, int i_track, int m, int var, int* indices){
  DFA *result = M;
  DFA *temp;
  int i, j;
  int flag =0;
  for(i=0; i<m; i++){
    if(i==i_track){
      for (j=0; j<var; j++){
	temp = dfaProject(result, i*var+j);
	//printf("\n Multitrack projection: track %d is away\n", i);
	if(flag)
	  dfaFree(result);
	result=dfaMinimize(temp);
	flag = 1;
	dfaFree(temp);
      }
    }
  }
  return result;
}//end mdfa_project


DFA *mdfaShiftToExtraTrack(DFA *M, int i_track, int m , int var, int* indices){

  DFA *result;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, n, shift;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps;
  char *statuces;
  int* mindices =allocateMutipleAscIIIndex(m+1, var); //add one extra track

  int len = (m+1)*var;
  max_exeps=1<<m*var; //maybe exponential
  sink=find_sink(M);
  assert(sink >-1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(M->ns, len, mindices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));

  for (i = 0; i < M->ns; i++) {
    if(M->f[i]==1) statuces[i] = '+';
    else statuces[i] = '-';
    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for(n = 0; n<m; n++){
	  shift = k*(len+1)+n*var;
	  if(n!=i_track){
	    for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	      for (tp = pp->trace; tp && (tp->index != mindices[n*var+j]); tp =tp->next);
	      if (tp) {
		if (tp->value) exeps[shift+j]='1';
		else exeps[shift+j]='0';
	      }
	      else
		exeps[shift+j]='X';
	    }
	  }else{ //move i_track to m and leave i be unconditional
	    for (j = 0; j < var; j++) {

	      exeps[shift+j]='X';

	      for (tp = pp->trace; tp && (tp->index != mindices[n*var+j]); tp =tp->next);
	      if (tp) {
		if (tp->value) exeps[k*(len+1)+m*var+j]='1';
		else exeps[k*(len+1)+m*var+j]='0';
	      }
	      else
		exeps[k*(len+1)+m*var+j]='X';
	    }
	  }//end if n!=i_track
	}
	exeps[k*(len+1)+len]='\0';
	to_states[k]=pp->to;
	k++;
      }
      pp = pp->next;
    }//end while

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(var+1));
    dfaStoreState(sink);

    kill_paths(state_paths);
  }//end for
  statuces[M->ns]='\0';
  result = dfaBuild(statuces);
  //dfaPrintVerbose(M);
  //dfaPrintVerbose(result);
  free(exeps);
  free(to_states);
  free(statuces);
  return dfaMinimize(result);

}

//return x_i:=x_jc
DFA *mdfaAssignLRc(DFA *M, char* str, int i_track, int j_track, int m, int var, int* indices){

  DFA* Mj = NULL;
  DFA* M_1 = NULL;
  DFA* M_2 = NULL;
  DFA* result = NULL;
  if(i_track == j_track){ // X:=Xc
    Mj = dfaGetTrack(M, j_track, m, var, indices);
    M_1 = mdfaMEqualXRc(Mj, str, i_track, m+1, m+1, var, indices); //i = m+1.c
    //dfaPrintVerbose(M_1);

    dfaFree(Mj);
    //dfaPrintVerbose(M);
    M_2 = mdfaShiftToExtraTrack(M, i_track, m , var, indices);
    result = mdfa_project(dfa_intersect(M_1, M_2), m+1, m+1, var, indices);
    printf("\n After project away extra track:");
    //dfaPrintVerbose(result);
  }else{//X:=Yc
    Mj = dfaGetTrack(M, j_track, m, var, indices);
    M_1 = mdfaMEqualXRc(Mj, str, i_track, j_track, m, var, indices); //i = j.c
    dfaFree(Mj);
    M_2 = mdfa_project(M, i_track, m, var, indices);
    result = dfa_intersect(M_1, M_2); //Note M_1 has m-1 tracks but M_2 has m tracks
  }
  dfaFree(M_1);
  dfaFree(M_2);
  // dfaFree(tmp);
  return result;
}

//return x_i := x_jx_k
DFA *mdfaAssignLRR(DFA *M, int i_track, int j_track, int k_track, int m, int var, int* indices){
  DFA* Mk = NULL;
  DFA* Mj = NULL;
  DFA* M_1 = NULL;
  DFA* M_2 = NULL;
  DFA* result = NULL;
  Mj = dfaGetTrack(M, j_track, m, var, indices);
  //dfaPrintVerbose(Mj);
  Mk = dfaGetTrack(M, k_track, m, var, indices);
  //dfaPrintVerbose(Mk);

  if(i_track == j_track){ // X_j:=X_jX_k
    M_1 = mdfaMEqualXRR(Mj, Mk, i_track, m+1, k_track, m+1, var, indices); //i = m+1.k
    M_2 = mdfaShiftToExtraTrack(M, i_track, m , var, indices);
    result = mdfa_project(dfa_intersect(M_1, M_2), m+1, m+1, var, indices);
  }else{//X_i:=X_jX_k
    M_1 = mdfaMEqualXRR(Mj, Mk,  i_track, j_track, k_track, m, var, indices); //i = j.k
    M_2 = mdfa_project(M, i_track, m, var, indices);
    result = dfa_intersect(M_1, M_2); //Note M_1 has m-1 tracks but M_2 has m tracks
  }
  dfaFree(M_1);
  dfaFree(M_2);
  dfaFree(Mj);
  dfaFree(Mk);
  return result;
}
