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
 * Authors: Fang Yu, Muath Alkhalaf
 */


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

//for internal
#include "stranger_lib_internal.h"


/***************************************************

Replace function

***************************************************/





//Replace any c \in {sharp1} \vee bar \vee {sharp2} with \epsilon (Assume 00000000000)
DFA *dfa_replace_delete(DFA *M, int var, int *oldindices)
{
      DFA *result = NULL;
  DFA *tmpM2 = NULL;
  DFA *tmpM1 = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, o, z, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var;
  int sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;

  //printf("Start get match exclude\n");
  pairs = get_match_exclude_self(M, var, indices); //for deletion, exclude self state from the closure
  //printf("End get match exclude\n");
  maxCount = get_maxcount(pairs, M->ns);
  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    //printf("Deletion [insert auxiliary bits]!\n");
    aux = get_hsig(maxCount);
    len = var+aux;
    auxbit = (char *) malloc(aux*sizeof(char));
    indices = allocateArbitraryIndex(len);
  }

  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  assert(sink >-1);

  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i


  dfaSetup(M->ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));


  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {//it is bar value
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0';
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;
	  if(pairs[pp->to]!=NULL && pairs[pp->to]->count>0){ //need to add extra edges to states in reachable closure
	    o=k-1; //the original path
	    for(z=0, tmp=pairs[pp->to]->head;z<pairs[pp->to]->count; z++, tmp = tmp->next){
	      to_states[k]=tmp->value;
	      for (j = 0; j < var; j++) exeps[k*(len+1)+j]=exeps[o*(len+1)+j];
	      set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	      for (j = var; j < len; j++) { //set to xxxxxxxx100
		exeps[k*(len+1)+j]=auxbit[len-j-1];
	      }
              exeps[k*(len+1)+len]='\0';
	      k++;
	    }
	  }
	}
      }
      pp = pp->next;
    }//end while

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='0';

    kill_paths(state_paths);
  }

  statuces[M->ns]='\0';
  tmpM2=dfaBuild(statuces);
  //dfaPrintVitals(result);
  for(i=0; i<aux; i++){
    j=len -i;
	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace_delete : states %d : bddnodes %u : before projection : loop %d \n", tmpM2->ns, bdd_size(tmpM2->bddm), i );
    tmpM1 =dfaProject(tmpM2, (unsigned) j);
      dfaFree(tmpM2); tmpM2 = NULL;
	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace_delete : states %d : bddnodes %u : after projection : loop %d \n", tmpM1->ns, bdd_size(tmpM1->bddm), i );
    tmpM2 = dfaMinimize(tmpM1);
      dfaFree(tmpM1); tmpM1 = NULL;
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);

  if(maxCount>0) free(auxbit);

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);
  free(pairs);
  if( DEBUG_SIZE_INFO )
	  printf("\t peak : replace_delete : states %d : bddnodes %u \n", tmpM2->ns, bdd_size(tmpM2->bddm) );
  result = dfaMinimize(tmpM2);	//MUST BE CAREFUL FOR INDICES..INDICES MAY NOT MATCH!!
    dfaFree(tmpM2);
    return result;

}




//Replace sharp1 bar sharp2 to str. str is a single char
//for all i, if pairs[i]!=NULL, add path to each state in pairs[i]
DFA *dfa_replace_char(DFA *M, char a, int var, int *oldindices)
{
    DFA *result = NULL;
  DFA *tmpM1 = NULL;
  DFA *tmpM2 = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount = 0;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, z, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var;
  int sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;
  char *apath =bintostr(a, var);

  pairs = get_match(M, var, indices);
  maxCount = get_maxcount(pairs, M->ns);

  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    aux = get_hsig(maxCount);
    //	printf("Replace one char: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
    auxbit = (char *) malloc(aux*sizeof(char));
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
  }



  max_exeps=1<<len; //maybe exponential
//    printf("len in dfa_replace_char = %d, max_exeps = %ld\n", len, max_exeps);
  sink=find_sink(M);
  assert(sink >-1);

  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i


  dfaSetup(M->ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));

  //printf("Before Replace Char\n");
  //dfaPrintVerbose(M);

  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0';
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

	}
      }
      pp = pp->next;
    }//end while

    if(pairs[i]!=NULL && pairs[i]->count>0){ //need to add extra edges to states in reachable closure

      for(z=0, tmp=pairs[i]->head;z< pairs[i]->count; z++, tmp = tmp->next){
	to_states[k]=tmp->value;
	for (j = 0; j < var; j++) exeps[k*(len+1)+j]=apath[j];
	set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	for (j = var; j < len; j++) { //set to xxxxxxxx100
	  exeps[k*(len+1)+j]=auxbit[len-j-1];
	}
	exeps[k*(len+1)+len]='\0';
	k++;
      }
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='0';

    kill_paths(state_paths);
  }

  statuces[M->ns]='\0';
  tmpM1=dfaBuild(statuces);
  //dfaPrintVitals(result);
  for(i=0; i<aux; i++){
    j=len-i; //len = var
	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace_char : states %d : bddnodes %u : before projection : loop %d \n", tmpM1->ns, bdd_size(tmpM1->bddm), i );
    tmpM2 =dfaProject(tmpM1, (unsigned) j);
      dfaFree(tmpM1); tmpM1 = NULL;
	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace char : states %d : bddnodes %u : after projection : loop %d \n", tmpM2->ns, bdd_size(tmpM2->bddm), i );
    tmpM1 = dfaMinimize(tmpM2);
      dfaFree(tmpM2); tmpM2 = NULL;
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);

  free(apath);

  if(maxCount>0) free(auxbit);

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);
  free(pairs);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace_char : states %d : bddnodes %u \n", tmpM1->ns, bdd_size(tmpM1->bddm) );
    result = dfaMinimize(tmpM1);
    dfaFree(tmpM1);
    return result;


}


int count_accepted_chars(DFA* M){
  paths state_paths, pp;
  int k=0;
  int sink = find_sink(M);
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  while (pp){
    if(pp->to!=sink && (M->f[pp->to]==1))  k++;
    pp = pp->next;
  }
  return k;
}



void set_accepted_chars(DFA* M,char** apath, int numchars, int var, int* indices){

  paths state_paths, pp;
  trace_descr tp;
  int k=0;
  int j;
  int sink = find_sink(M);
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  while (pp){
    if(pp->to!=sink && (M->f[pp->to]==1)){
      apath[k] = (char *) malloc(var*sizeof(char));
       for (j = 0; j < var; j++) {
	 //the following for loop can be avoided if the indices are in order
	 for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	 if (tp) {
	   if (tp->value) apath[k][j]='1';
	   else apath[k][j]='0';
	 }
	 else
	   apath[k][j]='X';
       }
      k++;
    }
    pp = pp->next;
  }
  assert(k==numchars); // the number of added apaths shall be equal to numchars
}

//Replace sharp1 bar sharp2 to Mr. Mr accepts a set of single chars
//for all i, if pairs[i]!=NULL, add path to each state in pairs[i]
DFA *dfa_replace_M_dot(DFA *M, DFA* Mr, int var, int *oldindices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount = 0;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, z, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var;
  int sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;

  //Get from Mr
  int nc;
  int numchars = count_accepted_chars(Mr);
  char* apath[numchars];
  set_accepted_chars(Mr, apath, numchars, var, indices);

  pairs = get_match(M, var, indices);
  maxCount = get_maxcount(pairs, M->ns);

  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    aux = get_hsig(maxCount);
    //	printf("Replace one char: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
    auxbit = (char *) malloc(aux*sizeof(char));
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
  }



  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  assert(sink >-1);

  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i


  dfaSetup(M->ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));

  //printf("Before Replace Char\n");
  //dfaPrintVerbose(M);

  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0';
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

	}
      }
      pp = pp->next;
    }//end while

    if(pairs[i]!=NULL && pairs[i]->count>0){ //need to add extra edges to states in reachable closure

      for(z=0, tmp=pairs[i]->head;z< pairs[i]->count; z++, tmp = tmp->next){
	set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	for(nc = 0; nc<numchars; nc++){
	  to_states[k]=tmp->value;
	  for (j = 0; j < var; j++) exeps[k*(len+1)+j]=apath[nc][j];
	  for (j = var; j < len; j++) { //set to xxxxxxxx100
	    exeps[k*(len+1)+j]=auxbit[len-j-1];
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;
	} // end for nc
      }	//end for z
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='0';

    kill_paths(state_paths);
  }

  statuces[M->ns]='\0';
  result=dfaBuild(statuces);
  //dfaPrintVitals(result);
  for(i=0; i<aux; i++){
    j=len-i;
    tmpM =dfaProject(result, (unsigned) j);
    result = dfaMinimize(tmpM);
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);

  //free(apath);
  for(i=0; i<numchars; i++) free(apath[i]);

  if(maxCount>0){
    free(auxbit);
    free(indices);
  }

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);
  free(pairs);

  return dfaMinimize(result);

}// End dfa_replace_M_dot


//Get outgoing information from M and fulfill in
//num: number of outgoing edges
//final: number of outgoing edges to final states
//bin: the binary value along the outgoing edge (add aux bits 0 at the tail)
//to: the destination of the outgoing edge

void initial_out_info(DFA* M, int* num, int* final, char*** bin, int** to, int var, int aux, int* indices){

  int i, j, k;
  paths state_paths, pp;
  trace_descr tp;
  int sink = find_sink(M);


  //initialize num

  for(i = 0; i<M->ns; i++){
    k =0;
    state_paths = pp = make_paths(M->bddm, M->q[i]);
    while (pp){
      if(pp->to!=sink)  k++;
      pp = pp->next;
    }
    num[i] = k;
    final[i] = 0;
    kill_paths(state_paths);
  }

  //initialize binary of each outgoing edges

  for(i = 0; i<M->ns; i++){
	  if(num[i]>0){
	  bin[i] = (char **) malloc((num[i])*sizeof(char *));
	  to[i] = (int *) malloc((num[i])*sizeof(int));
	  k=0;
	  state_paths = pp = make_paths(M->bddm, M->q[i]);
	  while (pp){
		  if(pp->to!=sink){

			  bin[i][k]=(char *) malloc((var+aux+1)*sizeof(char)); //may lead to memory leak
			  to[i][k] = pp->to;
			  if(M->f[pp->to] == 1) final[i]++;

			  for (j = 0; j < var; j++) {
				  //the following for loop can be avoided if the indices are in order
				  for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

				  if (tp) {
					  if (tp->value) bin[i][k][j]='1';
					  else bin[i][k][j]='0';
				  }
				  else
					  bin[i][k][j]='X';
			  }
			  for(j=var; j<var+aux; j++) bin[i][k][j]='0';

			  bin[i][k][j]= '\0';//end of string
			  k++;
		  }//end if != sink
		  pp = pp->next;
	  }//end while
	  kill_paths(state_paths);
	  }else{
		  bin[i] = NULL;
		  to[i] = NULL;
	  }
  }

}//end initial_out_info




//Replace every pairs(i,j), so that i can reach j through sharp1 bar sharp0, to i Mr j,
//where Mr is the replacement, whihc can be an arbitrary DFA accepting words >1
DFA *dfa_replace_M_arbitrary(DFA *M, DFA *Mr, int var, int *oldindices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount, numberOfSharp;


  paths state_paths, pp;
  trace_descr tp;
  int i, j, z, n, o, k, numsharp2;
  int s=0;
  char *exeps;
  char *auxexeps=NULL;
  int *to_states;
  int *aux_to_states=NULL;
  long max_exeps;
  char *statuces;
  int len=var;
  int ns, sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;

  int extrastates = Mr->ns; //duplicate states for each sharp pair

  //for out going information in Mr
  char ***binOfOut = (char ***) malloc((Mr->ns)*sizeof(char **)); //the string of the nonsink outgoing edge of each state
  int **toOfOut = (int **) malloc((Mr->ns)*sizeof(int *)); // the destination of the nonsink outgoing edge of each state
  int *numOfOut = (int *) malloc((Mr->ns)*sizeof(int)); // how many nonsink outgoing edges of each state
  int *numOfOutFinal = (int *) malloc((Mr->ns)*sizeof(int)); //how many final outgoing edges of each state

  int *startStates = NULL;



  pairs = get_match(M, var, indices);

  maxCount = get_maxcount(pairs, M->ns);
  numberOfSharp = get_number_of_sharp1_state(pairs, M->ns);


  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges

    aux = get_hsig(maxCount);//get the highest significant bit
    if(_FANG_DFA_DEBUG) printf("Replace Arbitrary M: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
    auxbit = (char *) malloc(aux*sizeof(char));//the redundant bits to distinguish outgoing edges
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
    s=0;
    startStates = (int *) malloc(numberOfSharp*sizeof(int));
    for(i =0; i<numberOfSharp; i++){
      startStates[i]=-1; //initially it is -1. There is an error if some of them are not set up later.
    }
    auxexeps=(char *)malloc(maxCount*(len+1)*sizeof(char));
    aux_to_states=(int *)malloc(maxCount*sizeof(int));
  }

  initial_out_info(Mr, numOfOut, numOfOutFinal, binOfOut, toOfOut, var, aux, indices);


  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  assert(sink >-1);
  ns = M->ns + numberOfSharp*extrastates;

  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
  dfaSetup(ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));



  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0'; //all original paths are set to zero
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

	}
      }
      pp = pp->next;
    }//end while

    if(pairs[i]!=NULL && pairs[i]->count>0){ //need to add extra edges to states in reachable closure
      startStates[s]=i; //pairs[startStates[s]] is the destination that later we shall use for region s
      for(o=0; o<numOfOut[Mr->s]; o++){
	to_states[k]=M->ns+s*(extrastates)+toOfOut[Mr->s][o]; // go to the next state of intial state of  Mr
	for(j = 0; j < var; j++) exeps[k*(len+1)+j]=binOfOut[Mr->s][o][j];
	for(j = var; j< len-1; j++) exeps[k*(len+1)+j] = '0';
	exeps[k*(len+1)+j]='1'; //to distinguish the original path
	exeps[k*(len+1)+len]='\0';
	k++;
      }
      s++;
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);

  }//end for i

  assert(s==numberOfSharp);
  assert(i==M->ns);

  //Add replace states
  for(n=0;n<numberOfSharp; n++){
    assert((pairs[startStates[n]]!=NULL) && (pairs[startStates[n]]->count > 0));
    numsharp2 = pairs[startStates[n]]->count;
    for(i=0; i<Mr->ns; i++){ //internal M (exclude the first and the last char)
      if(numOfOutFinal[i]==0){
	dfaAllocExceptions(numOfOut[i]);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	}
	dfaStoreState(sink);
      }else{//need to add aux edges back to sharp destination, for each edge leads to accepting state
	dfaAllocExceptions(numOfOut[i]+numOfOutFinal[i]*numsharp2);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	  if(Mr->f[toOfOut[i][o]]==1){ //add auxiliary back edges
	    for(z=0, tmp=pairs[startStates[n]]->head;z< numsharp2; z++, tmp = tmp->next){
	      aux_to_states[z]=tmp->value;
	      for (j = 0; j < var; j++) auxexeps[z*(len+1)+j]=binOfOut[i][o][j];
	      set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
	      for (j = var; j < len; j++) { //set to xxxxxxxx100
		auxexeps[z*(len+1)+j]=auxbit[len-j-1];
	      }
	      auxexeps[z*(len+1)+len]='\0';
	    }

	    for(z--;z>=0;z--)
	      dfaStoreException(aux_to_states[z],auxexeps+z*(len+1));
	  }
	}
	dfaStoreState(sink);
      }
    }//end for Mr internal
  }

  for(i=M->ns; i<ns; i++) statuces[i]='-';

  statuces[ns]='\0';
  result=dfaBuild(statuces);

  for(i=0; i<aux; i++){
    j=len-i;
    if(_FANG_DFA_DEBUG){
      printf("Project the %d bit\n", i);
      printf("Original:%d", i);
      dfaPrintVitals(result);
    }

    tmpM =dfaProject(dfaMinimize(result), (unsigned) j);

    if(_FANG_DFA_DEBUG){
      printf("Projected:%d", i);
      dfaPrintVitals(tmpM);
    }
    dfaFree(result);
    result = dfaMinimize(tmpM);
    dfaFree(tmpM);
    if(_FANG_DFA_DEBUG){
      printf("Minimized:%d", i);
      dfaPrintVitals(result);
    }
  }
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);



  if(maxCount>0){
    free(auxbit);
    free(aux_to_states);
    free(auxexeps);
    free(indices);
    free(startStates);
  }

  for(i=0; i<M->ns; i++)
    free_ilt(pairs[i]);

  for(i=0; i<Mr->ns; i++){
    free(binOfOut[i]);
    free(toOfOut[i]);
  }



  free(binOfOut);
  free(toOfOut);
  free(numOfOut);
  free(numOfOutFinal);

  free(pairs);

  return dfaMinimize(result);

}


char **get_bitstrings(char *str, int var, int aux){

  int j;
  char **result;
  size_t i = strlen(str);
  result = (char **)malloc(i*sizeof(char*));
  for(j=0; j<i; j++)
    result[j] = bintostrWithExtraBitsZero(str[j], var, aux);
  return result;
}

//Replace sharp1 bar sharp2 to str.
DFA *dfa_replace_string(DFA *M, char *str, int var, int *oldindices)
{
  DFA *result = NULL;
    DFA *tmpM1 = NULL;
  DFA *tmpM2 = NULL;
  int aux=0;
  struct int_list_type **pairs=NULL;
  int maxCount, numberOfSharp;


  paths state_paths, pp;
  trace_descr tp;
  int i, j, z, k;
  int s=0;
  char *exeps;
  char *auxexeps=NULL;
  int *to_states;
  int *aux_to_states=NULL;
  long max_exeps;
  char *statuces;
  int len=var;
  int ns, sink;
  int *indices=oldindices;
  char *auxbit=NULL;
  struct int_type *tmp=NULL;
  int extrastates = (int) strlen(str)-1;
  char **binOfStr=NULL;
  int *startStates = NULL;



  pairs = get_match(M, var, indices);

  maxCount = get_maxcount(pairs, M->ns);
  numberOfSharp = get_number_of_sharp1_state(pairs, M->ns);

  if(maxCount>0){ //Need auxiliary bits when there exist some outgoing edges
    aux = get_hsig(maxCount);
    //		printf("Replace string: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
    auxbit = (char *) malloc(aux*sizeof(char));
    len = var+aux; // extra aux bits
    indices = allocateArbitraryIndex(len);
    binOfStr = get_bitstrings(str, var, aux); //initially extra bit are zero
    s=0;
    startStates = (int *) malloc(numberOfSharp*sizeof(int));
    for(i =0; i<numberOfSharp; i++){
      startStates[i]=-1; //initially it is -1. There is an error if some of them are not set up later.
    }
    auxexeps=(char *)malloc(maxCount*(len+1)*sizeof(char));
    aux_to_states=(int *)malloc(maxCount*sizeof(int));
  }



  max_exeps=1<<len; //maybe exponential
//  printf("len in dfa_replace_string = %d, max_exeps = %ld\n", len, max_exeps);
  sink=find_sink(M);
  assert(sink >-1);
  ns = M->ns + numberOfSharp* (extrastates);
//  printf("old number of states in dfa_replace_string = %d, new number of states = %d\n", M->ns, ns);
  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
  dfaSetup(ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));



  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0'; //all original paths are set to zero
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;
	}
      }
      pp = pp->next;
    }//end while

    if(pairs[i]!=NULL && pairs[i]->count>0){ //need to add extra edges to states in reachable closure
      startStates[s]=i; //pairs[startStates[s]] is the destination that later we shall use for region s
      to_states[k]=M->ns+s*(extrastates); // go to the initial state of string by the first char
      s++;
      for (j = 0; j < len; j++) exeps[k*(len+1)+j]=binOfStr[0][j];
      exeps[k*(len+1)+len-1]='1'; //to distinguish the original path
      exeps[k*(len+1)+len]='\0';
      k++;
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }//end for

  assert(s==numberOfSharp);
  assert(i==M->ns);

  for(i=0;i<numberOfSharp; i++){
    for(j=0; j<extrastates-1; j++){ //internal string (exclude the first and the last char)
      dfaAllocExceptions(1);
      dfaStoreException(M->ns+i*(extrastates)+j+1, binOfStr[j+1]);
      dfaStoreState(sink);
    }
    assert((pairs[startStates[i]]!=NULL) && (pairs[startStates[i]]->count > 0));

    //for the end state add pathes to get back to pair[startStates[i]]


    for(z=0, tmp=pairs[startStates[i]]->head;z< pairs[startStates[i]]->count; z++, tmp = tmp->next){
      aux_to_states[z]=tmp->value;
      for (j = 0; j < var; j++) auxexeps[z*(len+1)+j]=binOfStr[extrastates][j];
      set_bitvalue(auxbit, aux, z+1); // aux = 3, z=4, auxbit 001
      for (j = var; j < len; j++) { //set to xxxxxxxx100
	auxexeps[z*(len+1)+j]=auxbit[len-j-1];
      }
      auxexeps[z*(len+1)+len]='\0';
    }
    dfaAllocExceptions(z);
    for(z--;z>=0;z--)
      dfaStoreException(aux_to_states[z],auxexeps+z*(len+1));
    dfaStoreState(sink);
  }

  for(i=M->ns; i<ns; i++) statuces[i]='0';

  statuces[ns]='\0';
  result=dfaBuild(statuces);
    
    free(exeps);
    //printf("FREE ToState\n");
    free(to_states);
    //printf("FREE STATUCES\n");
    free(statuces);
    
    if(maxCount>0){
        free(auxbit);
        free(aux_to_states);
        free(auxexeps);
        free(indices);
        free(startStates);
        for(i=0; i<strlen(str); i++) free(binOfStr[i]);
        free(binOfStr);
    }
    
    for(i=0; i<M->ns; i++)
        free_ilt(pairs[i]);
    free(pairs);

    
    
//    printf("Replace automaton built. Now minimizing and projecting\n");

	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace_string : states %d : bddnodes %u : before loop \n", result->ns, bdd_size(result->bddm) );
  tmpM1 = dfaMinimize(result);
  dfaFree(result); result = NULL;
    
  for(i=0; i<aux; i++){
    j=len-i;
//    if(_FANG_DFA_DEBUG){
//      printf("Project the %d bit\n", i);
//      printf("Original:%d\n", i);
//      dfaPrintVitals(result);
//    }
      if( DEBUG_SIZE_INFO )
    	  printf("\t peak : replace_string : states %d : bddnodes %u : before projection : loop %d \n", tmpM1->ns, bdd_size(tmpM1->bddm), i );
    tmpM2 =dfaProject(tmpM1, (unsigned) j);
      dfaFree(tmpM1); tmpM1 = NULL;
//    if(_FANG_DFA_DEBUG){
//      printf("Projected:%d\n", i);
//      dfaPrintVitals(tmpM2);
//    }
		if( DEBUG_SIZE_INFO )
			printf("\t peak : replace_string : states %d : bddnodes %u : after projection : loop %d \n", tmpM2->ns, bdd_size(tmpM2->bddm), i );
    tmpM1 = dfaMinimize(tmpM2);
      dfaFree(tmpM2); tmpM2 = NULL;
//    if(_FANG_DFA_DEBUG){
//      printf("Minimized:%d\n", i);
//      dfaPrintVitals(result);
//    }
  }
  
  return tmpM1;

}




DFA *dfa_replace_step3_replace(DFA *M, char *str, int var, int *indices)
{
  DFA *result=NULL;
  if((str ==NULL)||strlen(str)==0){
//    printf("Replacement [%s]!\n", str);
    result = dfa_replace_delete(M, var, indices);
  }else if(strlen(str)==1){
//    printf("Replacement [%s]!\n", str);
    result = dfa_replace_char(M, str[0], var, indices);
  }else {
//    printf("Replacement [%s]!\n", str);
    result = dfa_replace_string(M, str, var, indices);
  }
  return result;
} //END dfa_replace_stpe3_replace


DFA *dfa_replace_step3_general_replace(DFA *M, DFA* Mr, int var, int *indices)
{
  DFA *result0 = NULL;
  DFA *result1 = NULL;
  DFA *result2 = NULL;
  DFA *result = NULL;
  DFA *tmp = NULL;

  if(Mr->f[M->s]==1){
    //printf("Replacement [%s]!\n", str);
    result0 = dfa_replace_delete(M, var, indices);
    result = result0;
  }


  tmp = dfa_intersect(Mr, dfaDot(var, indices));
  if(!check_emptiness(tmp, var, indices)){
    result1 = dfa_replace_M_dot(M, tmp, var, indices);
    if(result){
      result = dfa_union(result, result1);
      dfaFree(result0);
      dfaFree(result1);
    }
    else result = result1;
  }

  dfaFree(tmp);
  tmp = dfa_intersect(Mr, dfaSigmaC1toC2(2, -1, var, indices));

  if(!check_emptiness(tmp, var, indices)){
    //replace rest rather than single character
    result2 = dfa_replace_M_arbitrary(M, tmp, var, indices);

   if(result){
     result1 = result;
     result = dfa_union(result1, result2);
     dfaFree(result1);
     dfaFree(result2);
   }
   else result = result2;
  }
  dfaFree(tmp);
  return result;
} //END dfa_replace_stpe3_general_replace



DFA *dfa_replace_extrabit(M1, M2, str, var, indices)
     DFA *M1;
     DFA *M2;
     char *str;
     int var;
     int *indices;
{
    DFA *temp1;
  DFA *result;
  DFA *M1_bar;
  DFA *M2_bar;
  DFA *M_inter;
  DFA *M_rep;
  DFA *M_sharp = dfaSharpStringWithExtraBit(var, indices);

//  printf("Insert sharp1 and sharp2 for duplicate M1\n");
  M1_bar = dfa_replace_step1_duplicate(M1, var, indices);
    //	dfaPrintVerbose(M1_bar);  //having extra bit
  if(_FANG_DFA_DEBUG) printf("M1_bar: var %d\n", var);
  //dfaPrintVerbose(M1_bar);
  //	dfaPrintGraphviz(M1_bar, var+1, allocateAscIIIndex(var+1));
//  printf("Generate M2 bar sharp1 M2 and sharp2\n");
  M2_bar = dfa_replace_step2_match_compliment(M2, var, indices);
  //	dfaPrintVerbose(M2_bar);  //having extra bit
  if(_FANG_DFA_DEBUG) printf("M2_bar: var %d\n", var);
  //dfaPrintVerbose(M2_bar);
  //	dfaPrintGraphviz(M2_bar, var+1, allocateAscIIIndex(var+1));

//  printf("Generate Intersection\n");
  M_inter = dfa_intersect(M1_bar, M2_bar);
  if(_FANG_DFA_DEBUG){
    printf("M_inter\n");
    dfaPrintVerbose(M_inter);
    dfaPrintGraphviz(M_inter, var+1, allocateAscIIIndexUnsigned(var+1));
    dfaPrintVerbose(M_inter);
  }

//  printf("Check Intersection\n");
  if(check_intersection(M_sharp, M_inter, var, indices)>0){

//    printf("Start Replacement!\n");
    //replace match patterns
    M_rep = dfa_replace_step3_replace(M_inter, str, var, indices);
    temp1=dfaProject(M_rep, (unsigned) var);
    dfaFree(M_rep);

  }else { //no match
    temp1 = dfaCopy(M1);
  }

  //printf("free M1_bar\n");
  dfaFree(M1_bar);
  //printf("free M2_bar\n");
  dfaFree(M2_bar);
  //printf("free M_inter\n");
  dfaFree(M_inter);
  //printf("free M_sharp\n");
  dfaFree(M_sharp);

	if( DEBUG_SIZE_INFO )
		printf("\t peak : replace_extrabit : states %d : bddnodes %u \n", temp1->ns, bdd_size(temp1->bddm) );
  result = dfaMinimize(temp1);
  dfaFree(temp1);
  return result;
}


DFA *dfa_general_replace_extrabit(DFA* M1, DFA* M2, DFA* M3, int var, int* indices){

  DFA *result;
  DFA *M1_bar;
  DFA *M2_bar;
  DFA *M_inter;
  DFA *M_rep;
  DFA *M_sharp = dfaSharpStringWithExtraBit(var, indices);

//  printf("Insert sharp1 and sharp2 for duplicate M1\n");
  M1_bar = dfa_replace_step1_duplicate(M1, var, indices);
  //	dfaPrintVerbose(M1_bar);  //having extra bit
  if(_FANG_DFA_DEBUG) printf("\nGeneral Replace of M1_bar: var %d\n", var);
  //dfaPrintVerbose(M1_bar);
  //	dfaPrintGraphviz(M1_bar, var+1, allocateAscIIIndex(var+1));
  //printf("Generate M2 bar sharp1 M2 and sharp2\n");

  M2_bar = dfa_replace_step2_match_compliment(M2, var, indices);

  //	dfaPrintVerbose(M2_bar);  //having extra bit
  if(_FANG_DFA_DEBUG) printf("\nGeneral Replace of M2_bar: var %d\n", var);
  //dfaPrintVerbose(M2_bar);
  //	dfaPrintGraphviz(M2_bar, var+1, allocateAscIIIndex(var+1));

  //printf("Generate Intersection\n");
  M_inter = dfa_intersect(M1_bar, M2_bar);
  if(_FANG_DFA_DEBUG){
    printf("\nGeneral Replace of M_inter\n");
    dfaPrintVerbose(M_inter);
    dfaPrintGraphviz(M_inter, var+1, allocateAscIIIndexUnsigned(var+1));
    dfaPrintVerbose(M_inter);
  }

  if(check_intersection(M_sharp, M_inter, var, indices)>0){

    //printf("Start Replacement!\n");
    //replace match patterns

    M_rep = dfa_replace_step3_general_replace(M_inter, M3, var, indices);

    if(_FANG_DFA_DEBUG) dfaPrintVerbose(M_rep);
    result = dfaProject(M_rep, (unsigned) var);
    dfaFree(M_rep);

  }else { //no match
    result = dfaCopy(M1);
  }

  //printf("free M1_bar\n");
  dfaFree(M1_bar);
  //printf("free M2_bar\n");
  dfaFree(M2_bar);
  //printf("free M_inter\n");
  dfaFree(M_inter);
  //printf("free M_sharp\n");
  dfaFree(M_sharp);
    
  DFA *tmp = dfaMinimize(result);
  dfaFree(result);
  return tmp;
    
}



//Take Output DFA
DFA *dfa_replace(M1, M2, M3, var, indices)
     DFA *M1;
     DFA *M2;
     DFA *M3;
     int var;
     int *indices;
{
  return dfa_general_replace_extrabit(M1, M2, M3, var, indices);
}



/******************************************************************

Insertion:insert Mr at every state of M

I.e., Output M' so that L(M')={ w0c0w1c1w2c2w3 | c0c1c2 \in L(M), wi \in L(Mr) }

******************************************************************/


DFA *dfa_insert_M_dot(DFA *M, DFA* Mr, int var, int *indices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var+1;
  int sink;

  //Get from Mr
  int nc;
  int numchars = count_accepted_chars(Mr);
  char* apath[numchars];
  set_accepted_chars(Mr, apath, numchars, var, indices);


  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  assert(sink>-1); //dfa_insert_M_dot



  dfaSetup(M->ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((M->ns+1)*sizeof(char));

  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	to_states[k]=pp->to;
	for (j = 0; j < var; j++) {
	  //the following for loop can be avoided if the indices are in order
	  for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	  if (tp) {
	    if (tp->value) exeps[k*(len+1)+j]='1';
	    else exeps[k*(len+1)+j]='0';
	  }
	  else
	    exeps[k*(len+1)+j]='X';
	}
	exeps[k*(len+1)+j]='0';//old value
	exeps[k*(len+1)+len]='\0';
	k++;
      }
      pp = pp->next;
    }//end while

    if(i!=sink){
      for(nc = 0; nc<numchars; nc++){
	to_states[k]=i;
	for (j = 0; j < var; j++) exeps[k*(len+1)+j]=apath[nc][j];
	exeps[k*(len+1)+j]='1';
	exeps[k*(len+1)+len]='\0';
	k++;
      } // end for nc
    }
    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }

  statuces[M->ns]='\0';
  result=dfaBuild(statuces);
  tmpM =dfaProject(result, (unsigned) len-1);
  result = dfaMinimize(tmpM);

  free(exeps);
  free(to_states);
  free(statuces);

  //free(apath);
  for(i=0; i<numchars; i++) free(apath[i]);

  return result;

}// End dfa_insert_M_dot




DFA *dfa_insert_M_arbitrary(DFA *M, DFA *Mr, int var, int *indices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;

  paths state_paths, pp;
  trace_descr tp;
  int i, j, n, o, k;
  char *exeps;
  char *auxexeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var+1;
  int ns, sink;

  int extrastates = Mr->ns; //duplicate states for each sharp pair

  //for out going information in Mr
  char ***binOfOut = (char ***) malloc((Mr->ns)*sizeof(char **)); //the string of the nonsink outgoing edge of each state
  int **toOfOut = (int **) malloc((Mr->ns)*sizeof(int *)); // the destination of the nonsink outgoing edge of each state
  int *numOfOut = (int *) malloc((Mr->ns)*sizeof(int)); // how many nonsink outgoing edges of each state
  int *numOfOutFinal = (int *) malloc((Mr->ns)*sizeof(int)); //how many final outgoing edges of each state


  initial_out_info(Mr, numOfOut, numOfOutFinal, binOfOut, toOfOut, var, 1, indices);


  max_exeps=1<<len; //maybe exponential
  sink=find_sink(M);
  assert(sink >-1);
  ns = M->ns + (M->ns)*(extrastates);

  dfaSetup(ns, len, indices);
  exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
  to_states=(int *)malloc(max_exeps*sizeof(int));
  statuces=(char *)malloc((ns+1)*sizeof(char));
  auxexeps=(char *)malloc((len+1)*sizeof(char));


  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;
    // add original paths
    while (pp) {
      if(pp->to!=sink){
	  to_states[k]=pp->to;
	  for (j = 0; j < var; j++) {
	    //the following for loop can be avoided if the indices are in order
	    for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);

	    if (tp) {
	      if (tp->value) exeps[k*(len+1)+j]='1';
	      else exeps[k*(len+1)+j]='0';
	    }
	    else
	      exeps[k*(len+1)+j]='X';
	  }
	  for (j = var; j < len; j++) {
	    exeps[k*(len+1)+j]='0'; //all original paths are set to zero
	  }
	  exeps[k*(len+1)+len]='\0';
	  k++;

      }
      pp = pp->next;
    }//end while

    //inser Mr

    for(o=0; o<numOfOut[Mr->s]; o++){
      to_states[k]=M->ns+i*(extrastates)+toOfOut[Mr->s][o]; // go to the next state of intial state of  Mr
      for(j = 0; j < var; j++) exeps[k*(len+1)+j]=binOfOut[Mr->s][o][j];
      exeps[k*(len+1)+j]='1'; //to distinguish the original path
      exeps[k*(len+1)+len]='\0';
      k++;
    }


    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink);

    if(M->f[i]==1)
      statuces[i]='+';
    else if(M->f[i]==-1)
      statuces[i]='-';
    else
      statuces[i]='-';

    kill_paths(state_paths);
  }//end for i

  assert(i==M->ns);

  //Add replace states
  for(n=0; n< M->ns; n++){
    for(i=0; i<Mr->ns; i++){ //internal M (exclude the first and the last char)
      if(numOfOutFinal[i]==0){
	dfaAllocExceptions(numOfOut[i]);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	}
	dfaStoreState(sink);
      }else{//need to add aux edges back to sharp destination, for each edge leads to accepting state
	dfaAllocExceptions(numOfOut[i]+numOfOutFinal[i]);
	for(o =0; o<numOfOut[i]; o++){
	  dfaStoreException(M->ns+n*(extrastates)+toOfOut[i][o], binOfOut[i][o]);
	  if(Mr->f[toOfOut[i][o]]==1){ //add auxiliary back edge to n
	    for (j = 0; j < var; j++) auxexeps[j]=binOfOut[i][o][j];
	    auxexeps[j]='1';
	    auxexeps[len]='\0';
	    dfaStoreException(n,auxexeps);
	  }
	}
	dfaStoreState(sink);
      }
    }//end for Mr internal
  }//end for n

  for(i=M->ns; i<ns; i++) statuces[i]='-';

  statuces[ns]='\0';
  result=dfaBuild(statuces);


  if(_FANG_DFA_DEBUG){
    printf("Project the %d bit\n", i);
    printf("Original:%d", i);
    dfaPrintVitals(result);
  }

  // dfaPrintVerbose(dfaMinimize(result));

  tmpM =dfaProject(dfaMinimize(result), (unsigned) len-1);
  //dfaPrintVerbose(tmpM);

  if(_FANG_DFA_DEBUG){
    printf("Projected:%d bit", len-1);
    dfaPrintVitals(tmpM);
  }
  dfaFree(result);
  result = dfaMinimize(tmpM);
  dfaFree(tmpM);
  if(_FANG_DFA_DEBUG){
    printf("Minimized:after %d bit", len-1);
    dfaPrintVitals(result);
  }

  free(exeps);
  free(auxexeps);
  free(to_states);
  free(statuces);


  for(i=0; i<Mr->ns; i++){
    if(binOfOut[i]!=NULL) free(binOfOut[i]);
    if(toOfOut[i]!=NULL) free(toOfOut[i]);
  }


  free(binOfOut);
  free(toOfOut);

  free(numOfOut);
  free(numOfOutFinal);

  return dfaMinimize(result);

}//End dfa_insert_M_arbitrary



DFA *dfa_insert_everywhere(DFA *M, DFA* Mr, int var, int *indices)
{
  DFA *result1 = NULL;
  DFA *result2 = NULL;
  DFA *result = NULL;
  DFA *tmp = NULL;


  tmp = dfa_intersect(Mr, dfaDot(var, indices));
  if(!check_emptiness(tmp, var, indices)){
    result = dfa_insert_M_dot(M, tmp, var, indices);
  }

  dfaFree(tmp);
  tmp = dfa_intersect(Mr, dfaSigmaC1toC2(2, -1, var, indices));

  if(!check_emptiness(tmp, var, indices)){
    //replace rest rather than single character
    result2 = dfa_insert_M_arbitrary(M, tmp, var, indices);
   if(result){
     result1 = result;
     result = dfa_union(result1, result2);
     dfaFree(result1);
     dfaFree(result2);
   }
   else result = result2;
  }
  dfaFree(tmp);
  return result;
} //END dfa_insert_everywhere



