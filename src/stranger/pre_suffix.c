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

/*********************************************

Functions for Composite Verification on Strings and Integers

Fang 06/30/2008

1) Prefix(DFA M, c_1, c_2)  Output M' so that L(M')={w| w'\in \Sigma*, ww' \in L(M), |w|<c_2 }
2) Suffix(DFA M, c_1, c_2)  Output M' so that L(M')={w| w'\in \Sigma^{c_1}, w'w \in L(M) }
3) Minimal(DFA M)
4) Maximal(DFA M)

**********************************************/



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

// A DFA that accepts everything within the length from c1 to c2
//c2 = -1, indicates unbounded upperbound
//c1 = -1, indicates unbounded lowerbound
DFA *dfaSigmaC1toC2(int c1, int c2, int var, int* indices){

  int i, n;
  char *statuces;
  DFA *result=NULL;

  if(c2<=-1){ //accept everything after c1 steps

    n=c1+1;
    statuces=(char *)malloc((n+1)*sizeof(char));
    dfaSetup(n,var,indices);
    //the 0 to c1-1 states(unaccepted)
    for( i=0; i<c1; i++){
      dfaAllocExceptions(0);
      dfaStoreState(i+1);
      statuces[i]='-';
    }
    //the c1 state
    dfaAllocExceptions(0);
    dfaStoreState(i);
    statuces[i]='+'; //i==c1
    statuces[n]='\0'; //n==c1+1

  }else if(c1<=-1){

    n=c2+2; //add one sink state
    statuces=(char *)malloc((n+1)*sizeof(char));
    dfaSetup(n,var,indices);
    //the 0 to c2 states(accepted)
    for( i=0; i<=c2; i++){
      dfaAllocExceptions(0);
      dfaStoreState(i+1);
      statuces[i]='+';
    }
    //the c1 state
    dfaAllocExceptions(0);
    dfaStoreState(i);
    statuces[i]='-'; //i==c2
    statuces[n]='\0'; //n==c1+1

  } else {

    assert(c2>=c1);
    n=c2+2; //add one sink state
    statuces=(char *)malloc((n+1)*sizeof(char));
    dfaSetup(n,var,indices);
    //the 0 to c2 states(accepted)
    for( i=0; i<=c2; i++){
      dfaAllocExceptions(0);
      dfaStoreState(i+1);
      if(i>=c1) statuces[i]='+';
      else statuces[i]='-';
    }
    //the c1 state
    dfaAllocExceptions(0);
    dfaStoreState(i);
    statuces[i]='-'; //i==c2
    statuces[n]='\0'; //n==c1+1
  }


  result=dfaBuild(statuces);
  //dfaPrintVerbose(result);
  free(statuces);
  if(c1==0) result->f[result->s]=1;
    DFA *tmp = dfaMinimize(result);
    dfaFree(result);
  return tmp;

}


DFA *dfa_Prefix(DFA *M, int c1, int c2, int var, int* indices) //Output M' so that L(M')={w| w'\in \Sigma*, ww' \in L(M), c_1 <= |w|<=c_2 }
{
  int i, sink;
  DFA *M1 = dfaSigmaC1toC2(c1, c2, var, indices);
  DFA *M2 = dfaCopy(M);
  //dfaPrintVerbose(M2);
  sink = find_sink(M);
  for(i=0; i<M2->ns; i++){
    if(i!= sink) M2->f[i]=1;
  }
  //dfaPrintVerbose(M2);
  DFA *result = dfa_intersect(M2, M1);
  //dfaPrintVerbose(result);
  dfaFree(M1);
  dfaFree(M2);
  return dfaMinimize(result);

}//end of prefix




struct int_list_type *reachable_states_bounded_steps(DFA *M, int c1, int c2){

  paths state_paths, pp;
  int current;
  int steps;
  int sink = find_sink(M);

  struct int_list_type *worklist=NULL;
  struct int_list_type *nextlist=NULL;
  struct int_list_type *finallist = new_ilt();

  worklist = enqueue(worklist, M->s);

  for(steps=1; steps <=c2; steps++){
    while(worklist->count>0){
      current = dequeue(worklist); //dequeue returns the int value instead of the struct
      state_paths = pp = make_paths(M->bddm, M->q[current]);
      while (pp) {
	if(pp->to != sink){
	  nextlist=enqueue(nextlist, pp->to);
	  if(steps >= c1) finallist = enqueue(finallist, pp->to);
	}
	pp = pp->next;
      }
    }
    if(!nextlist) break;
    free(worklist);
    worklist = nextlist;
    nextlist = NULL;
  }

  //print_ilt(finallist);
  return finallist;
}

/**
 * Muath documentation:
 * returns 1 (true) if s1 != lambda
 * end Muath documentation
 */
int isNotExactEqual2Lambda(char *s1, char *lambda, int var){
	int i;
	for(i=0; i<var; i++)
		if(s1[i]!=lambda[i]) return 1;
	return 0;
}

/**
 * Muath documentation:
 * returns 1 (true) if there is a transition out of state 'state' not equal to lambda
 * end Muath documentation
 */
int isOtherLambdaOut(DFA* M, char* lambda, int state, int var){

	char* symbol;
	paths state_paths, pp;
	trace_descr tp;
	int j, sink;

    sink = find_sink(M);
    assert(sink >= 0);
    
	symbol = (char *) malloc((var + 1) * sizeof(char));
	state_paths = pp = make_paths(M->bddm, M->q[state]);

	while (pp) {
		if (pp->to != sink) {
			for (j = 0, tp = pp->trace; j < var && tp; j++, tp = tp->next) {
				if (tp) {
					if (tp->value)
						symbol[j] = '1';
					else
						symbol[j] = '0';
				} else
					symbol[j] = 'X';
			}
			symbol[j] = '\0';
			if (isNotExactEqual2Lambda(symbol, lambda, var))
				return 1;
		}
		pp = pp->next;
	} //end while
	return 0;
}

/**
 * Muath documentation:
 * returns a list of states containing each state s that has at least one transition on lambda
 * into it and one transition on non-lambda out of it (except for sink state which is ignored)
 * end Muath documentation
 */
struct int_list_type *reachable_states_lambda_in_nout(DFA *M, char *lambda, int var){

	paths state_paths, pp;
	trace_descr tp;
	int j, current;
	int sink = find_sink(M);
	char *symbol;
	struct int_list_type *finallist=NULL;
	if(_FANG_DFA_DEBUG)dfaPrintVerbose(M);
	symbol=(char *)malloc((var+1)*sizeof(char));
	for(current=0; current<M->ns; current++){
		state_paths = pp = make_paths(M->bddm, M->q[current]);
		while (pp) {
			if(pp->to != sink){
				// construct transition from current to pp->to and store it in symbol
				for (j = 0, tp = pp->trace; j < var && tp; j++, tp = tp->next) {
					if (tp) {
						if (tp->value) symbol[j]='1';
						else symbol[j]='0';
					}
					else
						symbol[j]='X';
				}
				symbol[j]='\0';
				// if transition from current state to pp->to state is on labmda
				if(isEqual2Lambda(symbol, lambda, var)){
					// if there is a transition out of pp->to state on non-lambda then add pp->to to returned list
					if(isOtherLambdaOut(M, lambda, (pp->to), var)) finallist = enqueue(finallist, pp->to);
				}
			}
			pp = pp->next;
		}
	}

	if(_FANG_DFA_DEBUG) print_ilt(finallist);
	free(symbol);
	return finallist;
}



int check_accept(DFA *M, struct int_list_type *states){

  int i;
  struct int_type *tmpState=states->head;
  assert(states != NULL);
  for(i = 0; i< states->count; i++){
    if(tmpState!=NULL)
      if(M->f[tmpState->value]>0) return 1;
  }
  return 0;
}


DFA *dfa_Suffix(DFA *M, int c1, int c2, int var, int *oldindices)
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

  int i, j, z, k;

  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len=var;
  int sink;

  char *auxbit=NULL;


  //	char *apath =bintostr(a, var);
  states = reachable_states_bounded_steps(M, c1, c2);
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
  for (z=1; z<=states->count; z++) {
    state_paths = pp = make_paths(M->bddm, M->q[tmpState->value]);
    while (pp) {
      if(pp->to!=sink){
	to_states[k]=pp->to+1; //insert itself as the initial state
	for (j = 0; j < var; j++) {
	  //the following for loop can be avoided if the indices are in order
	  for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);
	  if (tp) {
	    if (tp->value) exeps[k*(len+1)+j]='1';
	    else exeps[k*(len+1)+j]='0';
	  }else{
	    exeps[k*(len+1)+j]='X';
	  }
	}
	set_bitvalue(auxbit, aux, z); // aux = 3, z=4, auxbit 001
	for (j = var; j < len; j++) { //set to xxxxxxxx100
	  exeps[k*(len+1)+j]=auxbit[len-j-1];
	}
	exeps[k*(len+1)+len]='\0';
	k++;
      }
      pp = pp->next;
    }//end while
    kill_paths(state_paths);
    tmpState = tmpState->next;
  } //end for

  dfaAllocExceptions(k);
  for(k--;k>=0;k--)
    dfaStoreException(to_states[k],exeps+k*(len+1));
  dfaStoreState(sink+1);

  if(check_accept(M, states))	statuces[0]='+';
  else 	statuces[0]='0';



  //for the rest of states (shift one state)
  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k=0;

    while (pp) {
      if(pp->to!=sink){
	for (tp = pp->trace; tp && (tp->index != indices[var]); tp =tp->next); //find the bar value
	if (!tp || !(tp->value)) {
	  to_states[k]=pp->to+1;
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

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink+1);

    if(M->f[i]==1)
      statuces[i+1]='+';
    else if(M->f[i]==-1)
      statuces[i+1]='-';
    else
      statuces[i+1]='0';

    kill_paths(state_paths);
  }

  statuces[M->ns+1]='\0';
  result=dfaBuild(statuces);
  //	dfaPrintVerbose(result);
  for(i=0; i<aux; i++){
    j=len-i-1;
    tmpM =dfaProject(result, (unsigned) j);
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
