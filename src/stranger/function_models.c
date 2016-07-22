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
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <limits.h>
#include "utility.h"


/*=====================================================================*/
/* Data structure for transition relation matrix
*/

void removeTransitionOnChar(char* transitions, char* charachter, int var, char** result, int* pSize);


struct transition_type{
	int from;
	int to;
	struct transition_type	*next;
};

struct transition_list_type{
	int count;
	struct	transition_type	*head;
	struct	transition_type	*tail;
};

struct transition_type *transition_new_it(int from, int to) {
	struct transition_type *tmp;
	tmp = (struct transition_type *) malloc(sizeof(struct transition_type));
	tmp->from = from;
	tmp->to = to;
	tmp->next = NULL;
	return tmp;
}

struct transition_list_type *transition_new_ilt() {
	struct transition_list_type *tmp;
	tmp = (struct transition_list_type *) malloc(sizeof(struct transition_list_type));
	tmp->count = 0;
	tmp->head = tmp->tail = NULL;
	return tmp;
}

struct transition_list_type *transition_add_data(struct transition_list_type *list, struct transition_type *data)
{
	if (data == NULL)
		return list;

	if (list == NULL)
		list = transition_new_ilt();
	if (list->count > 0) {
		list->tail->next = data;
		list->tail = list->tail->next;
		list->count++;
	} else {
		list->head = list->tail = data;
		list->count = 1;
	}
	return list;
}

int transition_check_value(list, from, to)
	struct transition_list_type *list;int from; int to; {
	struct transition_type *tmp = NULL;
	if (list != NULL)
		for (tmp = list->head; tmp != NULL; tmp = tmp->next)
			if (tmp->from == from && tmp->to == to)
				return 1;
	return 0;
}

struct transition_list_type *transition_remove_value(struct transition_list_type *list, int from, int to)
{
	struct transition_type *tmp = NULL;
	struct transition_type *del = NULL;
	if (transition_check_value(list, from, to) > 0) {
		for (tmp = list->head; tmp != NULL; tmp = tmp->next)
			if ((tmp->from == from && tmp->to == to) && (list->count == 1)) { //remove tmp
				list->count = 0;
				list->head = list->tail = NULL;
				free(tmp);
				return list;
			} else if ((tmp->from == from && tmp->to == to) && (list->head == tmp)) {
				list->count--;
				list->head = list->head->next;
				free(tmp);
				return list;
			} else if ((tmp->next != NULL) && (tmp->next->from == from && tmp->next->to == to)) {
				if (tmp->next->next == NULL) { //remove tail
					list->count--;
					list->tail = tmp;
					list->tail->next = NULL;
					free(tmp->next);
					return list;
				} else {
					list->count--;
					del = tmp->next;
					tmp->next = tmp->next->next;
					free(del);
					return list;
				}
			}
	}
	return list;
}

int transition_check_data(list, data)
	struct transition_list_type *list;struct transition_type *data; {
	struct transition_type *tmp = NULL;
	if ((list != NULL) && (data != NULL))
		for (tmp = list->head; tmp != NULL; tmp = tmp->next)
			if (tmp->from == data->from && tmp->to == data->to)
				return 1;
	return 0;
}


//no duplicate
struct transition_list_type *transition_enqueue(struct transition_list_type *list, int from, int to)
{
	if (!transition_check_value(list, from, to))
		list = transition_add_data(list, transition_new_it(from, to));
	return list;
}

struct transition_type *transition_dequeue(struct transition_list_type *list)
{
	struct transition_type *data = NULL;
	struct transition_type *i = NULL;
	if ((list == NULL) || (list->count == 0))
		return NULL;
	else
		data = list->head;
	if (list->count == 1) {
		list->count = 0;
		list->head = list->tail = NULL;
	} else {
		list->head = list->head->next;
		list->count--;
	}
	i = data;
	free(data);
	return i;
}

void transition_free_ilt(struct transition_list_type *list) {
	struct transition_type *tmp = transition_dequeue(list);
	while (tmp != NULL)
		tmp = transition_dequeue(list);
	free(list);
}

void transition_print_ilt(struct transition_list_type *list) {
	if (list == NULL){
		printf("list is empty.\n");
		return;
	}
	struct transition_type *tmp = list->head;
	while (tmp != NULL) {
		printf("-> from: %d, to:%d", tmp->from, tmp->to);
		tmp = tmp->next;
	}
}

/*
DFA *dfaPreRightTrim(DFA *M, char c, int var, int *oldIndices) {
	DFA *result;
	paths state_paths, pp;
	trace_descr tp;
	int i, j, k;
	char *exeps;
	int *to_states;
	int sink;
	long max_exeps;
	char *statuces;
	int len;
	int ns = M->ns;
	int *indices;
	char* lambda = bintostr(c, var);

	len = var + 1;
	max_exeps = 1 << len; //maybe exponential
	sink = find_sink(M);
	assert(sink>-1);

	indices = allocateArbitraryIndex(len);

	char* symbol = (char *) malloc((len + 1) * sizeof(char));//len+1 since we need extra bit
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((ns + 1) * sizeof(char));

	strcpy(symbol, lambda); symbol[var] = '1'; symbol[len] = '\0';


	dfaSetup(ns, len, indices);
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
		while (pp) {
			if (pp->to != sink) {
				to_states[k] = pp->to;
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp
							= tp->next)
						;
					if (tp) {
						if (tp->value)
							exeps[k * (len + 1) + j] = '1';
						else
							exeps[k * (len + 1) + j] = '0';
					} else
						exeps[k * (len + 1) + j] = 'X';
				}
				exeps[k * (len + 1) + j] = '0';// for init state extrabit 1 goes to self loop for lambda. Everthing else goes to sink
				exeps[k * (len + 1) + len] = '\0';// if no extrabit will overwrite assign in prev line
				k++;
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		// if accept state create a self loop on lambda
		if (M->f[i] == 1){
			dfaAllocExceptions(k+1);
			dfaStoreException(i, symbol);
		}
		else
			dfaAllocExceptions(k);

		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink);

		if (M->f[i] == -1)
			statuces[i] = '-';
		else if (M->f[i] == 1)
			statuces[i] = '+';
		else
			statuces[i] = '-';// DO NOT USE don't care
	}

	statuces[ns] = '\0';
	DFA* tmpM = dfaBuild(statuces);
	result = dfaProject(tmpM, ((unsigned)var));
	dfaFree(tmpM); tmpM = NULL;
	tmpM = dfaMinimize(result);
	dfaFree(result);result = NULL;

	free(exeps);
	free(symbol);
	free(lambda);
	free(to_states);
	free(statuces);
	free(indices);

	return tmpM;
}
*/

/*
DFA *dfaPreLeftTrim(DFA *M, char c, int var, int *oldIndices) {
	DFA *result;
	paths state_paths, pp;
	trace_descr tp;
	int i, j, k;
	char *exeps;
	int *to_states;
	int sink;
	long max_exeps;
	char *statuces;
	int len;
	int ns = M->ns;
	int *indices;
	char* lambda = bintostr(c, var);
	boolean extraBitNeeded = FALSE;


	sink = find_sink(M);
	assert(sink>-1);
	//printf("\n\n SINK %d\n\n\n", sink);

	char* symbol = (char *) malloc((var + 2) * sizeof(char));//var+2 since we may need extra bit
	//construct the added paths for the initial state
	state_paths = pp = make_paths(M->bddm, M->q[M->s]);
	//printf("\n\n INIT %d \n\n", M1->s);

	while (pp) {
		if (pp->to != sink) {
			for (j = 0; j < var; j++) {
				//the following for loop can be avoided if the indices are in order
				for (tp = pp->trace; tp && (tp->index != oldIndices[j]); tp
						= tp->next)
					;
				if (tp) {
					if (tp->value)
						symbol[j] = '1';
					else
						symbol[j] = '0';
				} else
					symbol[j] = 'X';
			}
			symbol[j] = '\0';
			if (isIncludeLambda(symbol, lambda, var)){
				if (pp->to == M->q[M->s]){
					result = dfaCopy(M);
					kill_paths(state_paths);
					free(symbol);
					free(lambda);
					return result;
				}
				else{
					extraBitNeeded = TRUE;
					break;
				}
			}
		}
		pp = pp->next;
	}
	kill_paths(state_paths);

	len = extraBitNeeded? var + 1: var;
	indices = extraBitNeeded? allocateArbitraryIndex(len) : oldIndices;
	max_exeps = 1 << len; //maybe exponential
	dfaSetup(ns, len, indices);
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((ns + 1) * sizeof(char));


	for (i = 0; i < M->ns; i++) {
		//construct the added paths for the initial state
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		//printf("\n\n INIT %d \n\n", M1->s);

		k = 0;
		while (pp) {
			if (pp->to != sink) {
				to_states[k] = pp->to;
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp
							= tp->next)
						;
					if (tp) {
						if (tp->value)
							exeps[k * (len + 1) + j] = '1';
						else
							exeps[k * (len + 1) + j] = '0';
					} else
						exeps[k * (len + 1) + j] = 'X';
				}
				exeps[k * (len + 1) + j] = '0';// for init state extrabit 1 goes to self loop for lambda. Everthing else goes to sink
				exeps[k * (len + 1) + len] = '\0';// if no extrabit will overwrite assign in prev line
				k++;
			}
			pp = pp->next;
		}
		kill_paths(state_paths);

		if (i == M->s){
			strcpy(symbol, lambda);
			if (extraBitNeeded){
				symbol[var] = '1';
				symbol[len] = '\0';
			}
			dfaAllocExceptions(k+1);
			dfaStoreException(M->s, symbol);
		}
		else
			dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink);

		if (M->f[i] == -1)
			statuces[i] = '-';
		else if (M->f[i] == 1)
			statuces[i] = '+';
		else
			statuces[i] = '0';
	}

	statuces[ns] = '\0';
	DFA* tmpM = dfaBuild(statuces);


	free(exeps);
	free(symbol);
	free(to_states);
	free(statuces);
	free(lambda);


	if (extraBitNeeded){
		free(indices);
		result = dfaProject(tmpM, ((unsigned)var));
		dfaFree(tmpM); tmpM = NULL;
		tmpM = dfaMinimize(result);
		dfaFree(result);result = NULL;
		return tmpM;
	}
	else
	{
		result = dfaMinimize(tmpM);
		dfaFree(tmpM);tmpM = NULL;
		return result;
	}
}
*/
struct transition_list_type *getTransitionRelationMatrix(DFA* M, char *lambda,
		int var, int* indices) {
	paths state_paths, pp;
	trace_descr tp;
	int j;
	int sink = find_sink(M);
	char *symbol = (char *) malloc((var+1)*sizeof(char));
	struct transition_list_type *finallist = NULL;
	int i;
	for (i = 0; i < M->ns; i++) {

		state_paths = pp = make_paths(M->bddm, M->q[i]);

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
				symbol[j] = '\0';
				if (isIncludeLambda(symbol, lambda, var)) {
					finallist = transition_enqueue(finallist, i, pp->to);
				}

			}
			pp = pp->next;
		} //end while

		kill_paths(state_paths);
	}

//	printf("list of states reachable on \\s:");
//	transition_print_ilt(finallist);
//	printf("\n");

	free(symbol);
	return finallist;
}

struct int_list_type * findReversePathsOnLambda(struct transition_list_type *transition_relation, struct int_list_type *finallist, int current_state){
	finallist = enqueue(finallist, current_state);
	struct transition_type *tmp2;
	// for all transition relation on lambda
	for (tmp2 = transition_relation->head; tmp2 != NULL; tmp2 = tmp2->next) {
		// if current transition has current state as destination then follow transition in reverse if has not been followed before
		if ((current_state == tmp2->to) && (!check_value(finallist, tmp2->from))){
			finallist = findReversePathsOnLambda(transition_relation, finallist, tmp2->from);
		}
	}
	return finallist;

}

struct int_list_type *states_reach_accept_lambda(DFA* M, char* lambda, int var, int* indices){

	struct transition_list_type *transition_relation = getTransitionRelationMatrix(M, lambda, var, indices);
	if (transition_relation == NULL)
		return NULL;
	struct int_list_type *finallist=NULL;

	// for each accepting state get list that reach the accepting state on lambda

	struct transition_type *tmp = transition_relation->head;
	while (tmp != NULL) {
		// for each accept state
		if (M->f[tmp->to] == 1){
			// if accept state has not been processed before
			if (!check_value(finallist, tmp->to)){
				finallist = findReversePathsOnLambda(transition_relation, finallist, tmp->to);
			}
		}
		tmp = tmp->next;
	}


	// free unneeded memory
	transition_free_ilt(transition_relation);
//	printf("states that reach an accepting state on lambda: ");
//	print_ilt(finallist);
//	printf("\n");
	return finallist;
}

DFA *dfaRightTrim(DFA *M, char c, int var, int *oldindices) {
	DFA *result = NULL;
	DFA *tmpM = NULL;
	char* lambda = bintostr(c, var);
	int aux = 1;
	struct int_list_type *states = NULL;

	int maxCount = 0;

	int *indices = oldindices; //indices is updated if you need to add auxiliary bits

	paths state_paths, pp;
	trace_descr tp;

	int i, j, z, k;

	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int len = var;
	int sink, new_accept_state;
	boolean split_char;

	int numOfChars;
	char** charachters;
	int size;

	char *symbol;


	states = states_reach_accept_lambda(M, lambda, var, indices);
	if (states == NULL ){
		free(lambda);
		return dfaCopy(M);
	}

	symbol = (char *) malloc((var + 1) * sizeof(char));
	maxCount = states->count;

	if (maxCount > 0) { //Need auxiliary bits when there exist some outgoing edges
		aux = 1;
		len = var + aux; // extra aux bits
		indices = allocateArbitraryIndex(len);
	}

	max_exeps = 1 << len; //maybe exponential
	sink = find_sink(M);
	assert(sink > -1);
	new_accept_state = M->ns;

	numOfChars = 1 << var;
	charachters = (char**) malloc(numOfChars * (sizeof(char*)));

	//pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i

	dfaSetup(M->ns + 1, len, indices); //add one new accept state
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((M->ns + 2) * sizeof(char)); //plus 2, one for the new accept state and one for \0 end of the string

	// for each original state
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
		// for each transition out from current state (state i)
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
				symbol[var] = '\0';
				// first copy to original destination without removing lambda
				to_states[k] = pp->to;
				for (j = 0; j < var; j++)
					exeps[k * (len + 1) + j] = symbol[j];
				exeps[k * (len + 1) + var] = '0';
				exeps[k * (len + 1) + len] = '\0';
				k++;

				split_char = check_value(states, pp->to);
				if (split_char == TRUE) {
					// second copy to new accept state after removing lambda
					if (!isIncludeLambda(symbol, lambda, var)) {
						// no lambda send as it is
						to_states[k] = new_accept_state; // destination new accept state
						for (j = 0; j < var; j++)
							exeps[k * (len + 1) + j] = symbol[j];
						exeps[k * (len + 1) + var] = '1';
						exeps[k * (len + 1) + len] = '\0';
						k++;
					} else {
						// remove lambda then send copy to new accept state
						removeTransitionOnChar(symbol, lambda, var, charachters,
								&size);
						for (z = 0; z < size; z++) {
							// first copy of non-bamda char to original destination
//							printf("%s, ", charachters[z]);
							to_states[k] = new_accept_state; // destination new accept state
							for (j = 0; j < var; j++)
								exeps[k * (len + 1) + j] = charachters[z][j];
							exeps[k * (len + 1) + var] = '1';
							exeps[k * (len + 1) + len] = '\0';
							k++;
							free(charachters[z]);
						}
//						printf("\n");
					}
				}
			}
			pp = pp->next;
		} //end while

		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink);
		statuces[i] = '-';

		kill_paths(state_paths);
	} // end for each original state

	// add new accept state
	dfaAllocExceptions(0);
	dfaStoreState(sink);
	statuces[new_accept_state] = '+';

	statuces[M->ns + 1] = '\0';
	result = dfaBuild(statuces);
//	printf("dfaAfterRightTrimBeforeMinimize\n");
//	dfaPrintGraphviz(result, len, indices);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : right_trim : states %d : bddnodes %u : before projection \n", result->ns, bdd_size(result->bddm) );
	j = len - 1;
	tmpM = dfaProject(result, (unsigned) j);
	dfaFree(result);result = NULL;
	if( DEBUG_SIZE_INFO )
		printf("\t peak : right_trim : states %d : bddnodes %u : after projection \n", tmpM->ns, bdd_size(tmpM->bddm) );
	result = dfaMinimize(tmpM);
	dfaFree(tmpM);tmpM = NULL;

	// if original accept epsilon or start state reaches an accept state on lambda (\s+ is an element of L(M))
    //then add epsilon to language
	if (M->f[M->s] == 1 || check_value(states, M->s)){
		tmpM = dfa_union_empty_M(result, var, indices);
		dfaFree(result); result = NULL;
		result = tmpM;
	}
	free(exeps);
	//printf("FREE ToState\n");
	free(to_states);
	//printf("FREE STATUCES\n");
	free(statuces);
	free(charachters);

	free_ilt(states);
	free(lambda);

    free(symbol);
    if (maxCount > 0) free(indices);
    
	return result;

}


DFA *dfaPreRightTrim(DFA *M, char c, int var, int *oldIndices)
{
    DFA *result = NULL;
    DFA *tmpM = NULL;
    char* lambda = bintostr(c, var);
    int *indices = oldIndices; //indices is updated if you need to add auxiliary bits
    
    paths state_paths, pp;
    trace_descr tp;
    
    int i, j, k, z;
    
    char *exeps;
    int *to_states;
    long max_exeps;
    char *statuces;
    int len;
    int sink;
    
    int size = 0;
    int numOfChars;
    char** charachters;
    
    char *symbol;
    
    sink=find_sink(M);
    assert(sink >-1);
    
    symbol=(char *)malloc((var+1)*sizeof(char));
    
    /**************************************************
     *   Add a new start state with space self loop   *
     **************************************************/
    
    
	len = var + 1;
	indices = allocateArbitraryIndex(len);
    
    
    max_exeps=1<<len; //maybe exponential
    
    
    numOfChars = 1<<var;
    charachters = (char**) malloc(numOfChars * (sizeof (char*)));
    
    
    unsigned shift = 0;
    if (M->f[M->s] == 1){
        //if start state is accepting then
        //one new start state and one new accept state
        dfaSetup(M->ns+2, len, indices); //add one new initial state as start state
        shift = 1;
        statuces=(char *)malloc((M->ns+3)*sizeof(char));//two states + null
    }
    else {
        dfaSetup(M->ns+1, len, indices); //add one new initial state as start state
        shift = 0;
        statuces=(char *)malloc((M->ns+2)*sizeof(char));//1 state + null
    }
    unsigned newStart = 0;
    unsigned newAcceptState = M->ns + shift;

    exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char)); //plus 1 for \0 end of the string
    to_states=(int *)malloc(max_exeps*sizeof(int));
    
    
    //printf("Before Replace Char\n");
    //dfaPrintVerbose(M);
    
    //if start state is an accept state then add a new start state
    //Reason: since original start is accepting then
    //preimage may have \s* that is removed by right
    //trim. Example: rightTrim(\s*(ab)*)= (ab)*|\s*(ab)+
    if (M->f[M->s] == 1){
        //construct the added paths for the initial state
        state_paths = pp = make_paths(M->bddm, M->q[M->s]);
        //printf("\n\n INIT %d \n\n", M1->s);
        k=0;
        
        /******    Copy transitions from original start state to new one  ********/
        //reset pp
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
            
                //case -1- copying a transition from old start to a state that is not accepting
                //Transition may have lambda on them
                if (M->f[pp->to] != 1){
                    //if start state does not go to and accept state
                    
                    //start state will have lambde on a self cycle so take care of lambda to other states
                    if (!isIncludeLambda(symbol, lambda, var)) { // Only Consider Non-lambda case
                        to_states[k] = pp->to + shift;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = symbol[j];
#if MORE_WORDS_LESS_NDTRANS == 1
                        exeps[k * (len + 1) + j] = 'X';//<-- only if len > var this will matter
#else
                        exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
#endif
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
                    }
                    else {
#if MORE_WORDS_LESS_NDTRANS == 1
                        removeTransitionOnChar(symbol, lambda, var, charachters, &size);
                        for (i = 0; i < size; i++)
                        {
                            //						printf("%s, ", charachters[i]);
                            to_states[k] = pp->to + shift;
                            for (j = 0; j < var; j++)
                                exeps[k * (len + 1) + j] = charachters[i][j];
                            exeps[k * (len + 1) + j] = 'X';//<-- only if len > var this will matter
                            exeps[k * (len + 1) + len] = '\0';
                            free(charachters[i]);
                            k++;
                        }
                        //					printf("\n");
                        to_states[k] = pp->to + shift;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = lambda[j];
                        exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
#else
                        to_states[k] = pp->to + shift;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = symbol[j];
                        exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
#endif
                    }
                }
                else {
                    //copy -1- to original accept state
                    to_states[k] = pp->to + shift;
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = symbol[j];
                    exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                    //copy -2- to new accept state. Do not copy lambda transitions (reason is complex but true)
                    if (!isIncludeLambda(symbol, lambda, var)) { // Only Consider Non-lambda case
                        //copy -2- to new accept state no lambda deletion
                        to_states[k] = newAcceptState;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = symbol[j];
                        exeps[k * (len + 1) + j] = '1';//<-- only if len > var this will matter
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
                    }
                    else {
                        //copy -2- to new accept state with lambda deletion
                        removeTransitionOnChar(symbol, lambda, var, charachters, &size);
                        for (i = 0; i < size; i++)
                        {
                            //						printf("%s, ", charachters[i]);
                            to_states[k] = newAcceptState;
                            for (j = 0; j < var; j++)
                                exeps[k * (len + 1) + j] = charachters[i][j];
                            exeps[k * (len + 1) + j] = '1';//<-- only if len > var this will matter
                            exeps[k * (len + 1) + len] = '\0';
                            free(charachters[i]);
                            k++;
                        }
                        //					printf("\n");
                    }
                }
            } //end if
            pp = pp->next;
        } //end while
        kill_paths(state_paths);
        
        //add self cycle on lambda
        to_states[k] = newStart;
        for (j = 0; j < var; j++)
            exeps[k * (len + 1) + j] = lambda[j];
        exeps[k * (len + 1) + j] = '1';//<-- only if len > var then this is the other lambda
        exeps[k * (len + 1) + len] = '\0';
        k++;
        
        //original out trans from origianl start state + 1 for lambda self cycle
        dfaAllocExceptions(k);
        //copy out edges from original start state
        for(k--;k>=0;k--)
            dfaStoreException(to_states[k],exeps+k*(len+1));
        dfaStoreState(sink+shift);
        
        // new one should be accepting
        statuces[0]='+';
        
    }//end if start state is an accept state
    
    /**************************************************
     *   Add remaining states from old automaton      *
     **************************************************/
    
    //for the rest of states
    //1- shift one state
    //2- change accept to non accept
    //3- if a state goes to an accept state then
    //copy transition to new accept state excep
    //transitions on space
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
                //case -1- copying a transition from old start to a state that is not accepting
                //Transition may have lambda on them
                if (M->f[pp->to] != 1){
                    //start state will have lambde on a self cycle so take care of lambda to other states
                    to_states[k] = pp->to + shift;
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = symbol[j];
#if MORE_WORDS_LESS_NDTRANS == 1
                    exeps[k * (len + 1) + j] = 'X';//<-- only if len > var this will matter
#else
                    exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
#endif
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                }
                else {
                    //copy -1- to original accept state
                    to_states[k] = pp->to + shift;
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = symbol[j];
                    exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                    //copy -2- to new accept state. Do not copy lambda transitions (reason is complex but true)
                    if (!isIncludeLambda(symbol, lambda, var)) { // Only Consider Non-lambda case
                        //copy -2- to new accept state no lambda deletion
                        to_states[k] = newAcceptState;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = symbol[j];
                        exeps[k * (len + 1) + j] = '1';//<-- only if len > var this will matter
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
                    }
                    else {
                        //copy -2- to new accept state with lambda deletion
                        removeTransitionOnChar(symbol, lambda, var, charachters, &size);
                        for (z = 0; z < size; z++)
                        {
                            //						printf("%s, ", charachters[i]);
                            to_states[k] = newAcceptState;
                            for (j = 0; j < var; j++)
                                exeps[k * (len + 1) + j] = charachters[z][j];
                            exeps[k * (len + 1) + j] = '1';//<-- only if len > var this will matter
                            exeps[k * (len + 1) + len] = '\0';
                            free(charachters[z]);
                            k++;
                        }
                        //					printf("\n");
                    }
                }                
			}
			pp = pp->next;
		} //end while
        kill_paths(state_paths);
        
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (len + 1));
		dfaStoreState(sink + shift);
        statuces[i + shift] = '-';
		
	}
    
    /*************************************************
     *       Add new accept state                    *
     *************************************************/
    
    //one transition which is a self cycle on lambda
    k = 0;
    to_states[k] = newAcceptState;
    for (j = 0; j < var; j++)
        exeps[k * (len + 1) + j] = lambda[j];
#if MORE_WORD_LESS_NDTRANS == 1
    exeps[k * (len + 1) + j] = 'X';//<-- only if len > var then this is the other lambda
#else
    exeps[k * (len + 1) + j] = '0';
#endif
    exeps[k * (len + 1) + len] = '\0';
    k++;
    
    //original out trans from origianl start state + 1 for lambda self cycle
    dfaAllocExceptions(k);
    //copy out edges from original start state
    for(k--;k>=0;k--)
        dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink+shift);
    
    // new one should be accepting
    statuces[newAcceptState]='+';

    
    /*************************************************
     *       build automaton and project             *
     *************************************************/
    
	statuces[M->ns + 1 + shift] = '\0';
	result = dfaBuild(statuces);
    
    free(exeps);
    //printf("FREE ToState\n");
    free(to_states);
    //printf("FREE STATUCES\n");
    free(statuces);
    free(charachters);
    free(lambda);
    free(symbol);
    //	printf("dfaAfterleftTrimBeforeMinimize\n");
    //	dfaPrintGraphviz(result, len, indices);
	//	dfaPrintVerbose(result);
    free(indices);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : pre_right_trim : states %d : bddnodes %u : before projection \n", result->ns, bdd_size(result->bddm) );
    tmpM = dfaProject(result, (unsigned) var);
    dfaFree(result); result = NULL;
	if( DEBUG_SIZE_INFO )
		printf("\t peak : pre_right_trim : states %d : bddnodes %u : after projection \n", tmpM->ns, bdd_size(tmpM->bddm) );
    result = dfaMinimize(tmpM);
    dfaFree(tmpM); tmpM = NULL;
    //		printf("\n After projecting away %d bits", j);
    //		dfaPrintVerbose(result);
	
    
    return result;
    
}

/**
 * Muath documentation:
 * returns a list of states containing each state s that has at least one transition on lambda
 * into it and one transition on non-lambda out of it (except for sink state which is ignored)
 * end Muath documentation
 */
struct int_list_type *reachable_states_lambda_in_nout1(DFA *M, char *lambda, int var, int* indices){

	paths state_paths, pp;
	trace_descr tp;
	int j, current;
	int sink = find_sink(M);
	char *symbol;
	struct int_list_type *finallist=NULL;
	if(_FANG_DFA_DEBUG)dfaPrintVerbose(M);
	symbol=(char *)malloc((var+1)*sizeof(char));
	current = 0;
	boolean keeploop = TRUE;
	while (keeploop){
		keeploop = FALSE;
		state_paths = pp = make_paths(M->bddm, M->q[current]);
		while (pp && (!keeploop)) {
			if(pp->to != sink){
				// construct transition from current to pp->to and store it in symbol
				for (j = 0; j < var; j++) {
					for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
					if (tp) {
						if (tp->value) symbol[j]='1';
						else symbol[j]='0';
					}
					else
						symbol[j]='X';

				}
				symbol[j]='\0';
				// if transition from current state to pp->to state is on labmda
				if(isIncludeLambda(symbol, lambda, var)){
					//if not added before
					if (!check_value(finallist, pp->to)){
						if (current == 0)
							finallist = enqueue(finallist, current);
						finallist = enqueue(finallist, pp->to);
						current = pp->to;
						keeploop = TRUE;
					}
				}
			}
			pp = pp->next;
		}
        kill_paths(state_paths);
	}
	if (finallist!=NULL){
//		printf("list of states reachable on \\s:");
//		print_ilt(finallist);
//		printf("\n");
	}
	free(symbol);
	return finallist;
}

void removeTransitionOnCharHelper(char** result, char* transitions, char* charachter, int* indexInResult, int currentBit, int var){
	int i;
	if (transitions[currentBit] == 'X')
	{
		transitions[currentBit] = '0';
		removeTransitionOnCharHelper(result, transitions, charachter, indexInResult, currentBit, var);
		transitions[currentBit] = '1';
		removeTransitionOnCharHelper(result, transitions, charachter, indexInResult, currentBit, var);
		transitions[currentBit] = 'X';

	}

	else if (transitions[currentBit] != charachter[currentBit])
	{
		result[*indexInResult] = (char*) malloc((var+1)*(sizeof (char)));
		for (i = 0; i < var; i++)
			result[*indexInResult][i] = transitions[i];
		result[*indexInResult][var] = '\0';
		(*indexInResult)++;
	}

	else {
			if (currentBit < (var - 1))
				removeTransitionOnCharHelper(result, transitions, charachter, indexInResult, currentBit + 1, var);
	}

}

void removeTransitionOnChar(char* transitions, char* charachter, int var, char** result, int* pSize){
	int indexInResult = 0;
	removeTransitionOnCharHelper(result, transitions, charachter, &indexInResult, 0, var);
	*pSize = indexInResult;
}

void removeTransitionOnChars(char* monaCharacter, char **charachters, int numOfChars, int var, char** result, int* pSize){
    int i, j, z;
    bool found = false;
  	int indexInResult = 0;
    int tempIndexInResult;
    
    int sizeOfTempResult = 1 << var;
    char **tempResult = (char **) mem_alloc(sizeOfTempResult * sizeof(char *));
    mem_zero(tempResult, sizeOfTempResult * sizeof(char *));
    char *tempMonaCharacter = (char *) mem_alloc((var + 1) * sizeof(char));
    
    result[indexInResult] = mem_alloc( (var + 1) * sizeof(char));
    mem_zero(result[indexInResult], (var + 1) * sizeof(char));
    strcpy(result[indexInResult], monaCharacter);
    result[indexInResult][var] = '\0';
    indexInResult++;
    
    /*      For each character remove it from transition    */
    
    for (i = 0; i < numOfChars; i++) {
        found = false;
        
//        /*  1- Get the mona character to break it and remove current char to be removed */
//        /* if nothing found before then remove from original mona character */
//        if (indexInResult == 0){
//            if (isIncludeLambda(monaCharacter, charachters[i], var)){
//                strcpy(tempMonaCharacter, monaCharacter);
//                tempMonaCharacter[var] = '\0';
//                found = true;
//            }
//        }
        /* check previous result to remove from it */
//        else {
            for (j = 0; j < indexInResult; j++) {
                //if new result includes current char to be removed then remove it
                if (isIncludeLambda(result[j], charachters[i], var)) {
                    //we need to break this entry in result into multiple entries
                    //first copy it
                    strcpy(tempMonaCharacter, result[j]);
                    tempMonaCharacter[var] = '\0';
                    //then delete it
                    free(result[j]);
                    for (z = j; z < indexInResult; z++){
                        result[z] = result[z+1];
                    }
                    indexInResult--;
                    //now ready to remove
                    found = true;
                    break;
                }
            }
//        }
        
        /*  2- remove the character from mona character */
        if (found){
            tempIndexInResult = 0;
            mem_zero(tempResult, sizeOfTempResult * sizeof(char *));
            removeTransitionOnCharHelper(tempResult, tempMonaCharacter, charachters[i], &tempIndexInResult, 0, var);
            
            /*  3- copy new tempresult into result */
            for (j = 0; j < tempIndexInResult; j++){
                result[indexInResult++] = tempResult[j];
            }
        }
    }
    
    free(tempMonaCharacter);
    free(tempResult);
    
    *pSize = indexInResult;
}


DFA *dfaLeftTrim(DFA *M, char c, int var, int *oldindices)
{
  DFA *result = NULL;
  DFA *tmpM = NULL;
  char* lambda = bintostr(c, var);
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

  int numOfChars;
  char** charachters;
  int size;

  char *symbol;


  states = reachable_states_lambda_in_nout1(M, lambda, var, indices);
  if(states == NULL){
	  free(lambda);
	  return dfaCopy(M);
  }

  symbol=(char *)malloc((var+1)*sizeof(char));

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

  numOfChars = 1<<var;
  charachters = (char**) malloc(numOfChars * (sizeof (char*)));

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
				else {
					removeTransitionOnChar(symbol, lambda, var, charachters, &size);
					for (i = 0; i < size; i++)
					{
//						printf("%s, ", charachters[i]);
						to_states[k] = pp->to + 1;
						for (j = 0; j < var; j++)
							exeps[k * (len + 1) + j] = charachters[i][j];

						set_bitvalue(auxbit, aux, z); // aux = 3, z=4, auxbit 001
						for (j = var; j < len; j++) { //set to xxxxxxxx100
							exeps[k * (len + 1) + j] = auxbit[len - j - 1];
						}
						exeps[k * (len + 1) + len] = '\0';
						free(charachters[i]);
						k++;
					}
//					printf("\n");
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

  // if we can reach an accept state on lambda* then
  // accept epsilon (start state becomes an accepting state)
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

					to_states[k] = pp->to + 1;
					for (j = 0; j < var; j++)
						exeps[k * (len + 1) + j] = symbol[j];
					for (j = var; j < len; j++) { //set to xxxxxxxx100
						exeps[k * (len + 1) + j] = '0';
					}
					exeps[k * (len + 1) + len] = '\0';
					k++;

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
    
    
    free(exeps);
    //printf("FREE ToState\n");
    free(to_states);
    //printf("FREE STATUCES\n");
    free(statuces);
    free(charachters);
    free(lambda);
    free(symbol);
    
    if(maxCount>0) {
        free(indices);
        free(auxbit);
    }
    free_ilt(states);
    
    
//	printf("dfaAfterleftTrimBeforeMinimize\n");
//	dfaPrintGraphviz(result, len, indices);
	//	dfaPrintVerbose(result);
	for (i = 0; i < aux; i++) {
		j = len - i - 1;
		if( DEBUG_SIZE_INFO )
			printf("\t peak : left_trim : states %d : bddnodes %u : before projection : loop %d \n", result->ns, bdd_size(result->bddm), i );
		tmpM = dfaProject(result, (unsigned) j);
		dfaFree(result); result = NULL;
		if( DEBUG_SIZE_INFO )
			printf("\t peak : left_trim : states %d : bddnodes %u : after projection : loop %d \n", tmpM->ns, bdd_size(tmpM->bddm), i );
		result = dfaMinimize(tmpM);
		dfaFree(tmpM); tmpM = NULL;
		//		printf("\n After projecting away %d bits", j);
		//		dfaPrintVerbose(result);
	}

  return result;

}

DFA *dfaPreLeftTrim(DFA *M, char c, int var, int *oldIndices)
{
    DFA *result = NULL;
    char* lambda = bintostr(c, var);
    int *indices = oldIndices; //indices is updated if you need to add auxiliary bits
    
    paths state_paths, pp;
    trace_descr tp;
    
    int i, j, k;
    
    char *exeps;
    int *to_states;
    long max_exeps;
    char *statuces;
    int sink;
    int size = 0;
    
    
    int numOfChars;
    char** charachters;
    
    char *symbol;
    
    sink=find_sink(M);
    assert(sink >-1);
    
    symbol=(char *)malloc((var+1)*sizeof(char));
    
    /************************************************
     *          check if we need extrabit           *
     ***********************************************
    
   	//construct the added paths for the initial state
	state_paths = pp = make_paths(M->bddm, M->q[M->s]);
	//printf("\n\n INIT %d \n\n", M1->s);
    
	while (pp) {
		if (pp->to != sink) {
			for (j = 0; j < var; j++) {
				//the following for loop can be avoided if the indices are in order
				for (tp = pp->trace; tp && (tp->index != oldIndices[j]); tp
                     = tp->next)
					;
				if (tp) {
					if (tp->value)
						symbol[j] = '1';
					else
						symbol[j] = '0';
				} else
					symbol[j] = 'X';
			}
			symbol[j] = '\0';
			if (isIncludeLambda(symbol, lambda, var)){
                //if spaces from start state to itself then no need for pretrim
				if (pp->to == M->q[M->s]){
					result = dfaCopy(M);
					kill_paths(state_paths);
					free(symbol);
					free(lambda);
					return result;
				}
				else{
					extraBitNeeded = true;
					break;
				}
			}
		}
		pp = pp->next;
	}
    // DO NOT FREE PP HERE WE NEED IT LATER
    
    **************************************************
     *   Add a new start state with space self loop   *
     **************************************************/
    
    max_exeps=1 << var; //maybe exponential

    
    numOfChars = 1 << var;
    charachters = (char**) malloc(numOfChars * (sizeof (char*)));
    
    //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
    
    
    dfaSetup(M->ns+1, var, indices); //add one new initial state as start state
    exeps=(char *)malloc(max_exeps*(var+1)*sizeof(char)); //plus 1 for \0 end of the string
    to_states=(int *)malloc(max_exeps*sizeof(int));
    statuces=(char *)malloc((M->ns+2)*sizeof(char));
    
    //printf("Before Replace Char\n");
    //dfaPrintVerbose(M);
    
    /******    Copy transitions from original start state to new one  ********/
    //construct the added paths for the initial state
	state_paths = pp = make_paths(M->bddm, M->q[M->s]);
    k=0;
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
                    exeps[k * (var + 1) + j] = symbol[j];
                exeps[k * (var + 1) + var] = '\0';
                k++;
            }
            else {
                removeTransitionOnChar(symbol, lambda, var, charachters, &size);
                for (i = 0; i < size; i++)
                {
                    //						printf("%s, ", charachters[i]);
                    to_states[k] = pp->to + 1;
                    for (j = 0; j < var; j++)
                        exeps[k * (var + 1) + j] = charachters[i][j];
                    exeps[k * (var + 1) + var] = '\0';
                    free(charachters[i]);
                    k++;
                }
                //					printf("\n");
            }
        } //end if
        pp = pp->next;
    } //end while
    kill_paths(state_paths);
    
    //add self cycle on lambda to new start state
    to_states[k] = 0;
    for (j = 0; j < var; j++)
        exeps[k * (var + 1) + j] = lambda[j];
    exeps[k * (var + 1) + var] = '\0';
    k++;

    //original out trans from origianl start state + 1 for lambda self cycle
    dfaAllocExceptions(k);
    //copy out edges from original start state
    for(k--;k>=0;k--)
        dfaStoreException(to_states[k],exeps+k*(var+1));
    dfaStoreState(sink+1);
    
    // if original start state is accepting then
    // new one should be 
    if(M->f[M->s] == 1)
        statuces[0]='+';
    else
        statuces[0]='-';
    
    /**************************************************
     *   Add remaining states from old automaton      *
     **************************************************/
    
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
                
                to_states[k] = pp->to + 1;
                for (j = 0; j < var; j++)
                    exeps[k * (var + 1) + j] = symbol[j];
                exeps[k * (var + 1) + var] = '\0';
                k++;
                
			}
			pp = pp->next;
		} //end while
        
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (var + 1));
		dfaStoreState(sink + 1);
        
		if (M->f[i] == 1)
			statuces[i + 1] = '+';
		else
			statuces[i + 1] = '-';
		kill_paths(state_paths);
	}
    
	statuces[M->ns + 1] = '\0';
	result = dfaBuild(statuces);
    
    free(exeps);
    //printf("FREE ToState\n");
    free(to_states);
    //printf("FREE STATUCES\n");
    free(statuces);
    free(charachters);
    free(lambda);
    free(symbol);
    //	printf("dfaAfterleftTrimBeforeMinimize\n");
    //	dfaPrintGraphviz(result, len, indices);
	//	dfaPrintVerbose(result);
    if( DEBUG_SIZE_INFO )
    	printf("\t peak : pre_left_trim : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
    DFA *tmp = dfaMinimize(result);
    dfaFree(result);
    return tmp;
}



// Stores the trimmed input string into the given output buffer, which must be
// large enough to store the result.  If it is too small, the output is
// truncated.
size_t trimwhitespace(char *out, size_t len, const char *str)
{
  if(len == 0)
    return 0;

  const char *end;
  size_t out_size;

  // Trim leading space
  while(isspace(*str)) str++;

  if(*str == 0)  // All spaces?
  {
    *out = 0;
    return 1;
  }

  // Trim trailing space
  end = str + strlen(str) - 1;
  while(end > str && isspace(*end)) end--;
  end++;

  // Set output size to minimum of trimmed string length and buffer size minus 1
  out_size = (end - str) < len-1 ? (end - str) : len-1;

  // Copy trimmed string and add null terminator
  memcpy(out, str, out_size);
  out[out_size] = 0;

  return out_size;
}

DFA* dfaTrim(DFA* inputAuto, char c, int var, int* indices){
	DFA *leftTrimmed, *leftThenRightTrimmed;
	leftTrimmed = dfaLeftTrim(inputAuto, c, var, indices);
//	printf("\n\n\ndfa after left trim\n");
//	dfaPrintGraphvizAsciiRange(leftTrimmed, var, indices, 0);
	leftThenRightTrimmed = dfaRightTrim(leftTrimmed, c, var, indices);
	dfaFree(leftTrimmed);
	return leftThenRightTrimmed;
}

/**
 * trims a list of characters stored in array chars[].
 * num is the size of array chars
 */
DFA* dfaTrimSet(DFA* inputAuto, char chars[], int num, int var, int* indices){
	DFA *leftTrimmed, *leftThenRightTrimmed, *tmp;
	int i;
	assert(chars != NULL);

	tmp = dfaCopy(inputAuto);

	for (i = 0; i < num; i++){
		leftTrimmed = dfaLeftTrim(tmp, chars[i], var, indices);
		dfaFree(tmp);
		tmp = leftTrimmed;
	}

	for (i = 0; i < num; i++){
		leftThenRightTrimmed = dfaRightTrim(tmp, chars[i], var, indices);
		dfaFree(tmp);
		tmp = leftThenRightTrimmed;
	}

	return leftThenRightTrimmed;
}

DFA* dfaPreTrim(DFA* inputAuto, char c, int var, int* indices){
	DFA *rightPreTrimmed, *rightThenLeftPreTrimmed;
	rightPreTrimmed = dfaPreRightTrim(inputAuto, c, var, indices);
//	printf("\n\n\ndfa after pre right trim\n");
//	dfaPrintGraphvizAsciiRange(rightPreTrimmed, var, indices, 0);
	rightThenLeftPreTrimmed = dfaPreLeftTrim(rightPreTrimmed, c, var, indices);
	dfaFree(rightPreTrimmed);
	return rightThenLeftPreTrimmed;
}

/**
 * pretrims a list of characters stored in array chars[].
 * num is the size of array chars
 */
DFA* dfaPreTrimSet(DFA* inputAuto, char chars[], int num, int var, int* indices){
	DFA *leftPreTrimmed, *leftThenRightPreTrimmed, *tmp;
	int i;
	assert(chars != NULL);

	tmp = dfaCopy(inputAuto);

	for (i = 0; i < num; i++){
		leftPreTrimmed = dfaPreLeftTrim(tmp, chars[i], var, indices);
		dfaFree(tmp);
		tmp = leftPreTrimmed;
	}

	for (i = 0; i < num; i++){
		leftThenRightPreTrimmed = dfaPreRightTrim(tmp, chars[i], var, indices);
		dfaFree(tmp);
		tmp = leftThenRightPreTrimmed;
	}

	return leftThenRightPreTrimmed;
}

DFA* dfaMysqlEscapeString(DFA* inputAuto, int var, int* indices) {
    char escapedChars[] = {'\'', '"', (char)10, (char)13, (char)26};
    DFA* retMe1 = dfa_escape(inputAuto, var, indices, '\\', escapedChars, 5);
    return retMe1;
}


DFA* dfaPreMysqlEscapeString(DFA* inputAuto, int var, int* indices) {
    char escapedChars[] = {'\\', '\'', '"', (char)10, (char)13, (char)26};
    DFA* retMe1 = dfa_pre_escape(inputAuto, var, indices, '\\', escapedChars, 6);
	return retMe1;
}

DFA* dfaAddSlashes(DFA* inputAuto, int var, int* indices){
        char escapedChars[] = {'\'', '"'};
//    if (isLengthFiniteDFS(inputAuto, var, indices)){
    DFA* retMe1 = dfa_escape(inputAuto, var, indices, '\\', escapedChars, 2);
        // escape single quota '
        // ' -> \'
//        DFA* retMe2 = dfa_escape_single_finite_lang(retMe1, var, indices, '\'', '\\');
//        dfaFree(retMe1);
//        // escape single quota '
//        // " -> \"
//        retMe1 = dfa_escape_single_finite_lang(retMe2, var, indices, '"', '\\');
//        dfaFree(retMe2);
        return retMe1;
//    }
//    else
//    {
//        DFA* searchAuto = dfa_construct_string("\\", var, indices);
//        char* replaceStr = "\\\\";
//        DFA* retMe1 = dfa_replace_extrabit(inputAuto, searchAuto, replaceStr, var, indices);
//        dfaFree(searchAuto); searchAuto = NULL;
//        printf("passed first replace in addSlashes\n");
//        // escape single quota '
//        // ' -> \'
//        searchAuto = dfa_construct_string("'", var, indices);
//        replaceStr = "\\'";
//        DFA* retMe2 = dfa_replace_extrabit(retMe1, searchAuto, replaceStr, var, indices);
//        dfaFree(searchAuto); searchAuto = NULL;
//        dfaFree(retMe1); retMe1 = NULL;
//        printf("passed second replace  in addSlashes\n");
//        // escape double quota "
//        // " -> \"
//        searchAuto = dfa_construct_string("\"", var, indices);
//        replaceStr = "\\\"";
//        retMe1 = dfa_replace_extrabit(retMe2, searchAuto, replaceStr, var, indices);
//        dfaFree(searchAuto); searchAuto = NULL;
//        dfaFree(retMe2); retMe2 = NULL;
//        printf("passed third replace in addSlashes\n");
//        return retMe1;
//    }
}

DFA* dfaPreAddSlashes(DFA* inputAuto, int var, int* indices){

    char escapedChars[] = {'\\', '\'', '"'};
//    if (isLengthFiniteDFS(inputAuto, var, indices)){
//        DFA* retMe1 = dfa_pre_escape_single_finite_lang(inputAuto, var, indices, '"', '\\');
    DFA* retMe1 = dfa_pre_escape(inputAuto, var, indices, '\\', escapedChars, 3);
//        // escape single quota '
//        // ' -> \'
//        DFA* retMe2 = dfa_pre_escape_single_finite_lang(retMe1, var, indices, '\'', '\\');
//        dfaFree(retMe1);.
    
        // escape single quota '
        // " -> \"
//        retMe1 = dfa_pre_escape_single_finite_lang(retMe2, var, indices, '\\', '\\');
//        dfaFree(retMe2);
        return retMe1;
//    }
//    else
//    {
//
//	// pre escape backslash \
//	// \ -> \\
//
//	DFA* searchAuto = dfa_construct_string("\\", var, indices);
//		char* replaceStr = "\\\\";
//		DFA* retMe1 = dfa_pre_replace_str(inputAuto, searchAuto, replaceStr, var, indices);
//		dfaFree(searchAuto); searchAuto = NULL;
//		// escape single quota '
//		// ' -> \'
//		searchAuto = dfa_construct_string("'", var, indices);
//		replaceStr = "\\'";
//		DFA* retMe2 = dfa_pre_replace_str(retMe1, searchAuto, replaceStr, var, indices);
//		dfaFree(searchAuto); searchAuto = NULL;
//		dfaFree(retMe1); retMe1 = NULL;
//
//		// escape double quota "
//		// " -> \"
//		searchAuto = dfa_construct_string("\"", var, indices);
//		replaceStr = "\\\"";
//		retMe1 = dfa_pre_replace_str(retMe2, searchAuto, replaceStr, var, indices);
//		dfaFree(searchAuto); searchAuto = NULL;
//		dfaFree(retMe2); retMe2 = NULL;
//
//		return retMe1;
//    }
}

void copyPrevBits(char* to, char* from, int limit){
	int i;
	//copy previous bits
	for (i = 0; i < limit; i++)
		to[i] = from[i];
}

/**
 */
void getUpperCaseCharsHelper(char** result, char* transitions, int* indexInResult, int currentBit, int var, char* prev){
	int i;
	if (transitions[currentBit] == 'X')
	{
		transitions[currentBit] = '0';
		getUpperCaseCharsHelper(result, transitions, indexInResult, currentBit, var, prev);
		transitions[currentBit] = '1';
		getUpperCaseCharsHelper(result, transitions, indexInResult, currentBit, var, prev);
		transitions[currentBit] = 'X';
	}
	// things that do not contain upper case
	else if ( (transitions[0] == '1' && currentBit == 0) ||
			  (transitions[1] == '0' && currentBit == 1) ||
			  (transitions[2] == '0' && currentBit == 2) ||
			  (transitions[5] == '1' && transitions[3] == '1' && currentBit == 5) ||
			  (transitions[7] ==  transitions[3] && currentBit == 7)
			 )
	{
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof (char)));
		for (i = 0; i < var; i++){
			result[*indexInResult][i] = transitions[i];
		}
		result[*indexInResult][var] = '0';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
	}
	else if ( (transitions[3] != transitions[4] && (currentBit == 4 )) ||
			  (transitions[3] != transitions[6] && currentBit == 6 ) ||
			  (transitions[3] != transitions[7] && currentBit == 7 ) ||
			  (transitions[5] == '1' && transitions[3] ==  '0' && currentBit == 5)
				 ){
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof(char)));
		for (i = 0; i < var; i++)
			result[*indexInResult][i] = transitions[i];
		// only difference between capital and small is bit number 2
		result[*indexInResult][2] = '0';
		// extrabit should be 1 since we may already have same small letter originally with 0
		result[*indexInResult][var] = '1';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
	}
	else{
		if (currentBit < (var-1)){
			getUpperCaseCharsHelper(result, transitions, indexInResult, currentBit + 1, var, prev);
		}
		else
			assert(FALSE);
	}

}
/**
 */
void getLowerUpperCaseCharsPrePostHelper(char** result, char* transitions, int* indexInResult, int currentBit, int var, char* prev, boolean lowerCase, boolean preImage){
	int i;
	if (transitions[currentBit] == 'X')
	{
		transitions[currentBit] = '0';
		getLowerUpperCaseCharsPrePostHelper(result, transitions, indexInResult, currentBit, var, prev, lowerCase, preImage);
		transitions[currentBit] = '1';
		getLowerUpperCaseCharsPrePostHelper(result, transitions, indexInResult, currentBit, var, prev, lowerCase, preImage);
		transitions[currentBit] = 'X';
	}
	// things that do not contain lower case
	else if ( (transitions[0] == '1' && currentBit == 0) ||
			  (transitions[1] == '0' && currentBit == 1) ||
			  (currentBit == 2 && ((transitions[2] == '1' && lowerCase) || (transitions[2] == '0' && !lowerCase))) ||
			  (transitions[5] == '1' && transitions[3] == '1' && currentBit == 5) ||
			  (transitions[7] ==  transitions[3] && currentBit == 7)
			 )
	{
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof (char)));
		for (i = 0; i < var; i++){
			result[*indexInResult][i] = transitions[i];
		}
		result[*indexInResult][var] = '0';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
	}
	else if ( (transitions[3] != transitions[4] && (currentBit == 4 )) ||
			  (transitions[3] != transitions[6] && currentBit == 6 ) ||
			  (transitions[3] != transitions[7] && currentBit == 7 ) ||
			  (transitions[5] == '1' && transitions[3] ==  '0' && currentBit == 5)
				 ){
		result[*indexInResult] = (char*) malloc((var+2)*(sizeof(char)));
		for (i = 0; i < var; i++)
			result[*indexInResult][i] = transitions[i];
		// only difference between capital and small is bit number 2
		if (!preImage){
			if (lowerCase)
				result[*indexInResult][2] = '1';
			else
				result[*indexInResult][2] = '0';
        }
		// extrabit should be 1 since we may already have same small letter originally with 0
		result[*indexInResult][var] = '1';//extrabit
		result[*indexInResult][var+1] = '\0';
		(*indexInResult)++;
		if (preImage){
			result[*indexInResult] = (char*) malloc((var+2)*(sizeof(char)));
			for (i = 0; i < var; i++)
				result[*indexInResult][i] = transitions[i];
			// only difference between capital and small is bit number 2
			if (lowerCase)
				result[*indexInResult][2] = '1';
			else
				result[*indexInResult][2] = '0';
			// extrabit should be 1 since we may already have same small letter originally with 0
			result[*indexInResult][var] = '1';//extrabit
			result[*indexInResult][var+1] = '\0';
			(*indexInResult)++;
		}
	}
	else{
			if (currentBit < (var-1)){
				getLowerUpperCaseCharsPrePostHelper(result, transitions, indexInResult, currentBit + 1, var, prev, lowerCase, preImage);
			}
			else
				assert(FALSE);
	}

}

/**
 * returns same chars in transitions unless char is capital in which case it is converted into small
 * or visa versa
 * examples:
 * A=01000001 -> a=[011000011]
 * {@, A, B, C ,D, E, F, G}=01000XXX -> {@, a, b, c, d, e, f, g}=[010000000, 011000011, 0110001X1, 011001XX1]
 * extrabit will be used. 0 for original letters, 1 for new small letters (converted from capital) to differentiate from original small chars
 */
void getLowerUpperCaseCharsPrePost(char* transitions, int var, char** result, int* pSize, boolean lowerCase, boolean preImage){
	int indexInResult = 0;
	char* prev = (char*) malloc(var*(sizeof(char)));
	getLowerUpperCaseCharsPrePostHelper(result, transitions, &indexInResult, 0, var, prev, lowerCase, preImage);
	*pSize = indexInResult;
}

/**
 * This functions models any function that changes all capital letters in a string to small ones (for example strtolower in php)
 * M: dfa to process
 * var: number of bits per character(for ASCII it is 8 bits)
 * indices: the indices
 * output: return D such that L(D) = { W_1S_1W_2S2..W_nS_n | W_1C_1W_2C2..W_nC_n element_of L(M) && W_i element_of Sigma* && S_i, C_i element_of Sigma && S_i = LowerCase(C_i)}
 */
DFA* dfaPrePostToLowerUpperCaseHelper(DFA* M, int var, int* oldIndices, boolean lowerCase, boolean preImage){
		DFA *result;
		paths state_paths, pp;
		trace_descr tp;
		int i, j, n, k;
		char *exeps;
		int *to_states;
		int sink;
		long max_exeps;
		char *statuces;
		int len;
		int ns = M->ns;

		len = var + 1;
		int* indices = allocateArbitraryIndex(len);

		max_exeps = 1 << len; //maybe exponential
		sink = find_sink(M);
		assert(sink>-1);

		char* symbol = (char *) malloc((len + 1) * sizeof(char));//len+1 since we need extra bit
		exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
		to_states = (int *) malloc(max_exeps * sizeof(int));
		statuces = (char *) malloc((ns + 1) * sizeof(char));
		int numOfChars = 1 << len;
		char** charachters = (char**) malloc(numOfChars * (sizeof (char*)));
		int size = 0;


		dfaSetup(ns, len, indices);
		for (i = 0; i < M->ns; i++) {
			state_paths = pp = make_paths(M->bddm, M->q[i]);
			k = 0;
			while (pp) {
				if (pp->to != sink) {
					for (j = 0; j < var; j++) {
						//the following for loop can be avoided if the indices are in order
						for (tp = pp->trace; tp && (tp->index != indices[j]); tp
								= tp->next)
							;
						if (tp) {
							if (tp->value)
								symbol[j] = '1';
							else
								symbol[j] = '0';
						} else
							symbol[j] = 'X';
					}
					symbol[var] = '\0';
					// convert symbol into a list of chars where we replace each capital letter with small letter
					getLowerUpperCaseCharsPrePost(symbol, var, charachters, &size, lowerCase, preImage);
					for (n = 0; n < size; n++)
					{
//						printf("%s, ", charachters[n]);
						to_states[k] = pp->to;
						for (j = 0; j < len; j++)
							exeps[k * (len + 1) + j] = charachters[n][j];
						exeps[k * (len + 1) + len] = '\0';
						free(charachters[n]);
						k++;
					}
//					printf("\n");
				}
				pp = pp->next;
			}
			kill_paths(state_paths);

			// if accept state create a self loop on lambda
			dfaAllocExceptions(k);
			for (k--; k >= 0; k--)
				dfaStoreException(to_states[k], exeps + k * (len + 1));
			dfaStoreState(sink);

			if (M->f[i] == -1)
				statuces[i] = '-';
			else if (M->f[i] == 1)
				statuces[i] = '+';
			else
				statuces[i] = '0';
		}

		statuces[ns] = '\0';
		DFA* tmpM = dfaBuild(statuces);
//		dfaPrintGraphviz(tmpM, len, indices);
//		dfaPrintVerbose(tmpM);
		flush_output();
		if( DEBUG_SIZE_INFO )
			printf("\t peak : upper_lower_case : states %d : bddnodes %u : before projection \n", tmpM->ns, bdd_size(tmpM->bddm) );
		result = dfaProject(tmpM, ((unsigned)var));
		dfaFree(tmpM); tmpM = NULL;
		if( DEBUG_SIZE_INFO )
			printf("\t peak : upper_lower_case : states %d : bddnodes %u : after projection \n", result->ns, bdd_size(result->bddm) );
		tmpM = dfaMinimize(result);
		dfaFree(result);result = NULL;

		free(exeps);
		free(symbol);
		free(to_states);
		free(statuces);
		free(indices);
		free(charachters);

		return tmpM;
}

DFA* dfaToLowerCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, TRUE, FALSE);
}

DFA* dfaToUpperCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, FALSE, FALSE);
}

DFA* dfaPreToLowerCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, FALSE, TRUE);
}

DFA* dfaPreToUpperCase(DFA* M, int var, int* indices){
	return dfaPrePostToLowerUpperCaseHelper(M, var, indices, FALSE, TRUE);
}


PStatePairArrayList getNewStatePairs(DFA *M, int var, int *indices, char **escapedCharsBin, unsigned numOfEscapedChars,int sink){
    int i, j;
    paths state_paths, pp;
	trace_descr tp;
    char *symbol = (char *) malloc((var + 1) * sizeof(char));
    PStatePairArrayList statePairs = createStatePairArrayList(((M->ns < 32)? M->ns : 32), numOfEscapedChars);
    // for each original state
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		// for each transition out from current state (state i)
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
				symbol[var] = '\0';
                
                for (j = 0; j < numOfEscapedChars; j++){
                    if (isIncludeLambda(symbol, escapedCharsBin[j], var)) {
                        char escapedChar = strtobin(escapedCharsBin[j], var);
                        addEscapeCharToStatePairArrayList(statePairs, i, pp->to, escapedChar);
                    }
                }
			}
			pp = pp->next;
		} //end while        
		kill_paths(state_paths);
	} // end for each original s
    
    free(symbol);
    
    return statePairs;
}

DFA *dfa_escape(DFA *M, int var, int *oldindices, char escapeChar, char *escapedChars, unsigned numOfEscapedChars){
    if (check_emptiness_minimized(M)){
        return dfaCopy(M);
    }
    DFA *result = NULL;
	char* escapeCharBin = bintostr(escapeChar, var);
    
	paths state_paths, pp;
	trace_descr tp;
    
	int i, j, z, k;
    
	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int len = var;
	int sink;
    
	int numOfChars;
	char** charachters;
	int size;
    
    //include the escape char as escaped
    numOfEscapedChars++;
    char **escapedCharsBin = (char **) mem_alloc((size_t) numOfEscapedChars * sizeof(char *));
    for (i = 0; i < numOfEscapedChars - 1; i++){
        escapedCharsBin[i] = bintostr(escapedChars[i], var);
    }
    escapedCharsBin[i] = escapeCharBin;
    
	char *symbol = (char *) malloc((var + 1) * sizeof(char));
    
    int *indices = allocateArbitraryIndex(len);
	max_exeps = 1 << len; //maybe exponential
	sink = find_sink(M);
	assert(sink > -1);
    
	numOfChars = 1 << var;
	charachters = (char**) malloc(numOfChars * (sizeof(char*)));
    
    PStatePairArrayList statePairs = getNewStatePairs(M, var, indices, escapedCharsBin, numOfEscapedChars, sink);
//    assert(statePairs->index < INT_MAX && statePairs->sorted);
//    printStatePairArrayList(statePairs);
    int num_new_states = (int) statePairs->index;
    
	dfaSetup(M->ns + num_new_states, len, indices); //add one new accept state
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((M->ns + num_new_states + 1) * sizeof(char)); //plus 1 for \0 end of the string
    
    int numOfEscapeStates = 0;
    bool escapeState;
    
	// for each original state
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
        escapeState = false;
		// for each transition out from current state (state i)
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
				symbol[var] = '\0';
                size_t index;
                if (searchStatePairArrayListBS(statePairs, i, pp->to
                                               , &index)){
                    escapeState = true;
                    removeTransitionOnChars(symbol, escapedCharsBin, numOfEscapedChars, var, charachters,
                                            &size);
                    for (z = 0; z < size; z++) {
                        // first copy of non-bamda char to original destination
                        to_states[k] = pp->to;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = charachters[z][j];
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
                        free(charachters[z]);
                    }
                }
                else {
                    to_states[k] = pp->to;
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = symbol[j];
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                }
			}
			pp = pp->next;
		} //end while
        
        if (escapeState){
            to_states[k] = (int) numOfEscapeStates + M->ns;
//            printf("%d -> %d\n", i, to_states[k]);
            for (j = 0; j < var; j++)
                exeps[k * (len + 1) + j] = escapeCharBin[j];
            exeps[k * (len + 1) + len] = '\0';
//            printf("%s\n",exeps + (k * (len + 1)));
            k++;
            numOfEscapeStates++;
        }
        
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--){
			dfaStoreException(to_states[k], exeps + k * (len + 1));
        }
		dfaStoreState(sink);
        if (M->f[i] == 1)
            statuces[i] = '+';
        else
            statuces[i] = '-';
        
		kill_paths(state_paths);
	} // end for each original state

	// add new states
    // i-> new state number
    // j-> from state number in state pairs
    // k-> state pairs index
    unsigned m, n, first;
//    if (num_new_states > 0)
//        first = statePairs->list[0]->first;
    z = 0;
    for (i = 0; i < num_new_states; i++){
        if (z < statePairs->index)
            first = statePairs->list[z]->first;
        k = 0;
        while (z < statePairs->index && statePairs->list[z]->first == first){
            PStatePair statePair = statePairs->list[z];
            m = 0;
            while (m < numOfEscapedChars && statePair->escapedChars[m] != (char) 255) {
                to_states[k] = statePair->second;
//                printf("%d -> %d\n", (i + M->ns), to_states[k]);
                char * escapedCharBin = bintostr(statePair->escapedChars[m], var);
                for (n = 0; n < var; n++)
                    exeps[k * (len + 1) + n] = escapedCharBin[n];
                exeps[k * (len + 1) + len] = '\0';
//                printf("%s\n",exeps + (k * (len + 1)));
                k++;m++;
            }
            z++;
        }
        dfaAllocExceptions(k);
		for (k--; k >= 0; k--){
			dfaStoreException(to_states[k], exeps + k * (len + 1));
        }
		dfaStoreState(sink);
        statuces[i + M->ns] = '-';
    }
	statuces[M->ns + num_new_states] = '\0';
	result = dfaBuild(statuces);
    
    //	printf("dfaAfterRightTrimBeforeMinimize\n");
    //	dfaPrintGraphviz(result, len, indices);
	free(exeps);
	free(to_states);
	free(statuces);
	free(charachters);
    for (i = 0; i < numOfEscapedChars; i++)
        free(escapedCharsBin[i]);//this will free the escapeChar also since it is escaped
    free(indices);
    free(symbol);

    for (i = 0; i < statePairs->index; i++){
        free(statePairs->list[i]->escapedChars);
        free(statePairs->list[i]);
    }
    free(statePairs->list);
    free(statePairs);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : escape : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
    DFA *tmp = dfaMinimize(result);
    dfaFree(result);
	return tmp;

}


bool getNextStateOnLambda(DFA *M, int var, int *indices, char *lambda, unsigned srcState, unsigned *pNextState){

    int sink = find_sink(M);
    assert(sink >= 0);
    unsigned j;
    if (pNextState)
        *pNextState = UINT_MAX;
    bool found = false;
    paths state_paths, pp;
	trace_descr tp;
    char *symbol = (char *) malloc((var + 1) * sizeof(char));
    
    state_paths = pp = make_paths(M->bddm, M->q[srcState]);
    // for each transition out from current state srcState
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
            symbol[var] = '\0';
                        
            if (isIncludeLambda(symbol, lambda, var)) {
                if (pNextState)
                    *pNextState = pp->to;
                found = true;
                break;

            }
        }
        pp = pp->next;
    } //end while
    kill_paths(state_paths);
    
    free(symbol);
    return found;
}

///*
// This will mark a number of state on a single path which have an escape char out of them as either escape states 
// (the escape char out of the state is to escape) or escaped (the escape char out of the state is being escaped).
// This will traverse one and only one path. This path is supposed to have a bunch of escape chars either escaping or being escaped.
// We will follow the path to the end i.e. when there is not escape char out or until we reach a marked state.
// Then start marking in reverse direction.
// Think about following langs: {a\\a, abc\\a}, {\\\\}, a(\ba\)*
// */
//void markEscapeStates(DFA *M, int var, int *indices, PUIntArrayList escapeStates, PUIntArrayList nonEscapeStates, pTransitionRelation pTransRel, pTransitionRelation pRevTransRel, unsigned currentState, unsigned prevState, const char *lambda, const char **escapees, const unsigned numOfEscapees){
//    unsigned nextState, i;
//    //if I have no next states then mark previous as escaped state
//    if (pTransRel->degrees[currentState] == 0){
//        insertIntoUIntSortedArrayList(nonEscapeStates, prevState);
//        return;
//    }
//    //if I am escaped then prev is nonescape
//    if (searchUIntArrayListBS(escapeStates, currentState, NULL)){
//        insertIntoUIntSortedArrayList(nonEscapeStates, prevState);
//        return;
//    }
//    //if I am not escape then prev is escape
//    else if (searchUIntArrayListBS(nonEscapeStates, currentState, NULL)){
//        insertIntoUIntSortedArrayList(escapeStates, prevState);
//        return;
//    }
//    //I do not know if I am escape or not
//    else {
//        //if I have out transition on escape char then check my next and let it mark me
//        if (getNextStateOnLambda(M, var, indices, lambda, currentState, &nextState)){
//            markEscapeStates(M, var, indices, escapeStates, nonEscapeStates, pTransRel, pRevTransRel, nextState, currentState, lambda, escapees, numOfEscapees);
//            //then I mark my previous
//            //if I am escaped then prev is nonescape
//            if (searchUIntArrayListBS(escapeStates, currentState, NULL)){
//                insertIntoUIntSortedArrayList(nonEscapeStates, prevState);
//                return;
//            }
//            //if I am not escape then prev is escape
//            else if (searchUIntArrayListBS(nonEscapeStates, currentState, NULL)){
//                insertIntoUIntSortedArrayList(escapeStates, prevState);
//                return;
//            }
//
//        }
//        //if I do not have out edges on lambda then
//        else {
//            //if I have at least one out edge on escapee char that is not the escape char (i.e. ' or " but not \) then I am escaping
//            for (i = 0; i < numOfEscapees; i++) {
//                if (getNextStateOnLambda(M, var, indices, escapees[i], currentState, &nextState)) {
//                    insertIntoUIntSortedArrayList(nonEscapeStates, currentState);
//                    insertIntoUIntSortedArrayList(escapeStates, prevState);
//                    return;
//                }
//            }
//            //I do not have out edge on escape char nor on an escapee char
//            //so prev is an escaped escape char
//            insertIntoUIntSortedArrayList(nonEscapeStates, prevState);
//            return;
//        }
//    }
//}


void getEscapeTransitionsHelper(DFA *M, int var, int *indices, PStatePairArrayList escapeTransitions, PUIntArrayList escapedStates, bool *visited, pTransitionRelation pTransRel, pTransitionRelation pRevTransRel, unsigned currentState, char *escapeCharBin, char escapeChar, unsigned numOfEscapees){
    unsigned nextState;
//    printf("current State = %u, degree of current State = %u\n", currentState, pTransRel->degrees[currentState]);
    
    visited[currentState] = true;
    
    //if current state has at least one out transition and it is on escape char
    if (pTransRel->degrees[currentState] > 0 && getNextStateOnLambda(M, var, indices, escapeCharBin, currentState, &nextState)){
        //Invariant: if a state is escaped then we must have seen at least one escape transition going to this state
        unsigned *fromStates = pRevTransRel->adjList[currentState];
        size_t index;
        bool escaped = false;
        unsigned i;
        for (i = 0; i < pRevTransRel->degrees[currentState] && !escaped; i++){
            unsigned from = fromStates[i];
//            printf("searching for %u->%u\n", from, currentState);
            if (searchStatePairArrayListBS(escapeTransitions, from, currentState, &index)){
//                printf("%u->%u escapes %u->%u\n",from, currentState, currentState, nextState);
                escaped = true;
                assert(searchUIntArrayListBS(escapedStates, currentState, NULL));
            }
        }
        if (!escaped){
            insertIntoStatePairSortedArrayList(escapeTransitions, currentState, nextState, escapeChar);
//            printf("new escape trans: %u->%u", currentState, nextState);
            if (!searchUIntArrayListBS(escapedStates, nextState, NULL)){
//                printf("   ==>  escaping state: %u\n", nextState);
                insertIntoUIntSortedArrayList(escapedStates, nextState);
            }
        }
        //markEscapeStates(M, var, indices, escapeStates, nonEscapeStates, pTransRel, pRevTransRel, nextState, currentState, escapeLambda, escapees, numOfEscapees
    }
    
    unsigned nextStateIndex;
    // if current node has out edges visit them
    if (pTransRel->degrees[currentState] > 0){
        for (nextStateIndex = 0; nextStateIndex < pTransRel->degrees[currentState]; nextStateIndex++){
            unsigned nextState = pTransRel->adjList[currentState][nextStateIndex];
//            printf("Next State = %u\n", nextState);
            //first time to see next node --> carry on DFS
            if (visited[nextState] == false)
                getEscapeTransitionsHelper(M, var, indices, escapeTransitions, escapedStates, visited, pTransRel, pRevTransRel, nextState, escapeCharBin, escapeChar, numOfEscapees);
        }
    }
}


/*
 An excape character can appear either to escape another 
 character or as a regular character (that must be preceeded
 by itself to escape itself).
 This will return a set of states that represent the from state
 of all transitions that have the escape character on them to
 escape other characters.
 */
void getEscapeTransitions(DFA *M, int var, int *indices, char *escapeLambda, char escapeChar, unsigned numOfEscapees, PStatePairArrayList escapeTransitions, PUIntArrayList escapedStates){
    bool *visited = (bool *) mem_alloc((size_t) M->ns * sizeof(bool));
    memset(visited, false, (size_t) M->ns * sizeof(bool));
    int sink = find_sink(M);
    assert(sink >= 0);

    pTransitionRelation pTransRel = dfaGetTransitionRelation(M);
    dfaShiftTransitionRelation(pTransRel, sink);
//    dfaPrintTransitionRelationNoShift(pTransRel);
    pTransitionRelation pRevTransRel = dfaReverseTransitionRelation(pTransRel);
//    dfaShiftTransitionRelation(pRevTransRel, sink);
//    dfaPrintTransitionRelationNoShift(pRevTransRel);
    getEscapeTransitionsHelper(M, var, indices, escapeTransitions, escapedStates, visited, pTransRel, pRevTransRel, M->s, escapeLambda, escapeChar, numOfEscapees);
    free(visited);
    dfaFreeTransitionRelation(pTransRel);
    dfaFreeTransitionRelation(pRevTransRel);

}

/*
 if we want to construct a new automaton by delteing states from original
 then shift will help us figure out the new ids for the new states.
 size: is the number of states in the original automaton
 deltedStates: the list of states that will be removed and it has to be sorted
 returns shiftArray: an array of size equal to original number of states
 where each entry represent the negartive shift for the correspoinding 
 state when it is added to the new automaton (if it is to be added).
 */
unsigned *getShiftArray(PUIntArrayList deletedStates, int size){
    assert(size >= 0);
    assert(deletedStates->index == 0 || deletedStates->sorted);
    
    unsigned *shiftArray = mem_alloc(size * sizeof(unsigned));
    mem_zero(shiftArray, size * sizeof(unsigned));
    
    int i, j, shift;
    for (i = 0, j = 0, shift = 0; i < size; i++){
        //if state i is escaped
        if (j < deletedStates->index && deletedStates->list[j] == i){
            j++;
            shift++;
        }
        shiftArray[i] = shift;
    }
    return shiftArray;
}

/*
 We assume here two things:
 1- the escape function - when computing post image - escapes every character it is asked 
 to escape even if the character is escaped in the original language. For example:
 addSlashes when applied to the following string "\\\" will produce the following output
 "\\\\\\".
 2- the escape character itself must be escaped by the escape function.
 Given this we do the following:
 when we see an edge with an escape char then:
 1- if it is preceeded by an edge with the escape char then we leave it  as it is
 2- if it is not preceeded by an edge with the escape then we assume that it is there to
 escape so we remove it and add all escaped characters from current state to next next state
 Invariant (we do not consider sink here):
 If a state has the escape char out from it to escape other chars then:
 1- It will only have one transition out of it and the transition is
 going to be on the escape char (all others to sink state).
 2- ALL transitions out of its (only) next state will have only chars that should be escaped.
 This next state must have at least one transition out.
 So this means that we will have two special type of states:
 1- escaping states: states that have one and only one transition out from them on the escape
 char going to an escaped state. The escape char will be seen only on transitions out from
 these states.
 2- escaped states: states that have at least one transition out and all transition out from
 it are on escaped chars only. Escaped chars will be seen only on transitions out from these
 states
 */
DFA *dfa_pre_escape(DFA *M, int var, int *indices, char escapeChar, char *escapedChars, unsigned numOfEscapedChars){
    if (check_emptiness_minimized(M)){
        return dfaCopy(M);
    }
    DFA *result = NULL;
	char* escapeCharBin = bintostr(escapeChar, var);
        
	paths state_paths, pp;
	trace_descr tp;
    
	int i, j, k, z;
    unsigned nextState;
    
	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int sink;
    
    char **escapedCharsBin = (char **) mem_alloc((size_t) numOfEscapedChars * sizeof(char *));
    for (i = 0; i < numOfEscapedChars; i++){
        escapedCharsBin[i] = bintostr(escapedChars[i], var);
    }
    
	char *symbol = (char *) malloc((var + 1) * sizeof(char));
    
	max_exeps = 1 << var; //maybe exponential
	sink = find_sink(M);
	assert(sink > -1);
    
    PStatePairArrayList escapeTransitions = createStatePairArrayList(32, numOfEscapedChars);
    PUIntArrayList escapedStates = createUIntArrayList(32);
    getEscapeTransitions(M, var, indices, escapeCharBin, escapeChar, numOfEscapedChars, escapeTransitions, escapedStates);
    
    unsigned *shiftArray = getShiftArray(escapedStates, M->ns);
    
    int num_of_states = M->ns - ((int)escapedStates->index);
//    printf("number_of_states = %d\n",num_of_states);
//    for (i = 0; i < M->ns; i++){
//        printf("shift[%d] == %d\n", i, shiftArray[i]);
//    }
    
	dfaSetup(num_of_states, var, indices); //add one new accept state
	exeps = (char *) malloc(max_exeps * (var + 1) * sizeof(char)); //plus 1 for \0 end of the string
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((num_of_states + 1) * sizeof(char)); //plus 2, one for the new accept state and one for \0 end of the string
    
	// for each original state
	for (i = 0; i < M->ns; i++) {
        if (searchUIntArrayListBS(escapedStates, i, NULL)){
//            printf("state skipped = %d\n",i);
            continue;
        }
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
		// for each transition out from current state (state i)
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
				symbol[var] = '\0';
                
                /*
                 1- if an escape transition (from, to) then add all escaped transitions (out from "to" state)
                 to current state from. 
                 Invariant: all transitions out from "to" must be escaped transitions (i.e. on escapee chars). Why?
                 Suppose the oppisite, that there is one transition (to, to`) on non escapee char. This means that 
                 there is a path s->...->from->to->to` where the escape char is not escaping and not being escaped.
                 */
                //if escape char is escaping
                if (searchStatePairArrayListBS(escapeTransitions, i, pp->to, NULL)){
                    //assert invariant: only one transition out and it is on escape char
                    for (j = 0; j < var; j++)
                        assert(symbol[j] == escapeCharBin[j]);
                    bool found = false;
                    //for each escaped char
                    for (z = 0; z < numOfEscapedChars; z++){
                        //if next state has an escaped char out of it then add it to next of
                        //currentState in new automaton (no need for extra bits due to
                        //invariant above)
                        if (getNextStateOnLambda(M, var, indices, escapedCharsBin[z], pp->to, &nextState))
                        {
                            //assert invariant: next state is not an escape state
                            assert(searchUIntArrayListBS(escapedStates, pp->to, NULL));
                            found = true;
                            to_states[k] = nextState - shiftArray[nextState];
                            for (j = 0; j < var; j++)
                                exeps[k * (var + 1) + j] = escapedCharsBin[z][j];
                            exeps[k * (var + 1) + var] = '\0';
                            k++;
                        }
                    }
                    //assert invariant: we find at least one to be escaped char on a transition
                    //out from next state
                    assert(found);
                }
                
                /*
                 2- if a regualr state i.e. not being escaped then add it to new
                 automaton as it is.
                 */
                //the state from which escaped chars are out is not going to be reachable in
                //new automaton so it is OK to copy it as it is since it will be removed
                //by minimization
                else if (!searchUIntArrayListBS(escapedStates, i, NULL)){
                    to_states[k] = pp->to - shiftArray[pp->to]; // destination new accept state
                    for (j = 0; j < var; j++)
                        exeps[k * (var + 1) + j] = symbol[j];
                    exeps[k * (var + 1) + var] = '\0';
                    k++;
                }
                /*
                 3- if an escaped state then ignore it since we are computing pre-image
                 of escape.
                 */
            }
			pp = pp->next;
		} //end while
        
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--)
			dfaStoreException(to_states[k], exeps + k * (var + 1));
		dfaStoreState(sink);
        if (M->f[i] == 1)
            statuces[i - shiftArray[i]] = '+';
        else
            statuces[i - shiftArray[i]] = '-';
        
		kill_paths(state_paths);
	} // end for each original state
    //    assert(new_state_counter == (num_new_states - 1));
    statuces[num_of_states] = '\0';
	result = dfaBuild(statuces);

    free(exeps);
//	printf("FREE ToState\n");
	free(to_states);
//	printf("FREE STATUCES\n");
	free(statuces);
    free(escapeCharBin);
    free(symbol);
    for (i = 0; i < numOfEscapedChars; i++){
        free(escapedCharsBin[i]);
    }
    free(escapedCharsBin);
    freeUIntArrayList(escapedStates);
    freeStatePairArrayList(escapeTransitions);
    //    dfaPrintVerbose(result);
	if( DEBUG_SIZE_INFO )
		printf("\t peak : pre_escape : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
    DFA *tmp = dfaMinimize(result);
//    dfaPrintVerbose(tmp);
    dfaFree(result);
    //	printf("dfaAfterRightTrimBeforeMinimize\n");
    //	dfaPrintGraphviz(result, len, indices);

    
	return tmp;
    
}



/*
 if we want to construct a new automaton by adding states to original
 then shift will help us figure out the new ids for the new states.
 size: is the number of states in the original automaton
 addedStates: the list of transitions that will be added and it has to be sorted
 returns shiftArray: an array of size equal to original number of states
 where each entry represent the positive shift for the correspoinding
 state when it is added to the new automaton (if it is to be added).
 Notice: if shifLen is 0 then the shift array will be 0
 */
unsigned *getShiftArray2(PStatePairArrayList addedStates, int size, int shiftLen){
    assert(size >= 0);
    assert(addedStates->index == 0 || addedStates->sorted);
    
    unsigned *shiftArray = mem_alloc(size * sizeof(unsigned));
    mem_zero(shiftArray, size * sizeof(unsigned));
    
    if (addedStates->index == 0 || shiftLen == 0)
        return shiftArray;
    
    int i, j, shift;
    for (i = 0, j = 0, shift = 0; i < size; i++){
        shiftArray[i] = shift;
        if (j < addedStates->index && addedStates->list[j]->first == i){
            while(j < addedStates->index && addedStates->list[j]->first == i)
                j++;
            shift += shiftLen;
        }
    }
    return shiftArray;
}

bool checkExtraBitNeeded(DFA *M, int var, int *indices, int state, char *lambda){
    paths state_paths, pp;
	trace_descr tp;
    int sink = find_sink(M);
	assert(sink > -1);
	int j;
    char *symbol = (char *) malloc((var + 1) * sizeof(char));
    bool retMe = false;
    state_paths = pp = make_paths(M->bddm, M->q[state]);
    while (pp) {
        if (pp->to != sink){
            for (j = 0; j < var; j++){
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
            symbol[var] = '\0';
            if (isIncludeLambda(symbol, lambda, var)){
                retMe = true;
                break;
            }
        }
        pp = pp->next;
    }
    kill_paths(state_paths);
    free(symbol);
    return retMe;
}

DFA *dfa_replace_char_with_string(DFA *M, int var, int *oldIndices, char replacedChar, char *string){
    if (check_emptiness_minimized(M)){
        return dfaCopy(M);
    }
    assert(string != NULL);
    //assert we do not do delete
    assert(strlen(string) > 0);
    //if replacing a char with itself just copy
    if (strlen(string) == 1 && string[0] == replacedChar){
        return dfaCopy(M);
    }
    DFA *result = NULL;
	char* replacedCharBin = bintostr(replacedChar, var);
    bool extraBitNeeded = false;
    char firstChar = string[0];
    char *firstCharBin = bintostr(firstChar, var);
    size_t strLength = strlen(string);
    int numOfAddedStates = 0;
    
	paths state_paths, pp;
	trace_descr tp;
    
	int i, j, k, z;
    
	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int sink;
    
	char *symbol = (char *) malloc((var + 1) * sizeof(char));
    
	max_exeps = 1 << var; //maybe exponential
	sink = find_sink(M);
	assert(sink > -1);
    
    PStatePairArrayList replaceTransitions = createStatePairArrayList(32, 0);
    
    /**************      PREPROCESSING PHASE     ******************/
    for (i = 0; i < M->ns; i++){
        state_paths = pp = make_paths(M->bddm, M->q[i]);
        while (pp) {
            if (pp->to != sink){
                for (j = 0; j < var; j++){
                    //the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != oldIndices[j]); tp =
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
				symbol[var] = '\0';
                if (isIncludeLambda(symbol, replacedCharBin, var)){
                    if (!searchStatePairArrayListBS(replaceTransitions, i, pp->to, NULL)){
                        insertIntoStatePairSortedArrayList(replaceTransitions, i, pp->to, replacedChar);
                        numOfAddedStates += (strLength - 1);
                    }
                    if (!extraBitNeeded && (isIncludeLambda(symbol, firstCharBin, var) || checkExtraBitNeeded(M, var, oldIndices, i, firstCharBin)))
                        extraBitNeeded = true;
                }
            }
            pp = pp->next;
        }
        kill_paths(state_paths);
    }
    
    /**************      BUILDING AUTOMATON PHASE     ******************/
    
    int len = extraBitNeeded? (var + 1): var;
    int *indices = allocateArbitraryIndex(len);

    
    
    //Invariant: each pair in replacedTransitions is unique i.e. no two pairs share the same first state
    
    //if lenString is 1 i.e. replace a char with another char then shift array will be 0's
    unsigned *shiftArray = getShiftArray2(replaceTransitions, M->ns, (int)strLength-1);
    //if lenString is 1 i.e. replace a char with another char then numOfAddedStates will be 0
    int num_of_states = M->ns + numOfAddedStates;
    int new_state_counter = 0;
//    printf("number_of_states = %d\n",num_of_states);
//    for (i = 0; i < M->ns; i++){
//        printf("shift[%d] == %d\n", i, shiftArray[i]);
//    }
    
	dfaSetup(num_of_states, len, indices); //add one new accept state
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((num_of_states + 1) * sizeof(char)); //plus 2, one for the new accept state and one for \0 end of the string
    int toState = -1;
    
	int numOfChars = 1 << var;
	char **charachters = (char**) malloc(numOfChars * (sizeof(char*)));
    int size = 0;
    
	// for each original state
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
        toState = -1;
        new_state_counter = i + shiftArray[i] + 1;
		// for each transition out from current state (state i)
		while (pp) {
			if (pp->to != sink) {
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != oldIndices[j]); tp =
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
				symbol[var] = '\0';
            
                /*
                 if we need to replace "replace char" between these two states then
                 remove transition to old dest and add a new one to a new state.
                 At the end of the whole for loop we will add other states for
                 remaining of the string
                 */
                if (searchStatePairArrayListBS(replaceTransitions, i, pp->to, NULL)){
                    if (isIncludeLambda(symbol, replacedCharBin, var)){
                        //if we are replacing one char with another char
                        if (strLength == 1){
                            //add first char of the string to the new dest state
                            to_states[k] = pp->to;
                            for (j = 0; j < var; j++)
                                exeps[k * (len + 1) + j] = firstCharBin[j];
                            exeps[k * (len + 1) + var] = '1';
                            exeps[k * (len + 1) + len] = '\0';
                            k++;
                        }
                        else {
                            toState = pp->to + shiftArray[pp->to];
                            //add first char of the string to the new dest state
                            to_states[k] = new_state_counter++;
                            for (j = 0; j < var; j++)
                                exeps[k * (len + 1) + j] = firstCharBin[j];
                            exeps[k * (len + 1) + var] = '1';
                            exeps[k * (len + 1) + len] = '\0';
                            k++;
                        }
                        // remove replace char from old dest state
                        removeTransitionOnChar(symbol, replacedCharBin, var, charachters,
                                               &size);
                        for (z = 0; z < size; z++) {
                            //							printf("%s, ", charachters[z]);
                            to_states[k] = pp->to + shiftArray[pp->to]; // destination new accept state
                            for (j = 0; j < var; j++)
                                exeps[k * (len + 1) + j] = charachters[z][j];
                            exeps[k * (len + 1) + var] = '0';
                            exeps[k * (len + 1) + len] = '\0';
                            k++;
                            free(charachters[z]);
                        }
                    }
                    else {//no need to replace anything
                        to_states[k] = pp->to + shiftArray[pp->to]; // destination new accept state
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = symbol[j];
                        exeps[k * (len + 1) + var] = '0';
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
                    }
                }
                else {//no need to replace anything
                    to_states[k] = pp->to + shiftArray[pp->to]; // destination new accept state
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = symbol[j];
                    exeps[k * (len + 1) + var] = '0';
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                }
            }
			pp = pp->next;
		} //end while
        
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--){
			dfaStoreException(to_states[k], exeps + k * (len + 1));
        }
		dfaStoreState(sink + shiftArray[sink]);
        if (M->f[i] == 1)
            statuces[i + shiftArray[i]] = '+';
        else
            statuces[i + shiftArray[i]] = '-';
		kill_paths(state_paths);
        
        //Now if state i has a transition out on "replaced char" then we add additional states
        //from state i for the replace string
        if (toState != -1){
            assert(strLength >= 2);
            for (z = 1; z < strLength; z++){
                char *binChar = extraBitNeeded? bintostrWithExtraBit(string[z], var): bintostr(string[z], var);
                dfaAllocExceptions(1);
                if (z == strLength - 1)
                    dfaStoreException(toState, binChar);
                else
                    dfaStoreException(new_state_counter, binChar);
                dfaStoreState(sink + shiftArray[sink]);
                statuces[new_state_counter - 1] = '-';
                free(binChar);
                new_state_counter++;
            }
        }
        
        
	} // end for each original state
    //    assert(new_state_counter == (num_new_states - 1));
    statuces[num_of_states] = '\0';
	result = dfaBuild(statuces);
    
    free(exeps);
    //	//printf("FREE ToState\n");
	free(to_states);
    //	//printf("FREE STATUCES\n");
	free(statuces);
    free(replacedCharBin);
    free(symbol);
    free(indices);
    free(charachters);
    freeStatePairArrayList(replaceTransitions);
    //    dfaPrintVerbose(result);
    DFA *tmp;
    if(extraBitNeeded){
		if( DEBUG_SIZE_INFO )
			printf("\t peak : replace_char_with_string : states %d : bddnodes %u : before projection \n", result->ns, bdd_size(result->bddm) );
        tmp = dfaProject(result, var);
        dfaFree(result);
		if( DEBUG_SIZE_INFO )
			printf("\t peak : replace_char_with_string : states %d : bddnodes %u : after projection \n", tmp->ns, bdd_size(tmp->bddm) );
        result = dfaMinimize(tmp);
        dfaFree(tmp);
    } else {
		if( DEBUG_SIZE_INFO )
			printf("\t peak : replace_char_with_string : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
        tmp = dfaMinimize(result);
        dfaFree(result);
        result = tmp;
    }
    
    //    dfaPrintVerbose(tmp);
    //	printf("dfaAfterRightTrimBeforeMinimize\n");
    //	dfaPrintGraphviz(result, len, indices);
	return result;

}


int transitionIncludesChar(const char *str, char target, int var){
    int i;
    boolean result;
    result = TRUE;
    char* targetS = bintostr(target, var);
    for(i=0; i<var; i++){
        if(str[i]!='X' && str[i]!=targetS[i]){
            result = FALSE;
            break;
        }
    }
    free(targetS);
    return result;
}


/*
 * if there is a path from state "state" on string "string" that does not lead
 * to sink then return state at end of path otherwise return -1
 */
int stringAcceptedFromState(DFA* M, int state, char* string, int var, int* indices){
   	assert(string != NULL);
    
	int length, i, j, currentState = state;
	paths state_paths, pp;
	trace_descr tp;
	char* symbol;
    bool found = true;

    int sink = find_sink(M);
    assert(sink > -1);
    
	length = (int) strlen(string);
    
	if (length == 0)
		return state;
    
	symbol = (char *) malloc((var + 1) * sizeof(char));
    
    //we stop searching if:
    //1- we finished the sting
    //2- if we hit the sink state
	for (i = 0; i < length && currentState != sink; i++){
        found = false;
		state_paths = pp = make_paths(M->bddm, M->q[currentState]);
		while (pp) {
            for (j = 0; j < var; j++) {
                //the following for loop can be avoided if the indices are in order
                for (tp = pp->trace; tp && (tp->index != indices[j]); tp
                     = tp->next)
                    ;
                if (tp) {
                    if (tp->value)
                        symbol[j] = '1';
                    else
                        symbol[j] = '0';
                } else
                    symbol[j] = 'X';
            }
            symbol[var] = '\0';
            if (transitionIncludesChar(symbol, string[i], var)){
                currentState = pp->to;
                //we found next state so stop searching from current state
                found = true;
                break;
            }
            pp = pp->next;
		}
		kill_paths(state_paths);
        //we must find a transition on current char but it may lead to sink state
        assert(found);
    }
  	
    free(symbol);

    //if we (1) finished the whole string and (2) did not hit the sink state then string is accepted from state
    if (i == length && currentState != sink)
        return currentState;
    else
        return -1;
}

/*
 A state i can go to only one state j on an input string. So from state i there is a maximum of one
 new transition out on replacedChar. This means we will need max 1 extra bit for nondeterminism.
 */
DFA *dfa_pre_replace_char_with_string(DFA *M, int var, int *oldIndices, char replacedChar, char *string){
    if (check_emptiness_minimized(M)){
        return dfaCopy(M);
    }
    assert(string != NULL);
    //assert we do not do delete
    assert(strlen(string) > 0);
    //if replacing a char with itself just copy
    if (strlen(string) == 1 && string[0] == replacedChar){
        return dfaCopy(M);
    }
    DFA *result = NULL;
	char* replacedCharBin = bintostr(replacedChar, var);
    bool extraBitNeeded = false;
    
	paths state_paths, pp;
	trace_descr tp;
    
	int i, j, k, z;
    
	char *exeps;
	int *to_states;
	long max_exeps;
	char *statuces;
	int sink;
    
	char *symbol = (char *) malloc((var + 1) * sizeof(char));
    
	max_exeps = 1 << var; //maybe exponential
	sink = find_sink(M);
	assert(sink > -1);
    
    PStatePairArrayList replaceTransitions = createStatePairArrayList(32, 0);
    
    for (i = 0; i < M->ns; i++){
        int endState = stringAcceptedFromState(M, i, string, var, oldIndices);
        if (endState != -1){
            //string takes us from i to endState
            if (!searchStatePairArrayListBS(replaceTransitions, i, endState, NULL)){
                insertIntoStatePairSortedArrayList(replaceTransitions, i, endState, replacedChar);
            }
            if (!extraBitNeeded && checkExtraBitNeeded(M, var, oldIndices, i, replacedCharBin))
                extraBitNeeded = true;
        }
    }
    
    int len = extraBitNeeded? (var + 1): var;
    int *indices = allocateArbitraryIndex(len);
    
	dfaSetup(M->ns, len, indices); //add one new accept state
	exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
	to_states = (int *) malloc(max_exeps * sizeof(int));
	statuces = (char *) malloc((M->ns + 1) * sizeof(char)); //plus 2, one for the new accept state and one for \0 end of the string
    
#if MORE_WORDS_LESS_NDTRANS == 1
    int numOfChars = 1 << var;
	char **charachters = (char**) malloc(numOfChars * (sizeof(char*)));
    int size = 0;
#endif
    
    
	// for each original state
	for (i = 0; i < M->ns; i++) {
		state_paths = pp = make_paths(M->bddm, M->q[i]);
		k = 0;
		// for each transition out from current state (state i)
		while (pp) {
			if (pp->to != sink) {
				for (j = 0; j < var; j++) {
					//the following for loop can be avoided if the indices are in order
					for (tp = pp->trace; tp && (tp->index != oldIndices[j]); tp =
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
				symbol[var] = '\0';
                
                //Add original transitions
#if MORE_WORDS_LESS_NDTRANS == 0
                to_states[k] = pp->to;
                for (j = 0; j < var; j++)
                    exeps[k * (len + 1) + j] = symbol[j];
                exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
                exeps[k * (len + 1) + len] = '\0';
                k++;
#else
                if (!isIncludeLambda(symbol, replacedCharBin, var)) { // Only Consider Non-lambda case
                    to_states[k] = pp->to;
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = symbol[j];
                    exeps[k * (len + 1) + j] = 'X';//<-- only if len > var this will matter
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                }
                else {
                    removeTransitionOnChar(symbol, replacedCharBin, var, charachters, &size);
                    for (z = 0; z < size; z++)
                    {
                        //						printf("%s, ", charachters[i]);
                        to_states[k] = pp->to;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = charachters[z][j];
                        exeps[k * (len + 1) + j] = 'X';//<-- only if len > var this will matter
                        exeps[k * (len + 1) + len] = '\0';
                        free(charachters[z]);
                        k++;
                    }
                    //					printf("\n");
                    to_states[k] = pp->to;
                    for (j = 0; j < var; j++)
                        exeps[k * (len + 1) + j] = replacedCharBin[j];
                    exeps[k * (len + 1) + j] = '0';//<-- only if len > var this will matter
                    exeps[k * (len + 1) + len] = '\0';
                    k++;
                }
#endif
                
                //check if this state "accepts" input string i.e. there is a path starting from this state
                //on input string
                //if so then add replacedChar transition to last state in that path
                for (z = 0; z < replaceTransitions->index && replaceTransitions->list[z]->first <= i; z++){
                    if (replaceTransitions->list[z]->first == i){
                        to_states[k] = replaceTransitions->list[z]->second;
                        for (j = 0; j < var; j++)
                            exeps[k * (len + 1) + j] = replacedCharBin[j];
                        exeps[k * (len + 1) + var] = '1';
                        exeps[k * (len + 1) + len] = '\0';
                        k++;
                        //assert that there is only one path out of i on string i.e. that accepts string
                        //we do this by checking if there is not next or the next is > i
                        assert(((z+1) == replaceTransitions->index) || replaceTransitions->list[z+1]->first > i);
                    }
                }
                    
            }
			pp = pp->next;
		} //end while
        
		dfaAllocExceptions(k);
		for (k--; k >= 0; k--){
			dfaStoreException(to_states[k], exeps + k * (len + 1));
        }
		dfaStoreState(sink);
        if (M->f[i] == 1)
            statuces[i] = '+';
        else
            statuces[i] = '-';
		kill_paths(state_paths);
	} // end for each original state

    statuces[M->ns] = '\0';
	result = dfaBuild(statuces);
    
        
#if MORE_WORDS_LESS_NDTRANS == 1
    free(charachters);
#endif
    free(exeps);
    //	//printf("FREE ToState\n");
	free(to_states);
    //	//printf("FREE STATUCES\n");
	free(statuces);
    free(replacedCharBin);
    free(symbol);
    free(indices);
    freeStatePairArrayList(replaceTransitions);
    //    dfaPrintVerbose(result);
    DFA *tmp;
    if(extraBitNeeded){
		if( DEBUG_SIZE_INFO )
			printf("\t peak : pre_replace_char_with_string : states %d : bddnodes %u : before projection \n", result->ns, bdd_size(result->bddm) );
        tmp = dfaProject(result, var);
        dfaFree(result);
		if( DEBUG_SIZE_INFO )
			printf("\t peak : pre_replace_char_with_string : states %d : bddnodes %u : after projection \n", tmp->ns, bdd_size(tmp->bddm) );
        result = dfaMinimize(tmp);
        dfaFree(tmp);
    } else {
		if( DEBUG_SIZE_INFO )
			printf("\t peak : pre_replace_char_with_string : states %d : bddnodes %u \n", result->ns, bdd_size(result->bddm) );
        tmp = dfaMinimize(result);
        dfaFree(result);
        result = tmp;
    }
    
    //    dfaPrintVerbose(tmp);
    //	printf("dfaAfterRightTrimBeforeMinimize\n");
    //	dfaPrintGraphviz(result, len, indices);
	return result;
    
}

DFA *dfaHtmlSpecialChars(DFA *inputAuto, int var, int *indices, hscflags_t flags){
    char *lt = "\xfe""lt;";
    char *gt = "\xfe""gt;";
    char *sq = "\xfe""apos;";
    char *dq = "\xfe""quot;";
    DFA *result = NULL;

    DFA *a1 = dfa_replace_char_with_string(inputAuto, var, indices, '<', lt);

    DFA *a2 = dfa_replace_char_with_string(a1, var, indices, '>', gt);
    dfaFree(a1);
    

    if (flags == ENT_QUOTES){
        DFA *a3 = dfa_replace_char_with_string(a2, var, indices, '\'', sq);
        dfaFree(a2);

        DFA *a4 = dfa_replace_char_with_string(a3, var, indices, '"', dq);
        dfaFree(a3);

        DFA *a5 = dfa_replace_char_with_string(a4, var, indices, '&', "&amp;");
        dfaFree(a4);

        result = dfa_replace_char_with_string(a5, var, indices, '\xfe', "&");
        dfaFree(a5);
    }
    
    else if (flags == ENT_COMPAT){
            DFA *a3 = dfa_replace_char_with_string(a2, var, indices, '"', dq);
            dfaFree(a2);

            DFA *a4 = dfa_replace_char_with_string(a3, var, indices, '&', "&amp;");
            dfaFree(a3);

            result = dfa_replace_char_with_string(a4, var, indices, '\xfe', "&");
            dfaFree(a4);

    }
    else {
        DFA *a3 = dfa_replace_char_with_string(a2, var, indices, '&', "&amp;");
        dfaFree(a2);

        result = dfa_replace_char_with_string(a3, var, indices, '\xfe', "&");
        dfaFree(a3);
    }

    return result;
}

DFA *dfaPreHtmlSpecialChars(DFA *inputAuto, int var, int *indices, hscflags_t flags){
    DFA *result = NULL;

    DFA *a1 = dfa_pre_replace_char_with_string(inputAuto, var, indices, '&', "&amp;");
    
    if (flags == ENT_QUOTES){
        DFA *a2 = dfa_pre_replace_char_with_string(a1, var, indices, '"', "&quot;");
        dfaFree(a1);

        DFA *a3 = dfa_pre_replace_char_with_string(a2, var, indices, '\'', "&apos;");
        dfaFree(a2);

        DFA *a4 = dfa_pre_replace_char_with_string(a3, var, indices, '>', "&gt;");
        dfaFree(a3);

        result = dfa_pre_replace_char_with_string(a4, var, indices, '<', "&lt;");
        dfaFree(a4);
    }
    else if (flags == ENT_COMPAT){
        DFA *a2 = dfa_pre_replace_char_with_string(a1, var, indices, '"', "&quot;");
        dfaFree(a1);

        DFA *a3 = dfa_pre_replace_char_with_string(a2, var, indices, '>', "&gt;");
        dfaFree(a2);

        result = dfa_pre_replace_char_with_string(a3, var, indices, '<', "&lt;");
        dfaFree(a3);
    }
    else {
        DFA *a2 = dfa_pre_replace_char_with_string(a1, var, indices, '>', "&gt;");
        dfaFree(a1);

        result = dfa_pre_replace_char_with_string(a2, var, indices, '<', "&lt;");
        dfaFree(a2);
    }
    return result;
}
