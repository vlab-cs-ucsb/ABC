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


#include "stranger.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
//for arithmetic automata
#include <math.h>

//for internal
#include "stranger_lib_internal.h"
#include "utility.h"

//Turn on composite analysis for vul checking
//#define _COMPOSITE_ANALYSIS

/****************************************

 Tool functions

 ****************************************/

char *bintostr(unsigned long n, int k) {
  char *str;

  // no extra bit
  str = (char *) malloc(k + 1);
  str[k] = '\0';

  for (k--; k >= 0; k--) {
    if (n & 1)
      str[k] = '1';
    else
      str[k] = '0';
    if (n > 0)
      n >>= 1;
  }
  //printf("String:%s\n", str);
  return str;
}

char *bintostrWithExtraBit(unsigned long n, int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 2);
  str[k + 1] = '\0';
  str[k] = 'X'; //the last bit dont care

  for (k--; k >= 0; k--) {
    if (n & 1)
      str[k] = '1';
    else
      str[k] = '0';
    n >>= 1;
  }
  //printf("String:%s\n", str);
  return str;
}

char *bintostrWithExtraBits(unsigned long n, int k, int aux) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 2);
  str[k + aux] = '\0';
  for (aux--; aux >= 0; aux--) {
    str[k + aux] = 'X'; //the last bit dont care
  }
  for (k--; k >= 0; k--) {
    if (n & 1)
      str[k] = '1';
    else
      str[k] = '0';
    n >>= 1;
  }
  //printf("String:%s\n", str);
  return str;
}


//Construct DFA accepts one character within [a-b]
DFA *dfa_construct_range(char a, char b, int var, int *indices){
  int n, n1, n2;
  n1 = (int) a;
  n2 = (int) b;
  int i = n2-n1;
  assert(i>=0); //range a-b,
  dfaSetup(3,var,indices);

  //state 0
  dfaAllocExceptions(i+1);
  for(n=n1; n<=n2; n++)
    dfaStoreException(1,bintostr(n, var));
  dfaStoreState(2);

  //state 1
  dfaAllocExceptions(0);
  dfaStoreState(2);

  //state 2
  dfaAllocExceptions(0);
  dfaStoreState(2);

  return dfaBuild("-+-");
}


//Construct DFA From another automaton (author muath)
// n_state is the number of states
// accept_states is a string where if the char at position i is + then state i is accepting, if it is - it is not accepting
// n_trans is the number of transitions in the transitions array
// Each transition in the transition array has a source state, destination state and a range of characters (the range is between firt and last)
// The transition array must be sorted based on the source state
// We create an extra sink state which is the state labeled n_states (so the constructed automaton has n_states+1 states)
DFA *dfa_construct_from_automaton(int n_states, int n_trans, transition* transitions, char* accept_states, int var, int *indices){
  int  n, n1, n2;
  int diff;
  dfaSetup(n_states+1,var,indices);

  int current_state = 0;
  int num_trans;
  int i, j;
  for (i = 0; i < n_trans;) {
    if (transitions[i].source == current_state) {
      num_trans = 0;
      for (j = i; transitions[j].source == current_state && j < n_trans; j++) {
         n1 = (int ) transitions[j].first;
         n2 = (int ) transitions[j].last;
         //printf("first = %d, last = %d\n", n1, n2);
         diff = n2-n1;
         assert(diff>=0);
         num_trans = num_trans+diff+1;
      }

      dfaAllocExceptions(num_trans);

        for (j = i; transitions[j].source == current_state && j < n_trans; j++) {
          n1 = (int ) transitions[j].first;
          n2 = (int ) transitions[j].last;
          diff = n2 - n1;
//          assert(diff>=0);
//          dfaAllocExceptions(diff+1);
          for(n=n1; n<=n2; n++)
             dfaStoreException(transitions[j].dest, bintostr(n, var));
        }
        dfaStoreState(n_states);
        current_state++;
        i = j;
    }
    else {
      dfaAllocExceptions(0);
      dfaStoreState(n_states);
      current_state++;
    }
  }
  for (; current_state <= n_states; current_state++) {
   dfaAllocExceptions(0);
   dfaStoreState(n_states);
  }

  char* acceptance_string = (char*)malloc((n_states+2) * sizeof(char));
  strcpy(acceptance_string, accept_states);
  acceptance_string[n_states] = '-';
  acceptance_string[n_states+1] = '\0';
  return dfaBuild(acceptance_string);
}


void test_dfa_construct_from_automaton(int var, int *indices){
  transition* t = (transition*) malloc(2 * sizeof(transition));
  t[0].source = 0;t[0].dest = 1; t[0].first = 'a'; t[0].last = 'd';
  t[1].source = 0;t[1].dest = 1; t[1].first = 'o'; t[1].last = 'r';
  DFA* result = dfa_construct_from_automaton(2, 2, t , "-+", var, indices);
  dfaPrintVerbose(result);
  printf("Test 1 passed - 1\n");

//  dfaPrintGraphviz(result, var, indices);
  printf("Test 1 passed - 2\n");

  dfaFree(result);
  printf("Test 1 passed - 3\n");

  free(t);
  printf("**************Test 1 passed****************\n\n");

  int num_of_trans = 10;
  t = (transition*) malloc(num_of_trans * sizeof(transition));
  int i = 0;
  t[i].source = 0;t[i].dest = 1; t[i].first = 'a'; t[i++].last = 'd';
  t[i].source = 0;t[i].dest = 1; t[i].first = 'o'; t[i++].last = 'z';
  t[i].source = 1;t[i].dest = 2; t[i].first = 'v'; t[i++].last = 'v';
  t[i].source = 2;t[i].dest = 3; t[i].first = 'c'; t[i++].last = 'd';
  t[i].source = 3;t[i].dest = 4; t[i].first = '6'; t[i++].last = 'm';
  t[i].source = 4;t[i].dest = 3; t[i].first = 'n'; t[i++].last = 'n';
  t[i].source = 4;t[i].dest = 5; t[i].first = '1'; t[i++].last = '6';
  t[i].source = 4;t[i].dest = 5; t[i].first = '7'; t[i++].last = '7';
  t[i].source = 4;t[i].dest = 5; t[i].first = 'B'; t[i++].last = 'D';
  t[i].source = 4;t[i].dest = 5; t[i].first = 'b'; t[i++].last = 'b';
  assert(i== num_of_trans);
  result = dfa_construct_from_automaton(6, num_of_trans, t, "-+--+-", var, indices);
  dfaPrintVerbose(result);
  printf("Test 2 passed - 1\n");

//  dfaPrintGraphviz(result, var, indices);
  printf("Test 2 passed - 2\n");

  dfaFree(result);
  printf("Test 2 passed - 3\n");

  free(t);
  printf("**************Test 2 passed****************\n\n");
}

char *bintostrWithExtraBitsZero(unsigned long n, int k, int aux) {
  char *str;

  str = (char *) malloc(k + aux + 1);
  str[k + aux] = '\0';
  for (aux--; aux >= 0; aux--) {
    str[k + aux] = '0'; //the aux bits initialized 0
  }
  for (k--; k >= 0; k--) {
    if (n & 1)
      str[k] = '1';
    else
      str[k] = '0';
    n >>= 1;
  }
  //printf("Aux String:%s\n", str);
  return str;
}

//Assume that 11111111(255) and 11111110(254) are reserved words in ASCII (the length depends on k)
//Sharp1 is 111111111 which will be used as a reserved symbol
char *getSharp1(int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 1);
  str[k] = '\0';
  for (k--; k >= 0; k--) {
    str[k] = '1';
  }
  //printf("String Sharp 1:%s\n", str);
  return str;
}

//Assume that 11111111(255) and 11111110(254) are reserved words in ASCII, (the length depends on k)
//Sharp0 is 111111110 which will be used as a reserved symbol
char *getSharp0(int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 1);
  str[k] = '\0';
  k--;
  str[k] = '0';
  for (k--; k >= 0; k--) {
    str[k] = '1';
  }
  //printf("String Sharp 1:%s\n", str);
  return str;
}

//Sharp1 is 111111111 which will be used as a reserved symbol
//the length is k+1 and the extra bit is set to 1
char *getSharp1WithExtraBit(int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 2);
  str[k + 1] = '\0';
  str[k] = '1'; //the last bit dont care

  for (k--; k >= 0; k--) {
    str[k] = '1';
  }
  //printf("String Sharp 1:%s\n", str);
  return str;
}

//Sharp0 is 111111110 which will be used as a reserved symbol
//the length is k+1 and the extra bit is set to 1
char *getSharp0WithExtraBit(int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 2);
  str[k + 1] = '\0';
  str[k] = '0'; //the last bit dont care
  k--;
  str[k] = '0';
  for (k--; k >= 0; k--) {
    str[k] = '1';
  }
  //printf("String Sharp 0:%s\n", str);
  return str;
}

//Sharp0 is 111111110 which will be used as a reserved symbol
char *getArbitraryStringWithExtraBit(int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 2);
  str[k + 1] = '\0';
  str[k] = '0'; //the last bit dont care

  for (k--; k >= 0; k--) {
    str[k] = 'X';
  }
  //printf("Arbitrary String :%s\n", str);
  return str;
}

//set less significant bit less priority
int* allocateAscIIIndex(int length) {
  int i;
  int* indices;
  indices = (int *) malloc(length * sizeof(int));
  for (i = 0; i < length; i++)
    indices[i] = i;
  return indices;
}

//set less significant bit less priority
unsigned* allocateAscIIIndexUnsigned(int length) {
  int i;
  unsigned* indices;
  indices = (unsigned *) malloc(length * sizeof(unsigned));
  for (i = 0; i < length; i++)
    indices[i] = i;
  return indices;
}

//set less significant bit less priority
//the extra bit has the less priority
int* allocateAscIIIndexWithExtraBit(int length) {
  int i;
  int* indices;
  indices = (int *) malloc((length + 1) * sizeof(int));
  for (i = 0; i <= length; i++)
    indices[i] = i;
  return indices;
}

int* allocateArbitraryIndex(int length) {
  int i;
  int* indices;
  indices = (int *) malloc((length) * sizeof(int));
  for (i = 0; i < length; i++)
    indices[i] = i;
  return indices;
}

int getVar() {
  return NUM_ASCII_TRACKS;
}

int* getIndices() {
  return allocateAscIIIndexWithExtraBit(NUM_ASCII_TRACKS);
}

//the default sink state is the last state
//int find_sink(DFA *M){
//  return ((M->ns)-1);
//}


//If M is not constructed manually, use the following to find_sink
//Note: the sink state is not the last state after dfaProject
int find_sink(DFA *M) {
  int i;
  for (i = 0; i < M->ns; i++) {
    //printf("Enter find_sink\n");
    //leaf, nowhere, reject
    if (bdd_is_leaf(M->bddm, M->q[i]) && (bdd_leaf_value(M->bddm, M->q[i])
        == i) && (M->f[i] == -1))
      return i;
  }
  //printf("Exit(find sink)\n");
  return -1;
}

//return the position of the highest significant bit
int get_hsig(int i) {
  int sig, n;
  n = i;
  for (sig = 0; n > 0; sig++)
    n >>= 1;
  return sig;
}

void set_bitvalue(char *bit, int length, int value) {
  int i;
  //  bit = (char *) malloc( length*sizeof(char));
  for (i = 0; i < length; i++)
    if (value & (1 << i))
      bit[i] = '1';
    else
      bit[i] = '0';
//  bit[length] = '\0';//causes buffer overrun
  //  printf("\n added bits: %s\n", bit);
}

/********************************************************
 basic list function
 *****************************************************/

struct int_type *new_it(int i) {
  struct int_type *tmp;
  tmp = (struct int_type *) malloc(sizeof(struct int_type));
  tmp->value = i;
  tmp->next = NULL;
  return tmp;
}

struct int_list_type *new_ilt() {
  struct int_list_type *tmp;
  tmp = (struct int_list_type *) malloc(sizeof(struct int_list_type));
  tmp->count = 0;
  tmp->head = tmp->tail = NULL;
  return tmp;
}

struct int_list_type *add_data(list, data)
  struct int_list_type *list;struct int_type *data; {
  if (data == NULL)
    return list;

  if (list == NULL)
    list = new_ilt();
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

int check_value(list, value)
  struct int_list_type *list;int value; {
  struct int_type *tmp = NULL;
  if (list != NULL)
    for (tmp = list->head; tmp != NULL; tmp = tmp->next)
      if (tmp->value == value)
        return 1;
  return 0;
}

struct int_list_type *remove_value(list, value)
  struct int_list_type *list;int value; {
  struct int_type *tmp = NULL;
  struct int_type *del = NULL;
  if (check_value(list, value) > 0) {
    for (tmp = list->head; tmp != NULL; tmp = tmp->next)
      if ((tmp->value == value) && (list->count == 1)) { //remove tmp
        list->count = 0;
        list->head = list->tail = NULL;
        free(tmp);
        return list;
      } else if ((tmp->value == value) && (list->head == tmp)) {
        list->count--;
        list->head = list->head->next;
        free(tmp);
        return list;
      } else if ((tmp->next != NULL) && (tmp->next->value == value)) {
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

int check_data(list, data)
  struct int_list_type *list;struct int_type *data; {
  struct int_type *tmp = NULL;
  if ((list != NULL) && (data != NULL))
    for (tmp = list->head; tmp != NULL; tmp = tmp->next)
      if (tmp->value == data->value)
        return 1;
  return 0;
}

//no duplicate
struct int_list_type *enqueue(list, value)
  struct int_list_type *list;int value; {
  if (!check_value(list, value))
    list = add_data(list, new_it(value));
  return list;
}

int dequeue(list)
  struct int_list_type *list; {
  struct int_type *data = NULL;
  int i;
  if ((list == NULL) || (list->count == 0))
    return -1;
  else
    data = list->head;
  if (list->count == 1) {
    list->count = 0;
    list->head = list->tail = NULL;
  } else {
    list->head = list->head->next;
    list->count--;
  }
  i = data->value;
  free(data);
  return i;
}

void free_ilt(struct int_list_type *list) {
  int tmp = dequeue(list);
  while (tmp != -1)
    tmp = dequeue(list);
  free(list);
}

void print_ilt(struct int_list_type *list) {
  if (list == NULL){
    printf("list is empty.");
    return;
  }

  struct int_type *tmp = list->head;
  while (tmp != NULL) {
    printf("-> %d", tmp->value);
    tmp = tmp->next;
  }
}

/****************************************

 DFA Construct functions

 ****************************************/

// A DFA that accepts everything except for the null (empty) string
DFA *dfaASCIINotNullString(int var, int* indices) {

  //number of states, number of vartiables(tracks), the BDD order of variables
  dfaSetup(2, var, indices);

  //state 0 (init state)
  //0: number of out transitions
  dfaAllocExceptions(0);
  //Since there are no exceptions, all inputs lead to state 1
  dfaStoreState(1);
  //state 1
  dfaAllocExceptions(0);
  dfaStoreState(1);
  //Status of states: '-' manes reject, '+' means accept.
  //Here state 0 is reject and state 1 is accept
  return dfaBuild("-+");
}


// A DFA that accepts nothing (empty language)
DFA *dfaASCIINonString(int var, int *indices) {

  dfaSetup(1, var, indices);

  dfaAllocExceptions(0);
  dfaStoreState(0);

  return dfaBuild("-");
}

// A DFA that accepts only the null (empty) string
DFA *dfaASCIIOnlyNullString(int var, int *indices) {

  dfaSetup(2, var, indices);

  dfaAllocExceptions(0);
  dfaStoreState(1);
  dfaAllocExceptions(0);
  dfaStoreState(1);

  return dfaBuild("+-");
}

// A DFA that accepts Sigma* but no reserver words
DFA *dfaAllString(int var, int *indices) {

  dfaSetup(1, var, indices);

  dfaAllocExceptions(0);
  dfaStoreState(0);
  return dfaBuild("+");
}

// A DFA that accepts all strings (Sigma*) except 11111111 and 111111110
DFA *dfaAllStringASCIIExceptReserveWords(int var, int *indices) {

  dfaSetup(2, var, indices);
  dfaAllocExceptions(2);
  //n = 255; //reserve word for sharp1
  char* sharp1 = getSharp1(var);
  dfaStoreException(1, sharp1);
  free(sharp1); sharp1 = NULL;
  //n = 254;
  char* sharp0 = getSharp0(var);
  dfaStoreException(1, sharp0);
  free(sharp0); sharp0 = NULL;
  dfaStoreState(0);

  dfaAllocExceptions(0);
  dfaStoreState(1);

  return dfaBuild("+-");
}

DFA *dfaSharpStringWithExtraBit(int var, int *indices) {

  char *sharp1;
  sharp1 = getSharp1WithExtraBit(var);
  dfaSetup(2, var + 1, indices);
  dfaAllocExceptions(1);
  dfaStoreException(1, sharp1);
  dfaStoreState(0);
  dfaAllocExceptions(0);
  dfaStoreState(1);

  return dfaBuild("-+");
}

//var is the number of tracks(bit variables)
//indices is the order of variables
// the last state is the sink state

DFA *dfa_construct_char(char a, int var, int *indices) {
  char* binChar;
  binChar = bintostr((unsigned long) a, var);
  dfaSetup(3, var, indices);
  dfaAllocExceptions(2);
  //  dfaStoreException(0, bintostr((unsigned long) a, var)); //test for nondeterminstic
  dfaStoreException(1, binChar);
  dfaStoreState(2);
  dfaAllocExceptions(0);
  dfaStoreState(2);
  dfaAllocExceptions(0);
  dfaStoreState(2);
  free(binChar);
  return dfaBuild("-+-");
}

DFA *dfa_construct_char_extrabit(char a, int var, int *indices) {
  char* binChar;
  binChar = bintostr((unsigned long) a, var);
  dfaSetup(3, var + 1, indices);
  dfaAllocExceptions(2);
  //  dfaStoreException(0, bintostr((unsigned long) a, var)); //test for nondeterminstic
  dfaStoreException(1, binChar);
  dfaStoreState(2);
  dfaAllocExceptions(0);
  dfaStoreState(2);
  dfaAllocExceptions(0);
  dfaStoreState(2);
  free(binChar);
  return dfaBuild("-+-");
}
//TODO baki finals is not terminated check for problems
DFA *dfa_construct_string(char *reg, int var, int *indices) {
  int i;
  char *finals;
  char* binChar;
  DFA* result;
  int len = (int) strlen(reg);
  finals = (char *) malloc((len + 2) * sizeof(char));
  dfaSetup(len + 2, var, indices);
  for (i = 0; i < len; i++) {
    dfaAllocExceptions(1);
    binChar = bintostr((unsigned long) reg[i], var);
    dfaStoreException(i + 1, binChar);
    free(binChar);
    dfaStoreState(len + 1);
    finals[i] = '-';
  }
  dfaAllocExceptions(0);
  dfaStoreState(len + 1);
  finals[len] = '+';
  assert(len == i);
  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(len + 1);
  finals[len + 1] = '-';

  result = dfaBuild(finals);
  free(finals);
  return result;
}

DFA* dfa_construct_set_of_strings(char** set, int size, int var, int* indices){
  DFA *tmp, *tmp2, *result;
  int i;
  result = dfaASCIINonString(var, indices);
  for (i = 0; i < size; i++){
    tmp = dfa_construct_string(set[i], var, indices);
    tmp2 = dfa_union_with_emptycheck(tmp, result, var, indices);
    dfaFree(tmp); tmp = NULL;
    dfaFree(result); result = NULL;
    result = tmp2;
  }
  return result;
}

DFA *dfa_construct_string_extrabit(char *reg, int var, int *indices) {
  int i;
  char *finals;
  char* binChar;
  DFA* result;
  int len = (int)strlen(reg);
  finals = (char *) malloc((len + 2) * sizeof(char));
  dfaSetup(len + 2, var + 1, indices);
  for (i = 0; i < len; i++) {
    dfaAllocExceptions(1);
    binChar = bintostrWithExtraBit((unsigned long) reg[i], var);
    //printf("INPUT: %c at the position %d \n", reg[i], i);
    dfaStoreException(i + 1, binChar);
    dfaStoreState(len + 1);
    finals[i] = '0';
    free(binChar);
  }
  dfaAllocExceptions(0);
  dfaStoreState(len + 1);
  finals[len] = '+';
  assert(len==i);
  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(len + 1);
  finals[len + 1] = '-';

  result = dfaBuild(finals);
  free(finals);
  return result;
}

//Output M, so that L(M)= reg*
DFA *dfa_construct_string_closure(char *reg, int var, int *indices) {
  int i;
  char *finals;
  char* binChar;
  DFA* result;
  int len = (int) strlen(reg);

  finals = (char *) malloc((len + 2) * sizeof(char));
  dfaSetup(len + 2, var, indices);
  for (i = 0; i < len; i++) {
    dfaAllocExceptions(1);
    binChar = bintostr((unsigned long) reg[i], var);
    //printf("INPUT: %c at the position %d \n", reg[i], i);
    dfaStoreException(i + 1, binChar);
    dfaStoreState(len + 1);
    finals[i] = '0';
    free(binChar);
  }
  dfaAllocExceptions(1);
  //printf("INPUT: %c at the accept position %d \n", reg[0], i);
  dfaStoreException(1, bintostr((unsigned long) reg[0], var));
  dfaStoreState(len + 1);
  finals[len] = '+';
  assert(len==i);
  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(len + 1);
  finals[len + 1] = '-';

  result = dfaBuild(finals);
  free(finals);
  return result;
}

DFA *dfa_construct_string_closure_extrabit(char *reg, int var, int *indices) {
  int i;
  char *finals;
  int len = (int) strlen(reg);
  finals = (char *) malloc((len + 2) * sizeof(char));
  dfaSetup(len + 2, var + 1, indices);
  for (i = 0; i < len; i++) {
    dfaAllocExceptions(1);
    //printf("INPUT: %c at the position %d \n", reg[i], i);
    dfaStoreException(i + 1, bintostrWithExtraBit((unsigned long) reg[i],
        var));
    dfaStoreState(len + 1);
    finals[i] = '0';
  }
  dfaAllocExceptions(1);
  //printf("INPUT: %c at the accept position %d \n", reg[0], i);
  dfaStoreException(1, bintostrWithExtraBit((unsigned long) reg[0], var));
  dfaStoreState(len + 1);
  finals[len] = '+';
  assert(len==i);
  //sink state
  dfaAllocExceptions(0);
  dfaStoreState(len + 1);
  finals[len + 1] = '-';

  return dfaBuild(finals);
}

/**
 Constructs and automaton that accepts any string s where |s| is in the 
 set "lengths".
 Lengths must be a set of integers with at least one element.
 If the set is ordered then set ordered to true to avoid ordering
 */
DFA *dfaSigmaLengthsSet(unsigned *lengths, const unsigned size, bool sorted, int var, int *indices){
    int i, numOfStates;
    char *statuces;
    DFA *result=NULL;
    
    assert(lengths != NULL && size > 0);
    
    if (!sorted){
        qsort(lengths, size, sizeof(unsigned), intcmpfunc);
    }
    unsigned upperBound = lengths[size - 1];//largest length
    
    numOfStates = upperBound + 2; //add one sink state
    statuces=(char *)malloc((numOfStates+1)*sizeof(char));
    dfaSetup(numOfStates,var,indices);
    
    for( i = 0; i <= upperBound; i++){
        dfaAllocExceptions(0);
        dfaStoreState(i+1);
        if(findStateBS(lengths, i, 0, size - 1)) statuces[i]='+';
        else statuces[i]='-';
    }
    //the sink state
    dfaAllocExceptions(0);
    dfaStoreState(i);
    statuces[i]='-'; 
    statuces[numOfStates]='\0';
    
    
    result=dfaBuild(statuces);
    //dfaPrintVerbose(result);
    free(statuces);
    DFA *tmp = dfaMinimize(result);
    dfaFree(result);
    return tmp;
}

// for INTERNAL use.
//Given M, output a dfa accepting L(M) u \{\empty\}
// not needed anymore. better use dfa_union_with_emptycheck
DFA *dfa_union_empty_M(DFA *M, int var, int *indices) {
  DFA *result;
  if (state_reachable(M, M->s, var, indices)==1)
    result = dfa_union_add_empty_M(M, var, indices);
  else { //no edge enters initial state, simply changing the initial state to be acceptable
    result = dfaCopy(M);
    result->f[result->s] = 1;
  }
  return result;
}

// DO NOT USE. Does not handle empty string correctly.
// use dfa_union_with_emptycheck instead
DFA *dfa_union(M1, M2)
DFA *M1;DFA *M2; {
  DFA *result, *tmp;
  result = dfaProduct(M1, M2, dfaOR);
    tmp = dfaMinimize(result);
    dfaFree(result);
    return tmp;
}

/*
 * checks if one of the two is empty string to call
 * union_with_empty other wise it just does the union
 * regardless.
 */
DFA *dfa_union_with_emptycheck(DFA* M1, DFA* M2, int var, int* indices){
  DFA* tmpM = dfaProduct(M1, M2, dfaOR);
  if( DEBUG_SIZE_INFO )
    printf("\t peak : union : states %d : bddnodes %u \n", tmpM->ns, bdd_size(tmpM->bddm) );
  DFA *result = dfaMinimize(tmpM);
  dfaFree(tmpM);tmpM = NULL;
  if(checkEmptyString(M1)||checkEmptyString(M2)){
    tmpM = dfa_union_empty_M(result, var, indices);
    dfaFree(result); result = NULL;
    result = tmpM;
  }
  return result;
}

DFA *dfa_intersect(M1, M2)
  DFA *M1;DFA *M2; {
  DFA *result, *tmpM;
  tmpM = dfaProduct(M1, M2, dfaAND);
  if( DEBUG_SIZE_INFO )
    printf("\t peak : intersect : states %d : bddnodes %u \n", tmpM->ns, bdd_size(tmpM->bddm) );
  result = dfaMinimize(tmpM);
  dfaFree(tmpM);
  return result;
}

DFA *dfa_negate(M1, var, indices)
  DFA *M1;int var;int *indices; {
  DFA *result, *tmpM3;
  DFA *tmpM1 = dfaAllStringASCIIExceptReserveWords(var, indices);
  DFA *tmpM2 = dfaCopy(M1);
  dfaNegation(tmpM2);
  tmpM3 = dfaProduct(tmpM1, tmpM2, dfaAND);
  dfaFree(tmpM1);
  dfaFree(tmpM2);
  if( DEBUG_SIZE_INFO )
    printf("\t peak : negate : states %d : bddnodes %u \n", tmpM3->ns, bdd_size(tmpM3->bddm) );
  result = dfaMinimize(tmpM3);
  dfaFree(tmpM3);
  return result;
}

//Output M, so that L(M)={w+| w \in L(M1)}
//Need to use extra bit to model NFA to DFA
//NOTE: IF no conflict, no need to use exra bit
// 1. Construct added paths (0->k, k is not sink)
// 2. For each f[i] is true, for each added path 0->k, add i to k
//    The extra bit is set 0 for old paths, while the extra bit is set 1 for new paths
// 3. Project extra bit away

DFA *dfa_closure_extrabit(M1, var, indices)
  DFA *M1;int var;int *indices; {
  DFA *result;
  DFA *tmpM;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, ka, numOfAddedPaths;
  char *exeps;
  char *addedexeps;
  int *to_states;
  int *added_to_states;
  int sink;
  long max_exeps;
  char *statuces;
  int len;
  len = var + 1; //one extra bit

  max_exeps = 1 << len; //maybe exponential
  sink = find_sink(M1);
  assert(sink>-1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(M1->ns, len, indices);
  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  addedexeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  added_to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((M1->ns + 1) * sizeof(char));

  //construct the added paths
  state_paths = pp = make_paths(M1->bddm, M1->q[M1->s]);
  //printf("\n\n INIT %d \n\n", M1->s);

  k = 0;
  while (pp) {
    if (pp->to != sink) {
      added_to_states[k] = pp->to;
      for (j = 0; j < var; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp
            = tp->next)
          ;
        if (tp) {
          if (tp->value)
            addedexeps[k * (len + 1) + j] = '1';
          else
            addedexeps[k * (len + 1) + j] = '0';
        } else
          addedexeps[k * (len + 1) + j] = 'X';
      }
      addedexeps[k * (len + 1) + var] = '1'; //new path
      addedexeps[k * (len + 1) + len] = '\0';
      k++;
    }
    pp = pp->next;
  }
  kill_paths(state_paths);
  numOfAddedPaths = k; //ka is the number of new paths
  if(_FANG_DFA_DEBUG) printf("\n\n FANG: Concat NUMBER OF ADDED PATHS %d \n\n", numOfAddedPaths);

  for (i = 0; i < M1->ns; i++) {

    state_paths = pp = make_paths(M1->bddm, M1->q[i]);
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
        exeps[k * (len + 1) + var] = '0'; //old value
        exeps[k * (len + 1) + len] = '\0';
        k++;
      }
      pp = pp->next;
    }
    if (M1->f[i] == 1) { //add added paths
      ka = numOfAddedPaths;
      dfaAllocExceptions(k + ka);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (len + 1));
      for (ka--; ka >= 0; ka--)
        dfaStoreException(added_to_states[ka], addedexeps + ka * (len
            + 1));
      dfaStoreState(sink);
      statuces[i] = '+';
    } else {
      dfaAllocExceptions(k);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (len + 1));
      dfaStoreState(sink);
      if (M1->f[i] == -1)
        statuces[i] = '-';
      else
        statuces[i] = '0';
    }
    kill_paths(state_paths);
  }
  statuces[i] = '\0';
  //result = dfaBuild(statuces);
  tmpM = dfaBuild(statuces);
  result = dfaProject(tmpM, (unsigned) var); //var is the index of the extra bit
  free(exeps);
  free(addedexeps);
  free(to_states);
  free(added_to_states);
  free(statuces);
  dfaFree(tmpM);
  return dfaMinimize(result);

} // END dfa_closure_extrabit

//Output M, so that L(M) is {w1w2| w1 \in L(M1) and w2 \in L(M2)}
//Need to use extra bit to model NFA to DFA
//NOTE: IF no conflict, no need to use exra bit
// 1. Construct added paths ((M2->s)->k, k is not sink)
// 2. For each f[i] is true, for each added path (M2->s)->k, add i to k
//    The extra bit is set 0 for old paths, while the extra bit is set 1 for new paths
// 3. Project extra bit away

int check_init_reachable(M, var, indices)
  DFA *M;int var;int *indices; {
  paths state_paths, pp;
  int i;

  for (i = 0; i < M->ns; i++) {
    if (M->f[i] == 1) {
      state_paths = pp = make_paths(M->bddm, M->q[i]);
      while (pp) {
        if (pp->to == M->s)
          return 1;
        pp = pp->next;
      }
      kill_paths(state_paths);
    }
  }
  return 0;
}

DFA *dfa_concat_extrabit(M1, M2, var, indices)
       DFA *M1;
       DFA *M2;
       int var;
       int *indices;
  {
    DFA *result;
    DFA *tmpM;
    paths state_paths, pp;
    trace_descr tp;
    int i, j, k, ka, numOfAddedPaths;
    char *exeps;
    char *addedexeps;
    int *to_states;
    int *added_to_states;
    long max_exeps;
    char *statuces;
    int len, shift, newns, sink1, sink2;
    int initflag = check_init_reachable(M2, var, indices);
    int loc;
    len = var+1; //one extra bit
    shift = M1->ns; // map M2 transitions to new M


    if(len <= 10) max_exeps=1<<len; //maybe exponential
    else max_exeps = 1<< 10; //saving for multi-track bounded for 25 bits
    sink1=find_sink(M1);
    sink2=find_sink(M2);
    assert(sink1 >-1);
    assert(sink2 >-1);

    newns= (M1->ns)+(M2->ns)-1-(1-initflag); //number of states after concatenation. The sink state of M2 is merged.

    dfaSetup(newns, len, indices); //the sink state of M2 is merged to M1
    exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
    addedexeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
    to_states=(int *)malloc(max_exeps*sizeof(int));
    added_to_states=(int *)malloc(max_exeps*sizeof(int));
    statuces=(char *)malloc((newns+1)*sizeof(char));

    //construct the added paths
    state_paths = pp = make_paths(M2->bddm, M2->q[M2->s]);
    //printf("\n\n INIT2 %d \n\n", M2->s);

    k=0;
    while (pp) {
      if(pp->to!=sink2){

        added_to_states[k]=pp->to+shift;
        if ( M2->s == pp->to) {
          // BAKI: avoid self loop bug
          // example (concat "a" /b*c/)
          added_to_states[k] -= 2;
        } else {
          if(sink2>=0 && ((pp->to) > sink2)) added_to_states[k]--; //to new state, sink state will be eliminated and hence need -1
          if(initflag == 0 && ((pp->to)> M2->s)) added_to_states[k]--; // to new state, init state will be eliminated if init is not reachable
        }


        for (j = 0; j < var; j++) {
          //the following for loop can be avoided if the indices are in order
          for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);
          if (tp) {
            if (tp->value) addedexeps[k*(len+1)+j]='1';
            else addedexeps[k*(len+1)+j]='0';
          }
          else
            addedexeps[k*(len+1)+j]='X';
        }
        addedexeps[k*(len+1)+var]='1'; //new path
        addedexeps[k*(len+1)+len]='\0';
        k++;
      }
      pp = pp->next;
    }
    kill_paths(state_paths);
    numOfAddedPaths=k; //numOfAddedPaths is the number of new paths
    //printf("\n\n NUMBER OF ADDED PATHS %ld \n\n", numOfAddedPaths);

    for (i = 0; i < M1->ns; i++) {

      state_paths = pp = make_paths(M1->bddm, M1->q[i]);
      k=0;

      while (pp) {
        if(pp->to!=sink1){
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
    exeps[k*(len+1)+var]='0'; //old value
    exeps[k*(len+1)+len]='\0';
    k++;
        }
        pp = pp->next;
      }
      if(M1->f[i]==1){ //add added paths
        ka = numOfAddedPaths;
        dfaAllocExceptions(k+ka);
        for(k--;k>=0;k--)
    dfaStoreException(to_states[k],exeps+k*(len+1));
        for(ka--;ka>=0;ka--)
    dfaStoreException(added_to_states[ka],addedexeps+ka*(len+1));
        dfaStoreState(sink1);
        // BAKI: empty string acceptance on the right hand side
        if ( M2->f[0] == 1 ) {
          statuces[i] = '+';
        } else {
          statuces[i] = '-';
        }
      } else{
        dfaAllocExceptions(k);
        for(k--;k>=0;k--)
    dfaStoreException(to_states[k],exeps+k*(len+1));
        dfaStoreState(sink1);
        statuces[i]='-';
      }
      kill_paths(state_paths);
    }
    //REUSE exeps and to_states shall be fine
      free(exeps);
      free(to_states);
      exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
      to_states=(int *)malloc(max_exeps*sizeof(int));
    //  initflag is 1 iff init is reached by some state. In this case,

    for (i = 0; i < M2->ns; i++) {
      if(i!=sink2){
        if(i!=M2->s || initflag>0){
    state_paths = pp = make_paths(M2->bddm, M2->q[i]);
    k=0;

    while (pp) {
      if((pp->to)!=sink2){
        to_states[k]=pp->to+shift;
        if(sink2>=0 && ((pp->to) > sink2)) to_states[k]--; //to new state, sink state will be eliminated and hence need -1
        if(initflag == 0 && ((pp->to)> M2->s)) to_states[k]--; // to new state, init state will be eliminated if init is not reachable

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
        exeps[k*(len+1)+var]='0'; //old value
        exeps[k*(len+1)+len]='\0';
        k++;
      }
      pp = pp->next;
    }

    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(to_states[k],exeps+k*(len+1));
    dfaStoreState(sink1);

    loc = shift+i;
    if(initflag == 0 && i > M2->s) loc--;
    if(sink2>=0 && i>sink2) loc--;

    if(M2->f[i]==1)
      statuces[loc]='+';
    else if(M2->f[i]==-1)
      statuces[loc]='-';
    else
      statuces[loc]='-';

    kill_paths(state_paths);
        }
      }
    }
    statuces[newns]='\0';
    //assert(i+shift==newns);

    //result = dfaBuild(statuces);
    //printf("START TO CONCAT BUILD\n");
    tmpM=dfaBuild(statuces);
    //dfaMinimize(tmpM);
    //dfaPrintVitals(tmpM);

    //printf("START TO PROJECT\n");
  if( DEBUG_SIZE_INFO )
    printf("\t peak : concat : states %d : bddnodes %u : before projection \n", tmpM->ns, bdd_size(tmpM->bddm) );
    result=dfaProject(tmpM, (unsigned) var);
    //dfaPrintVerbose(result);

    //printf("FREE EXEPS\n");
    free(exeps);
    //printf("FREE ADDEDEXEPS\n");
    free(addedexeps);
    //printf("FREE ToState\n");
    free(to_states);
    //printf("FREE AddedToState\n");
    free(added_to_states);
    //printf("FREE STATUCES\n");
    free(statuces);
    dfaFree(tmpM);
  if( DEBUG_SIZE_INFO )
    printf("\t peak : concat : states %d : bddnodes %u : after projection \n", result->ns, bdd_size(result->bddm) );
      tmpM = dfaMinimize(result);
        dfaFree(result);
        return tmpM;
  }//End of dfa_concat_extrabit




  //Given M, output a dfa accepting L(M) but initial state is not an accepting state
  DFA *dfa_shift_empty_M(DFA *M, int var, int *indices)
  {
    DFA *result;
    paths state_paths, pp;
    trace_descr tp;
    int i, j, k;
    char *exeps;
    char *addedexeps;
    int *to_states;
    int *added_to_states;
    int sink;
    long max_exeps;
    char *statuces;
    int len;
    int ns = M->ns+1;
    int shift = 1;
    len = var; //one extra bit

    if(len <= 10) max_exeps=1<<len;
    else max_exeps = 1<<10;//maybe exponential
    sink=find_sink(M);
    assert(sink >-1);
    //printf("\n\n SINK %d\n\n\n", sink);

    dfaSetup(ns, len, indices);
    exeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
    addedexeps=(char *)malloc(max_exeps*(len+1)*sizeof(char));
    to_states=(int *)malloc(max_exeps*sizeof(int));
    added_to_states=(int *)malloc(max_exeps*sizeof(int));
    statuces=(char *)malloc((ns+1)*sizeof(char));

    //construct the added paths for the initial state
    state_paths = pp = make_paths(M->bddm, M->q[M->s]);
    //printf("\n\n INIT %d \n\n", M1->s);

    k=0;
    while (pp) {
      if(pp->to!=sink){
        added_to_states[k]=pp->to+shift;
        for(j = 0; j < var; j++) {
          //the following for loop can be avoided if the indices are in order
          for (tp = pp->trace; tp && (tp->index != indices[j]); tp =tp->next);
          if (tp) {
            if (tp->value) addedexeps[k*(len+1)+j]='1';
            else addedexeps[k*(len+1)+j]='0';
          }
          else
            addedexeps[k*(len+1)+j]='X';
        }
        addedexeps[k*(len+1)+len]='\0';
        k++;
      }
      pp = pp->next;
    }
    kill_paths(state_paths);

    //initial state
    dfaAllocExceptions(k);
    for(k--;k>=0;k--)
      dfaStoreException(added_to_states[k],addedexeps+k*(len+1));
    dfaStoreState(sink+shift);
    statuces[0]='-';


    //M
    for (i = 0; i < M->ns; i++) {

      state_paths = pp = make_paths(M->bddm, M->q[i]);
      k=0;

      while (pp) {
        if(pp->to!=sink){
    to_states[k]=pp->to+shift;
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
    exeps[k*(len+1)+var]='1'; //old value
    exeps[k*(len+1)+len]='\0';
    k++;
        }
        pp = pp->next;
      }
      dfaAllocExceptions(k);
      for(k--;k>=0;k--)
        dfaStoreException(to_states[k],exeps+k*(len+1));
      dfaStoreState(sink+shift);
      if(M->f[i]==-1)
        statuces[i+shift]='-';
      else if (M->f[i]==1)
        statuces[i+shift]='+';
      else statuces[i+shift]='-';

      kill_paths(state_paths);
    }
    statuces[ns]='\0';
    //result = dfaBuild(statuces);
    result=dfaBuild(statuces);
    //dfaPrintVitals(result);
    //printf("Original M\n");
    //dfaPrintVerbose(M);

    //printf("Union empty with M\n");
    //dfaPrintVerbose(result);

    free(exeps);
    free(addedexeps);
    free(to_states);
    free(added_to_states);
    free(statuces);
    return dfaMinimize(result);
  }



  //Considering empty string for concat
  /**
   * Baki: added only empty string checks, watch for efficiency
   */
  DFA *dfa_concat(M1, M2, var, indices)
       DFA *M1;
       DFA *M2;
       int var;
       int *indices;
  {
    DFA *tmp0 = NULL;
    DFA *tmp1 = NULL;

    if (checkOnlyEmptyString(M1, var, indices)) {
      return dfaCopy(M2);
    }

    if (checkOnlyEmptyString(M2, var, indices)) {
      return dfaCopy(M1);
    }

    if(checkEmptyString(M2)){
      if(state_reachable(M2, M2->s, var, indices)){
        tmp1 = dfa_shift_empty_M(M2, var, indices);
        tmp0 =  dfa_concat_extrabit(M1, tmp1, var, indices);
        dfaFree(tmp1);
      }
      else{
        tmp0 =  dfa_concat_extrabit(M1, M2, var, indices);
      }
      tmp1 = dfa_union(tmp0, M1);
      dfaFree(tmp0);
    }else{
      tmp1 = dfa_concat_extrabit(M1, M2, var, indices);
    }
    return tmp1;
  }
////Take Output DFA
//DFA *dfa_replace(M1, M2, M3, var, indices)
//  DFA *M1;DFA *M2;DFA *M3;int var;int *indices; {
//
//  DFA *result = NULL;
//  //NEED TO IMPLEMENT
//  //Construct the following DFA
//
//  result = dfaASCIINotNullString(var, indices);
//  return result;
//}

//Output M so that L(M)={w|w=x0#1\bar{x1}#2.., where x0x1... \in L(M1)}
DFA *dfa_replace_step1_duplicate(DFA *M, int var, int *indices) {
  DFA* result;
    DFA *temp;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, duplicate_id;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len, shift, newns, sink;
  char *sharp1;
  char *sharp0;
  sharp1 = getSharp1WithExtraBit(var);
  sharp0 = getSharp0WithExtraBit(var);
  len = var + 1; //one extra bit
  shift = M->ns; // map M2 transitions to new M
  newns = 2 * (M->ns) - 1; //number of states after duplicate. The sink state is not duplicated.

  max_exeps = 1 << len; //maybe exponential
  sink = find_sink(M);
  assert(sink>-1);

  dfaSetup(newns, len, indices);
  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((newns + 1) * sizeof(char));

  for (i = 0; i < M->ns; i++) {

    if (i != sink) {
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
          exeps[k * (len + 1) + var] = '0'; //old value
          exeps[k * (len + 1) + len] = '\0';
          k++;
        }
        pp = pp->next;
      }
      dfaAllocExceptions(k + 1);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (len + 1));
      if (i > sink)
        dfaStoreException(i + shift - 1, sharp1);
      else
        dfaStoreException(i + shift, sharp1);

      dfaStoreState(sink);

      if (M->f[i] == 1)
        statuces[i] = '+';
      else if (M->f[i] == -1)
        statuces[i] = '-';
      else
        statuces[i] = '0';
      kill_paths(state_paths);
    } else {
      dfaAllocExceptions(0);
      dfaStoreState(sink);
      statuces[i] = '-';
    }
  }

  for (i = 0; i < M->ns; i++) {
    if (i != sink) {
      state_paths = pp = make_paths(M->bddm, M->q[i]);
      k = 0;

      while (pp) {
        if ((pp->to) != sink) {
          if ((pp->to) > sink)
            to_states[k] = pp->to + shift - 1; //to new state, sink state will be eliminated and hence need -1
          else
            to_states[k] = pp->to + shift; //to new state

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
          exeps[k * (len + 1) + var] = '1'; //bar value
          exeps[k * (len + 1) + len] = '\0';
          k++;
        }
        pp = pp->next;
      }

      dfaAllocExceptions(k + 1);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (len + 1));
      dfaStoreException(i, sharp0);
      dfaStoreState(sink);
      duplicate_id = i + shift;
      if (i > sink) {
        duplicate_id--;
      }
      if (M->f[i] == 1)
        statuces[duplicate_id] = '0';
      else if (M->f[i] == -1)
        statuces[duplicate_id] = '-';
      else
        statuces[duplicate_id] = '0';
      kill_paths(state_paths);
    } else if (sink < M->ns - 1) {
      if (M->f[sink + 1] == -1) {
        statuces[sink + shift] = '-';
      } else {
        statuces[sink + shift] = '0';
      }
    }
  }

  statuces[newns] = '\0';
  //assert(i+shift == newns);
  temp = dfaBuild(statuces);
  //dfaPrintVitals(result);
  //printf("FREE EXEPS\n");
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);
  //dfaFree(tmpM);
    result = dfaMinimize(temp);
    dfaFree(temp);

  return result;
} //END dfa_replace_step1_duplicate


//Given M, output a DFA accepting S*.w.S* where w \in M
DFA *dfa_star_M_star(DFA *M, int var, int *indices) {
  DFA *result;
  DFA *tmpM;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k;
  char *exeps;
  char *addedexeps;
  int *to_states;
  int *added_to_states;
  int sink;
  long max_exeps;
  char *statuces;
  int len;
  int ns = M->ns + 1;
  int shift = 1;
  char *arbitrary = getArbitraryStringWithExtraBit(var);
  len = var + 1; //one extra bit

  max_exeps = 1 << len; //maybe exponential
  sink = find_sink(M);
  assert(sink>-1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(ns, len, indices);
  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  addedexeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  added_to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((ns + 1) * sizeof(char));

  //construct the added paths for the initial state
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  //printf("\n\n INIT %d \n\n", M1->s);

  k = 0;
  while (pp) {
    if (pp->to != sink) {
      added_to_states[k] = pp->to + shift;
      for (j = 0; j < var; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp
            = tp->next)
          ;
        if (tp) {
          if (tp->value)
            addedexeps[k * (len + 1) + j] = '1';
          else
            addedexeps[k * (len + 1) + j] = '0';
        } else
          addedexeps[k * (len + 1) + j] = 'X';
      }
      addedexeps[k * (len + 1) + var] = '1'; //new path
      addedexeps[k * (len + 1) + len] = '\0';
      k++;
    }
    pp = pp->next;
  }
  kill_paths(state_paths);

  //initial state
  dfaAllocExceptions(k + 1);
  for (k--; k >= 0; k--)
    dfaStoreException(added_to_states[k], addedexeps + k * (len + 1));
  dfaStoreException(0, arbitrary);
  dfaStoreState(sink + shift);
  statuces[0] = '0';

  //M
  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k = 0;

    while (pp) {
      if (pp->to != sink) {
        to_states[k] = pp->to + shift;
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
        exeps[k * (len + 1) + var] = '1'; //old value
        exeps[k * (len + 1) + len] = '\0';
        k++;
      }
      pp = pp->next;
    }
    if (M->f[i] == 1) { //add added paths
      dfaAllocExceptions(k + 1);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (len + 1));
      dfaStoreException(i + shift, arbitrary); //for appending S* for the final state
      dfaStoreState(sink + shift);
      statuces[i + shift] = '+';
    } else {
      dfaAllocExceptions(k);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (len + 1));
      dfaStoreState(sink + shift);
      if (M->f[i] == -1)
        statuces[i + shift] = '-';
      else
        statuces[i + shift] = '0';
    }
    kill_paths(state_paths);
  }
  statuces[ns] = '\0';
  //result = dfaBuild(statuces);
  tmpM = dfaBuild(statuces);
  //dfaPrintVitals(tmpM);
  //printf("Original M\n");
  //dfaPrintVerbose(M);
  //printf("Star M Star\n");
  //dfaPrintVerbose(tmpM);

  result = dfaProject(tmpM, (unsigned) var); //var is the index of the extra bit
  //printf("Projection of Star M Star\n");
  //dfaPrintVerbose(result);

  free(exeps);
  free(addedexeps);
  free(to_states);
  free(added_to_states);
  free(statuces);
    free(arbitrary);
  dfaFree(tmpM);
    tmpM = dfaMinimize(result);
    dfaFree(result);
  return tmpM;

}

//return 1 if dest can be reached from some state
int state_reachable(DFA *M, int dest, int var, int *indices) {
  paths state_paths, pp;
  int i;
  assert(dest < M->ns);
  for (i = 0; i < M->ns; i++) {
    state_paths = pp = make_paths(M->bddm, M->q[i]); // one step
    while (pp) {
      if (pp->to == dest)
        return 1;
      pp = pp->next;
    }
    kill_paths(state_paths);
  }
  return 0;
}

//Given M, output a dfa accepting L(M) u \{\empty\}
DFA *dfa_union_add_empty_M(DFA *M, int var, int *indices) {
  DFA *result;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k;
  char *exeps;
  char *addedexeps;
  int *to_states;
  int *added_to_states;
  int sink;
  long max_exeps;
  char *statuces;
  int len;
  int ns = M->ns + 1;
  int shift = 1;

  len = var;

  max_exeps = 1 << len; //maybe exponential
  sink = find_sink(M);
  assert(sink>-1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(ns, len, indices);
  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  addedexeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  added_to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((ns + 1) * sizeof(char));

  //construct the added paths for the initial state
  state_paths = pp = make_paths(M->bddm, M->q[M->s]);
  //printf("\n\n INIT %d \n\n", M1->s);

  k = 0;
  while (pp) {
    if (pp->to != sink) {
      added_to_states[k] = pp->to + shift;
      for (j = 0; j < var; j++) {
        //the following for loop can be avoided if the indices are in order
        for (tp = pp->trace; tp && (tp->index != indices[j]); tp
            = tp->next)
          ;
        if (tp) {
          if (tp->value)
            addedexeps[k * (len + 1) + j] = '1';
          else
            addedexeps[k * (len + 1) + j] = '0';
        } else
          addedexeps[k * (len + 1) + j] = 'X';
      }
      addedexeps[k * (len + 1) + len] = '\0';
      k++;
    }
    pp = pp->next;
  }
  kill_paths(state_paths);

  //initial state
  dfaAllocExceptions(k);
  for (k--; k >= 0; k--)
    dfaStoreException(added_to_states[k], addedexeps + k * (len + 1));
  dfaStoreState(sink + shift);
  statuces[0] = '+';

  //M
  for (i = 0; i < M->ns; i++) {

    state_paths = pp = make_paths(M->bddm, M->q[i]);
    k = 0;

    while (pp) {
      if (pp->to != sink) {
        to_states[k] = pp->to + shift;
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
        exeps[k * (len + 1) + len] = '\0';
        k++;
      }
      pp = pp->next;
    }
    dfaAllocExceptions(k);
    for (k--; k >= 0; k--)
      dfaStoreException(to_states[k], exeps + k * (len + 1));
    dfaStoreState(sink + shift);
    if (M->f[i] == -1)
      statuces[i + shift] = '-';
    else if (M->f[i] == 1)
      statuces[i + shift] = '+';
    else
      statuces[i + shift] = '0';

    kill_paths(state_paths);
  }
  statuces[ns] = '\0';
  //result = dfaBuild(statuces);
  DFA* tmpM = dfaBuild(statuces);
  //dfaPrintVitals(result);

  free(exeps);
  free(addedexeps);
  free(to_states);
  free(added_to_states);
  free(statuces);
  //changed by Muath --
//  return dfaMinimize(result); --> old
  result = dfaMinimize(tmpM);
  dfaFree(tmpM);tmpM = NULL;
  return result;
  //end change by Muath
}



//Output M so that L(M)={w|w=x0#1\bar{x1}#2.., where \bar{x_i} \in L(M), x_i is \in the compliment of L(S*MS*)}

DFA *dfa_replace_step2_match_compliment(DFA *M, int var, int *indices) {
  DFA *result;
    DFA *temp;
  DFA *M_neg;
  DFA *M_tneg;
  //  DFA *M_e;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, y, k;
  char *exeps;
  int *to_states;
  long max_exeps;
  char *statuces;
  int len, shift, newns, sink, sink_M_neg;
  char *sharp1;
  char *sharp0;
  sharp1 = getSharp1WithExtraBit(var);
  sharp0 = getSharp0WithExtraBit(var);

  /*  //Union empty string via MONA
   M_e = dfaASCIIOnlyNullString(); //null string
   printf("NULL string\n");
   dfaPrintVerbose(M_e);


   M_tneg = dfa_star_M_star(M, var, indices);
   dfaNegation(M_tneg);
   printf("The Compliment of Star M Star\n");
   dfaPrintVerbose(M_tneg);

   M_neg = dfaProduct(M_tneg, M_e, dfaOR);
   printf("Compliment Union NULL string\n");
   dfaPrintVerbose(M_neg);
   */

  M_tneg = dfa_star_M_star(M, var, indices);
  dfaNegation(M_tneg);
  //printf("The Compliment of Star M Star\n");
  //dfaPrintVerbose(M_tneg);

  //Union empty string manually
  M_neg = dfa_union_empty_M(M_tneg, var, indices);
  //printf("Compliment Union NULL string\n");
  //dfaPrintVerbose(M_neg);

  sink_M_neg = find_sink(M_neg);
  if (sink_M_neg < 0) {
    //THERE IS no SINK STATES
    //printf("No Sink of M_neg :[%d]\n", sink_M_neg);
    shift = M_neg->ns; // map M transitions to new M
    newns = M->ns + M_neg->ns; //number of states for new M. Note that there maybe no sink state in M_neg.
  } else {
    //THERE IS no SINK STATES
    //printf("Sink of M_neg :[%d] will be removed.\n", sink_M_neg);
    shift = M_neg->ns - 1; // map M transitions to new M
    newns = M->ns + M_neg->ns - 1; //number of states for new M. Note that there maybe no sink state in M_neg.
  }

  len = var + 1; //one extra bit for bar

  max_exeps = 1 << len; //maybe exponential
  sink = find_sink(M);
  assert(sink>-1);
  sink += shift;

  dfaSetup(newns, len, indices);
  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((newns + 1) * sizeof(char));

  //the initial state
  for (i = 0, y = 0; i < M_neg->ns; i++) {
    if (i != sink_M_neg) {
      state_paths = pp = make_paths(M_neg->bddm, M_neg->q[i]);
      k = 0;

      while (pp) {
        if (pp->to != sink_M_neg) {
          if (pp->to > sink_M_neg)
            to_states[k] = pp->to - 1;
          else
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
          exeps[k * (len + 1) + var] = '0'; //original value
          exeps[k * (len + 1) + len] = '\0';
          k++;
        }
        pp = pp->next;
      }

      if (M_neg->f[i] == 1) {
        dfaAllocExceptions(k + 1);
        for (k--; k >= 0; k--)
          dfaStoreException(to_states[k], exeps + k * (len + 1));
        dfaStoreException(shift, sharp1);
        dfaStoreState(sink);
        statuces[y] = '+';
      } else {
        dfaAllocExceptions(k);
        for (k--; k >= 0; k--)
          dfaStoreException(to_states[k], exeps + k * (len + 1));
        dfaStoreState(sink);
        if (M_neg->f[i] == -1)
          statuces[y + shift] = '-';
        else
          statuces[y + shift] = '0';
      }
      kill_paths(state_paths);
      y++; //y is the number of visited non sink states
    }
    /*    else {
     //if M_neg exists sink state
     dfaAllocExceptions(0);
     dfaStoreState(sink);
     statuces[i]='0';
     }
     */
  }
  if (sink_M_neg < 0)
    assert(y==M_neg->ns);
  else
    assert(y+1==M_neg->ns);

  for (i = 0; i < M->ns; i++) {
    if (i != sink - shift) {
      state_paths = pp = make_paths(M->bddm, M->q[i]);
      k = 0;

      while (pp) {
        if (pp->to != sink - shift) {
          to_states[k] = pp->to + shift;
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
          exeps[k * (len + 1) + var] = '1'; //bar value
          exeps[k * (len + 1) + len] = '\0';
          k++;
        }
        pp = pp->next;
      }

      if (M->f[i] == 1) {
        dfaAllocExceptions(k + 1);
        for (k--; k >= 0; k--)
          dfaStoreException(to_states[k], exeps + k * (len + 1));
        dfaStoreException(0, sharp0); //add sharp1 to the initial state of M
        dfaStoreState(sink);
        statuces[i + shift] = '0';
      } else {
        dfaAllocExceptions(k);
        for (k--; k >= 0; k--)
          dfaStoreException(to_states[k], exeps + k * (len + 1));
        dfaStoreState(sink);
        if (M->f[i] == -1)
          statuces[i + shift] = '-';
        else
          statuces[i + shift] = '0';
      }
      kill_paths(state_paths);
    } else { //sink state
      dfaAllocExceptions(0);
      dfaStoreState(sink);
      statuces[i + shift] = '-';
    }
  }
  statuces[newns] = '\0';
  assert(i+shift == newns);
  temp = dfaBuild(statuces);
  //dfaPrintVitals(result);
  //printf("FREE EXEPS\n");
  free(exeps);
  //printf("FREE ToState\n");
  free(to_states);
  //printf("FREE STATUCES\n");
  free(statuces);
  dfaFree(M_neg);
  dfaFree(M_tneg);
  //dfaFree(M_e);
    result = dfaMinimize(temp);
    dfaFree(temp);
  return result;
} //END dfa_replace_step2_match_negation

//type==1
//search the first reachable state from sharp1 bar sharp2
//type ==2
//search the longest reachable state from sharp1 bar sharp2


void initial_visited_states(int *visited, int n) {
  int i;
  visited = (int *) malloc(n * sizeof(int));
  for (i = 0; i < n; i++)
    visited[i] = 0;
}

//reachable states from \bar* sharp0;
struct int_list_type *reachable_closure(DFA *M, int start, int var,
    int *indices) {

  paths state_paths, pp;
  trace_descr tp;
  int j, sink, current;
  struct int_list_type *worklist = NULL;
  struct int_list_type *finallist = NULL;
  int finalflag = 1;
  char *sharp0 = getSharp0WithExtraBit(var);
  int *visited = (int *) malloc(M->ns * sizeof(int));
  for (j = 0; j < M->ns; j++)
    visited[j] = 0;

  sink = find_sink(M);
  assert(sink>-1);

  worklist = enqueue(worklist, start);

  while (worklist->count > 0) {
    current = dequeue(worklist);
    visited[current] = 1;
    assert(current!=-1);
    state_paths = pp = make_paths(M->bddm, M->q[current]);
    while (pp) {
      if (pp->to != sink) {
        //find the path that may contain 111111101
        for (j = 0; j < var + 1; j++) {
          //the following for loop can be avoided if the indices are in order
          for (tp = pp->trace; tp && (tp->index != j); tp = tp->next)
            ;

          if (tp) {
            if (tp->value) {
              if (sharp0[j] == '0')
                finalflag = 0;
            } else {
              if (sharp0[j] == '1')
                finalflag = 0;
            }
          }
        }
        if (finalflag != 0)
          finallist = enqueue(finallist, pp->to);

        for (tp = pp->trace; tp && (tp->index != var); tp = tp->next)
          ;
        if (((tp && tp->value) || !tp) && (visited[pp->to] == 0)
            && (finalflag == 0))
          worklist = enqueue(worklist, pp->to);
      }
      pp = pp->next;
      finalflag = 1;
    }
        kill_paths(state_paths);
  }
    free_ilt(worklist);
    free(visited);
    free(sharp0);
  return finallist;
}

//for each state reachable from sharp1, find its reachable_closure

int exist_sharp1_path(DFA *M, int start, int var) {
  paths state_paths, pp;
  trace_descr tp;
  int j, sink;
  int finalflag = 1;
  int *indices = allocateAscIIIndexWithExtraBit(var);
  char *sharp1 = getSharp1WithExtraBit(var);
  //printf("Get Sharp1 %s\n", sharp1);
  sink = find_sink(M);
  assert(sink>-1);
  //printf("Find sink in sharp1: %d\n", sink);
  assert(start < M->ns);

  if (start == sink){
        free(indices);
        free(sharp1);
    return -1;
    }
  else {
    state_paths = pp = make_paths(M->bddm, M->q[start]);

    while (pp) {
      if (pp->to != sink) {
        //find the path that may contain 111111111
        for (j = 0; j < var + 1; j++) {
          //the following for loop can be avoided if the indices are in order
          for (tp = pp->trace; tp && (tp->index != j); tp = tp->next)
            ;
          if (tp) {
            if (tp->value) {
              //printf("TP value true\n");
              if (sharp1[j] == '0')
                finalflag = 0;
            } else {
              if (sharp1[j] == '1')
                finalflag = 0;
            }
          }
        }
        if (finalflag != 0) {
          free(indices);
                    free(sharp1);
                    int toState = pp->to;
                    kill_paths(state_paths);
          return toState;
        }
      }
      pp = pp->next;
      finalflag = 1;
    }
        kill_paths(state_paths);
  }
  free(indices);
    free(sharp1);
  return -1;
}

struct int_list_type **get_match(DFA *M, int var, int *indices) {
  int i, next;
  struct int_list_type **result;
  result = (struct int_list_type **) malloc((M->ns)
      * sizeof(struct int_list_type *));
  for (i = 0; i < M->ns; i++) {
    next = exist_sharp1_path(M, i, var);
    if (next > -1)
      result[i] = reachable_closure(M, next, var, indices);//result[i]= reachable_closure(M, next, var, indices);
    else
      result[i] = new_ilt();
  }
  return result;
}

struct int_list_type **get_match_exclude_self(DFA *M, int var, int *indices) {
  int i, next;
  struct int_list_type **result;
  result = (struct int_list_type **) malloc((M->ns)
      * sizeof(struct int_list_type *));
  for (i = 0; i < M->ns; i++) {
    //printf("Start exist sharp1\n");
    next = exist_sharp1_path(M, i, var);
    //printf("End exist sharp1: state[%d]\n", next);
    if (next > -1) //result[i]= remove_value(reachable_closure(M, next, var, indices), i);
      result[i] = reachable_closure(M, next, var, indices);
    else
      result[i] = new_ilt();
  }
  return result;
}


//space is 0010 0000
char *getSpace(int k) {
  char *str;

  // add one extra bit for later used
  str = (char *) malloc(k + 1);
  str[k] = '\0';
  for (k--; k >= 0; k--) {
    str[k] = (k == 2)?  '1' : '0';
  }
  //printf("String Sharp 1:%s\n", str);
  return str;
}

DFA *dfaRemoveSpace(DFA* M, int var, int* indices){
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
  char* lambda = getSpace(var);

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




/*********************************************

 Functions for Composite Verification on Strings and Integers

 Fang 06/30/2008

 1) Prefix(DFA M, c_1, c_2)  Output M' so that L(M')={w| w'\in \Sigma*, ww' \in L(M), |w|<c_2 }
 2) Suffix(DFA M, c_1, c_2)  Output M' so that L(M')={w| w'\in \Sigma^{c_1}, w'w \in L(M) }
 3) Minimal(DFA M)
 4) Maximal(DFA M)
*/

/**********************************************/

// A DFA that accepts only one arbitrary character
DFA *dfaDot(int var, int *indices){

   dfaSetup(3,var,indices);

   dfaAllocExceptions(2);
   dfaStoreException(2, getSharp1(var));
   dfaStoreException(2, getSharp0(var));
   dfaStoreState(1);
   dfaAllocExceptions(0);
   dfaStoreState(2);
   dfaAllocExceptions(0);
   dfaStoreState(2);

   return dfaBuild("-+-");
}


// A DFA that accepts only emty or one arbitrary character
DFA *dfaQuestionMark(int var, int *indices){

   dfaSetup(3,var,indices);

   dfaAllocExceptions(2);
   dfaStoreException(2, getSharp1(var));
   dfaStoreException(2, getSharp0(var));
   dfaStoreState(1);
   dfaAllocExceptions(0);
   dfaStoreState(2);
   dfaAllocExceptions(0);
   dfaStoreState(2);

   return dfaBuild("++-");
}
 /**********************************************/

// A DFA that accepts everything within the length from c1 to c2
//c2 = -1, indicates unbounded upperbound
//c1 = -1, indicates unbounded lowerbound
//
//DFA *dfaSigmaC1toC2(int c1, int c2, int var, int* indices){
//
//   int i, n;
//   char *statuces;
//   DFA *result=NULL;
//
//   if(c2<=-1){ //accept everything after c1 steps
//
//     n=c1+1;
//     statuces=(char *)malloc((n+1)*sizeof(char));
//     dfaSetup(n,var,indices);
//     //the 0 to c1-1 states(unaccepted)
//     for( i=0; i<c1; i++){
//       dfaAllocExceptions(0);
//       dfaStoreState(i+1);
//       statuces[i]='-';
//     }
//     //the c1 state
//     dfaAllocExceptions(0);
//     dfaStoreState(i);
//     statuces[i]='+'; //i==c1
//     statuces[n]='\0'; //n==c1+1
//
//   }else if(c1<=-1){
//
//     n=c2+2; //add one sink state
//     statuces=(char *)malloc((n+1)*sizeof(char));
//     dfaSetup(n,var,indices);
//     //the 0 to c2 states(accepted)
//     for( i=0; i<=c2; i++){
//       dfaAllocExceptions(0);
//       dfaStoreState(i+1);
//       statuces[i]='+';
//     }
//     //the c1 state
//     dfaAllocExceptions(0);
//     dfaStoreState(i);
//     statuces[i]='-'; //i==c2
//     statuces[n]='\0'; //n==c1+1
//
//
//   }else {
//   assert(c2>=c1);
//     n=c2+2; //add one sink state
//     statuces=(char *)malloc((n+1)*sizeof(char));
//     dfaSetup(n,var,indices);
//     //the 0 to c2 states(accepted)
//     for( i=0; i<=c2; i++){
//       dfaAllocExceptions(0);
//       dfaStoreState(i+1);
//       if(i>=c1) statuces[i]='+';
//       else statuces[i]='-';
//     }
//     //the c1 state
//     dfaAllocExceptions(0);
//     dfaStoreState(i);
//     statuces[i]='-'; //i==c2
//     statuces[n]='\0'; //n==c1+1
//   }
//
//   result=dfaBuild(statuces);
//   //dfaPrintVerbose(result);
//   free(statuces);
//   if(c1==0) result->f[result->s]=1;
//   return dfaMinimize(result);
//
//} //end of dfaSigmaC1toC2
//
//
//DFA *dfa_Prefix(DFA *M, int c1, int c2, int var, int* indices) //Output M' so that L(M')={w| w'\in \Sigma*, ww' \in L(M), c_1 <= |w|<=c_2 }
//{
//  int i, sink;
//  DFA *M1 = dfaSigmaC1toC2(c1, c2, var, indices);
//  DFA *M2 = dfaCopy(M);
//  //dfaPrintVerbose(M2);
//  sink = find_sink(M);
//  for (i = 0; i < M2->ns; i++) {
//    if (i != sink)
//      M2->f[i] = 1;
//  }
//  //dfaPrintVerbose(M2);
//  DFA *result = dfa_intersect(M2, M1);
//  //dfaPrintVerbose(result);
//  dfaFree(M1);
//  dfaFree(M2);
//  return dfaMinimize(result);
//
//}//end of prefix
//
//
//struct int_list_type *reachable_states_bounded_steps(DFA *M, int c1, int c2) {
//
//  paths state_paths, pp;
//  int current;
//  int steps;
//  int sink = find_sink(M);
//
//  struct int_list_type *worklist = NULL;
//  struct int_list_type *nextlist = NULL;
//  struct int_list_type *finallist = NULL;
//
//  worklist = enqueue(worklist, M->s);
//
//  for (steps = 1; steps <= c2; steps++) {
//    while (worklist->count > 0) {
//      current = dequeue(worklist); //dequeue returns the int value instead of the struct
//      state_paths = pp = make_paths(M->bddm, M->q[current]);
//      while (pp) {
//        if (pp->to != sink) {
//          nextlist = enqueue(nextlist, pp->to);
//          if (steps >= c1)
//            finallist = enqueue(finallist, pp->to);
//        }
//        pp = pp->next;
//      }
//    }
//    free(worklist);
//    worklist = nextlist;
//    nextlist = NULL;
//  }
//
//  print_ilt(finallist);
//  return finallist;
//}
//
//int check_accept(DFA *M, struct int_list_type *states) {
//
//  int i;
//  struct int_type *tmpState = states->head;
//  assert(states != NULL);
//  for (i = 0; i < states->count; i++) {
//    if (tmpState != NULL)
//      if (M->f[tmpState->value] > 0)
//        return 1;
//  }
//  return 0;
//}

//DFA *dfa_Suffix(DFA *M, int c1, int c2, int var, int *oldindices) {
//  DFA *result = NULL;
//  DFA *tmpM = NULL;
//  int aux = 0;
//  struct int_list_type *states = NULL;
//  struct int_type *tmpState = NULL;
//
//  int maxCount = 0;
//
//  int *indices = oldindices; //indices is updated if you need to add auxiliary bits
//
//  paths state_paths, pp;
//  trace_descr tp;
//
//  int i, j, z;
//
//  char *exeps;
//  int *to_states;
//  long max_exeps, k;
//  char *statuces;
//  int len = var;
//  int sink;
//
//  char *auxbit = NULL;
//
//  //  char *apath =bintostr(a, var);
//
//  states = reachable_states_bounded_steps(M, c1, c2);
//  maxCount = states->count;
//
//  if (maxCount > 0) { //Need auxiliary bits when there exist some outgoing edges
//    aux = get_hsig(maxCount);
//    printf(
//        "\n There are %d reachable states, need to add %d auxiliary bits\n",
//        maxCount, aux);
//    auxbit = (char *) malloc(aux * sizeof(char));
//    len = var + aux; // extra aux bits
//    indices = allocateArbitraryIndex(len);
//  }
//
//  max_exeps = 1 << len; //maybe exponential
//  sink = find_sink(M);
//  assert(sink>-1);
//
//  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
//
//
//  dfaSetup(M->ns + 1, len, indices); //add one new initial state
//  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
//  to_states = (int *) malloc(max_exeps * sizeof(int));
//  statuces = (char *) malloc((M->ns + 2) * sizeof(char));
//
//  //printf("Before Replace Char\n");
//  //dfaPrintVerbose(M);
//
//  k = 0;
//  //setup for the initial state
//  tmpState = states->head;
//  for (z = 1; z <= states->count; z++) {
//    state_paths = pp = make_paths(M->bddm, M->q[tmpState->value]);
//    while (pp) {
//      if (pp->to != sink) {
//        to_states[k] = pp->to + 1; //insert itself as the initial state
//        for (j = 0; j < var; j++) {
//          //the following for loop can be avoided if the indices are in order
//          for (tp = pp->trace; tp && (tp->index != indices[j]); tp
//              = tp->next)
//            ;
//          if (tp) {
//            if (tp->value)
//              exeps[k * (len + 1) + j] = '1';
//            else
//              exeps[k * (len + 1) + j] = '0';
//          } else {
//            exeps[k * (len + 1) + j] = 'X';
//          }
//        }
//        set_bitvalue(auxbit, aux, z); // aux = 3, z=4, auxbit 001
//        for (j = var; j < len; j++) { //set to xxxxxxxx100
//          exeps[k * (len + 1) + j] = auxbit[len - j - 1];
//        }
//        exeps[k * (len + 1) + len] = '\0';
//        k++;
//      }
//      pp = pp->next;
//    }//end while
//    kill_paths(state_paths);
//    tmpState = tmpState->next;
//  } //end for
//
//  dfaAllocExceptions(k);
//  for (k--; k >= 0; k--)
//    dfaStoreException(to_states[k], exeps + k * (len + 1));
//  dfaStoreState(sink + 1);
//
//  if (check_accept(M, states))
//    statuces[0] = '+';
//  else
//    statuces[0] = '0';
//
//  //for the rest of states (shift one state)
//  for (i = 0; i < M->ns; i++) {
//
//    state_paths = pp = make_paths(M->bddm, M->q[i]);
//    k = 0;
//
//    while (pp) {
//      if (pp->to != sink) {
//        for (tp = pp->trace; tp && (tp->index != indices[var]); tp
//            = tp->next)
//          ; //find the bar value
//        if (!tp || !(tp->value)) {
//          to_states[k] = pp->to + 1;
//          for (j = 0; j < var; j++) {
//            //the following for loop can be avoided if the indices are in order
//            for (tp = pp->trace; tp && (tp->index != indices[j]); tp
//                = tp->next)
//              ;
//
//            if (tp) {
//              if (tp->value)
//                exeps[k * (len + 1) + j] = '1';
//              else
//                exeps[k * (len + 1) + j] = '0';
//            } else
//              exeps[k * (len + 1) + j] = 'X';
//          }
//          for (j = var; j < len; j++) {
//            exeps[k * (len + 1) + j] = '0';
//          }
//          exeps[k * (len + 1) + len] = '\0';
//          k++;
//        }
//      }
//      pp = pp->next;
//    }//end while
//
//    dfaAllocExceptions(k);
//    for (k--; k >= 0; k--)
//      dfaStoreException(to_states[k], exeps + k * (len + 1));
//    dfaStoreState(sink + 1);
//
//    if (M->f[i] == 1)
//      statuces[i + 1] = '+';
//    else if (M->f[i] == -1)
//      statuces[i + 1] = '-';
//    else
//      statuces[i + 1] = '0';
//
//    kill_paths(state_paths);
//  }
//
//  statuces[M->ns + 1] = '\0';
//  result = dfaBuild(statuces);
//  //  dfaPrintVerbose(result);
//  for (i = 0; i < aux; i++) {
//    j = len - i - 1;
//    tmpM = dfaProject(result, (unsigned) j);
//    result = dfaMinimize(tmpM);
//    //    printf("\n After projecting away %d bits", j);
//    //    dfaPrintVerbose(result);
//  }
//  free(exeps);
//  //printf("FREE ToState\n");
//  free(to_states);
//  //printf("FREE STATUCES\n");
//  free(statuces);
//
//  if (maxCount > 0)
//    free(auxbit);
//
//  free_ilt(states);
//
//  return dfaMinimize(result);
//
//}

/*********************************************

 Verfication Function

 **********************************************/
/**
 if automaton is guaranteed to be minimized then this check
 is very quick
 */
bool check_emptiness_minimized(DFA *M){
    return (M->ns == 1 && M->f[M->s] == -1)? true : false;
}

int check_emptiness(M1, var, indices)
DFA *M1;int var;int *indices; {
  if (M1->f[M1->s] == 1)
    return false;
    if (M1->ns == 1 && M1->f[M1->s] == -1)
        return true;
    
    
  char *satisfyingexample = NULL;
  int i;
//  unsigned *uindices = (unsigned *) malloc((var+1) * sizeof(unsigned));
  unsigned *uindices = (unsigned *) calloc((var+1), sizeof(unsigned));
  //conver int to unsigned
  for (i = 0; i < var; i++)
    uindices[i] = (indices[i] <= 0 ? 0 : indices[i]);
  uindices[i] = '\0';
    
  satisfyingexample = dfaMakeExample(M1, 1, var, uindices);
    
  mem_free(uindices);
    int result = ((satisfyingexample == NULL) ? 1 : 0);
    free(satisfyingexample);
    return result;
}

int check_intersection(M1, M2, var, indices)
  DFA *M1;DFA *M2;int var;int *indices; {
  DFA *M;
  int result;
  M = dfa_intersect(M1, M2);
  result = 1 - check_emptiness(M, var, indices);
  dfaFree(M);
  return result;
}

int check_equivalence(M1, M2, var, indices)
  DFA *M1;DFA *M2;int var;int *indices; {
  DFA *M[4];
  int result, i;

  M[0] = dfaProduct(M1, M2, dfaIMPL);
  M[1] = dfaProduct(M2, M1, dfaIMPL);
  M[2] = dfa_intersect(M[0], M[1]);
  M[3] = dfa_negate(M[2], var, indices);
  result = check_emptiness(M[3], var, indices);

  for (i = 0; i < 4; i++)
    dfaFree(M[i]);

  return result;
}

/*
 * returns true if M2 includes M1 i.e.
 * L(M1) subset_of L(M2)
 */
int check_inclusion(M1, M2, var, indices)
  DFA *M1;DFA *M2;int var;int *indices; {
  DFA *M, *tmp;
  int result;
  tmp = dfa_negate(M2, var, indices);
  M = dfa_intersect(M1, tmp);
  dfaFree(tmp); tmp = NULL;
  result = check_emptiness(M, var, indices);
  dfaFree(M);
  return result;
}

/**
 * converts mona binary char representation into an ascii char
 * Example: input: "01000001" --> output: 'A'
 */
unsigned char strtobin(char* binChar, int var){
  // no extra bit
  char* str = binChar;
  int k = var;
  unsigned char c = 0;
  for (k = 0; k < var; k++) {
    if (str[k] == '1')
      c |= 1;
    else
      c |= 0;
    if (k < (var-1))
      c <<= 1;
  }
  return c;
}

/**
 * Muath documentation:
 * returns a list of states containing each state s that has at least one transition on lambda
 * into it and one transition on non-lambda out of it (except for sink state which is ignored)
 * end Muath documentation
 */
char *isSingleton(DFA *M, int var, int* indices){
    if (check_emptiness(M, var, indices))
        return NULL;
    if (checkOnlyEmptyString(M, var, indices))
        return "";
  paths state_paths, pp;
  trace_descr tp;
  int j, i, current, next, singleTransOut;
//    char *result = (char*) malloc(M->ns * sizeof(char));
  char *result = (char*) calloc(M->ns, sizeof(char));
//  char *symbol = (char*) malloc((var + 1) * sizeof(char));
  char *symbol = (char*) calloc((var + 1), sizeof(char));
  int sink = find_sink(M);
  struct int_list_type *visited=NULL;
  for (i = 0, current = 0, singleTransOut = TRUE; singleTransOut == TRUE && current != -1; current = next, i++){
    singleTransOut = TRUE;
        next = -1;
    state_paths = pp = make_paths(M->bddm, M->q[current]);
    while (pp && singleTransOut) {
      if(pp->to != sink){
        // construct transition from current to pp->to and store it in symbol
        for (j = 0; j < var; j++) {
                    //This loop is to order only
          for (tp = pp->trace; tp && (tp->index != indices[j]); tp = tp->next);
                    //if current bit is X then more than one char in this transition
          if (tp){
                        if (tp->value)
                            symbol[j] = '1';
                        else
                            symbol[j] = '0';
                    }
                    else
                        singleTransOut = FALSE;
                    
        }
                symbol[var] = '\0';
                result[i] = strtobin(symbol, var);
                //if we have only one char on this transition
                if (singleTransOut){
                    //if we have not seen any next state
                    if (next == -1){
                        if (current == pp->to)
                            singleTransOut = FALSE;
                        else
                            next = pp->to;
                    }
                    //if next state is not the same as previous next state then more than one transitino
                    else if (next != pp->to)
                        singleTransOut = FALSE;
                }
      }
      pp = pp->next;
    }
        kill_paths(state_paths);
        if (singleTransOut == TRUE && next != -1){
            //if loop is found then no singleton
            if (check_value(visited, next)){
                singleTransOut = FALSE;
            }
            else
                visited = enqueue(visited, next);
        }
  }

    if (visited != NULL)
        free_ilt(visited);
    free(symbol);
    if (singleTransOut == TRUE){
        assert(i < M->ns);
        result[i] = '\0';
        return result;
    }
    else{
        free(result);
        return NULL;
    }
}


/*
 * check if dfa accepts empty string
 */
int checkEmptyString(DFA *M){
  return ((M->f[M->s])==1) ? 1 : 0;
}

/*
 * check if dfa accepts only empty string
 */
int checkOnlyEmptyString(DFA *M, int var, int* indices){
  DFA *emptyString = dfaASCIIOnlyNullString(var, indices);
  return check_equivalence(M, emptyString, var, indices);
}


int isTransitionIncludeChar(const char *str, char target, int var){
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
 * checks if string element_of L(M)
 */
int checkMembership(DFA* M, char* string, int var, int* indices){
  int length, i, j, endState;
  paths state_paths, pp;
  trace_descr tp;
  char* symbol;
  boolean found;

  assert(string != NULL);

  length = (int) strlen(string);

  if (length == 0)
    return checkEmptyString(M);

  symbol = (char *) malloc((var + 1) * sizeof(char));
  endState = M->s;

  for (i = 0; i < length; i++){
    found = FALSE;
    state_paths = pp = make_paths(M->bddm, M->q[endState]);
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
        if (isTransitionIncludeChar(symbol, string[i], var)){
          endState = pp->to;
          found = TRUE;
          break;
        }

        pp = pp->next;
    }
    kill_paths(state_paths);
    assert(found);
  }

  free(symbol);

  return ((M->f[endState])==1) ? 1 : 0;;
}

/**
 * Given char ci, fills s with ASCII decimal value of n as a
 * string.
 * s: must not be null, allocated before to be of size >= 4
 */
void charToAsciiDigits(unsigned char ci, char s[])
{
    int i, j;
    unsigned char c;
    assert(s != NULL);
    i = 0;
    do {       /* generate digits in reverse order */
        s[i++] = ci % 10 + '0';   /* get next digit */
    } while ((ci /= 10) > 0);     /* delete it */

    s[i] = '\0';
  for (i = 0, j = (int)strlen(s)-1; i<j; i++, j--) {
    c = s[i];
    s[i] = s[j];
    s[j] = c;
  }
}

/**
 * give a char c, returns its ASCII value in asciiVal
 * as a string of length <= 3. For non printable chars
 * it returns their ascii chart value according to ascii table or
 * their decimal value if above 126.
 * asciiVal must be allocated before with size >= 4
 */
void charToAscii(char* asciiVal, unsigned char c){
  int i = 0;
  assert(asciiVal != NULL);
  char* charName[] = {"NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS ", "HT ", "LF ", "VT ", "FF ", "CR ", "SO ", "SI ", "DLE",
      "DC1", "DC2", "CD3", "DC4", "NAK", "SYN", "ETB", "CAN", "EM ", "SUB", "ESC", "FS ", "GS ", "RS ", "US "};
  if (c < 32){
    strcpy(asciiVal, charName[(int)c]);
    return;
  }
  else if (c > 126){
    charToAsciiDigits(c, asciiVal);
    assert(strlen(asciiVal) == 3);
    return;
  }
  else {
    switch(c){
      case ' ': // ' ' -> \\s
        asciiVal[i++] = '\\';
        asciiVal[i++] = '\\';
        asciiVal[i++] = 's';
        break;
      case '\t': // ' ' -> \\t
        asciiVal[i++] = '\\';
        asciiVal[i++] = '\\';//needed to escape first back slash for dot file parser
        asciiVal[i++] = 't';
        break;
      case '"':
        asciiVal[i++] = '\\';//needed to escape double quote for dot file parser
        asciiVal[i++] = '"';
        break;
      case '\\':
        asciiVal[i++] = '\\';
        asciiVal[i++] = '\\';//needed to escape first back slash for dot file parser
        break;
      default:
        asciiVal[i++] = c;
    }
    asciiVal[i] = '\0';
    return;
  }

}

/**
 * given two characters returns a string (char*) range == "[firstChar-lastChar]"
 */
void fillOutCharRange(char* range, char firstChar, char lastChar){
  int i = 0;
  if (firstChar == lastChar){
    charToAscii(range, firstChar);
    assert(strlen(range) <= 3);
    return;
  }

  char* char1 = (char*)(malloc ((4) * (sizeof(char))));
  char* char2 = (char*)(malloc ((4) * (sizeof(char))));
  //[firstChar-lastChar]
  range[i++] = '[';

  //put first char in range
  charToAscii(char1, firstChar);
  assert(strlen(char1) <= 3);
  strncpy(range+i, char1, strlen(char1));
  i += strlen(char1);
  range[i++] = '-';
  //put second char in range
  charToAscii(char2, lastChar);
  assert(strlen(char2) <= 3);
  strncpy(range+i, char2, strlen(char2));
  i += strlen(char2);

  range[i++] = ']';

  range[i] = '\0';
  assert(strlen(range) <= 9);

  free(char1);
  free(char2);
}









void getTransitionCharsHelper(pCharPair result[], char* transitions, int* indexInResult, int currentBit, int var){
  int i;
  boolean allX;
  if (transitions[currentBit] == 'X')
  {
    allX = TRUE;
    for (i = currentBit + 1; i < var; i++){
      if (transitions[i] != 'X'){
        allX = FALSE;
        break;
      }
    }
    if (allX == FALSE){
      transitions[currentBit] = '0';
      getTransitionCharsHelper(result, transitions, indexInResult, currentBit, var);
      transitions[currentBit] = '1';
      getTransitionCharsHelper(result, transitions, indexInResult, currentBit, var);
      transitions[currentBit] = 'X';
    }
    else {
      // convert to a char range (c1,cn)
      pCharPair charPairPtr = (pCharPair) malloc(sizeof(CharPair));
      char* firstBin = (char*) malloc((var+1)*(sizeof (char)));
      char* lastBin = (char*) malloc((var+1)*(sizeof (char)));
      // fill up prev bits
      for (i = 0; i < currentBit; i++){
        lastBin[i] = firstBin[i] = transitions[i];
      }
      // fill up first with 0's and last with 1's
      for (i = currentBit; i < var; i++){
        firstBin[i] = '0';
        lastBin[i] = '1';
      }
      lastBin[var] = firstBin[var] = '\0';
      char firstChar = strtobin(firstBin, var);
      char lastChar = strtobin(lastBin, var);
      charPairPtr->first = firstChar;
      charPairPtr->last = lastChar;
      result[*indexInResult] = charPairPtr;
      (*indexInResult)++;
      free(firstBin);
      free(lastBin);
    }

  }

  else if (currentBit == (var - 1))
  {
    // convert into a single char pair (c,c)
    pCharPair charPairPtr = (pCharPair) malloc(sizeof(CharPair));
    char* firstBin = (char*) malloc((var+1)*(sizeof (char)));
    // fill up prev bits
    for (i = 0; i <= currentBit; i++){
      firstBin[i] = transitions[i];
    }
    unsigned char char_ = strtobin(firstBin, var);
    charPairPtr->first = charPairPtr->last = char_;
    result[*indexInResult] = charPairPtr;
    (*indexInResult)++;
    free(firstBin);
  }

  else {
    if (currentBit < (var - 1))
      getTransitionCharsHelper(result, transitions, indexInResult, currentBit + 1, var);
  }

}

/**
 * Given a mona char in 'transitions', returns in 'result' a set of CharPairs representing all ASCII chars/ranges included in this char
 * where *pSize is the number of these ranges.
 * Note that a CharPair is a pair of char values (each of type char).
 * Example: input="0XXX000X"  ==> output=(NUL,SOH), (DLE,DC1), (\s,!), (0,1), (@,A), (P,Q), (`,a), (p,q) , *pSize=8
 * Example: input="00000000"  ==> output=(NUL,NUL), *pSize=1
 * Example: input="XXXXXXXX"  ==> output=(NUL,255), *pSize=1
 */
void getTransitionChars(char* transitions, int var, pCharPair result[], int* pSize){
  assert(strlen(transitions) == var);
  char* trans = (char*) malloc((var + 1)* sizeof(char));
  strcpy(trans, transitions);
  int indexInResult = 0;
  getTransitionCharsHelper(result, trans, &indexInResult, 0, var);
  *pSize = indexInResult;
  free(trans);
}

/* Given a list of CharPairs in 'charRanges', returns a list of STRINGS representing all ASCII chars/ranges included in the
 * input list after merging them where *pSize is the number of these ranges
 * Note values in input are of type char while values of output are the char value (of type char) converted into a string (of type char*)
 * For non printable chars, either its name in ASCII chart (NUL, SOH, CR, LF, ...etc) or its Decimal value is output
 * Example: input=(NUL,SOH), (DLE,DC1), (\s,!), (0,1), (@,A), (P,Q), (`,a), (p,q)  ==> output="[NUL-SOH]", "[DLE-DC1]", "[\s - ! ]", "[ 0 - 1 ]", "[ @ - A ]", "[ P - Q ]", "[ ` - a ]", "[ p - q ]" , *pSize=8
 * Example: input=(NUL,US), (!,!), (",#), ($,'), ((,/), (0,?), (@,DEL), (128, 255)  ==> output="[NUL-US]", "[!-255]", *pSize=1
 * Example: input=(NUL,NUL)  ==> output="NUL", *pSize=1
 * Example: input=(255,255)  ==> output="255", *pSize=1
 * Example: input=(NUL,255)  ==> output="[NUL-255]", *pSize=1
 */
char** mergeCharRanges(pCharPair charRanges[], int* p_size){
  int size = *p_size;
  int i, k, newSize;
  char newFirst, newLast;

  if (size == 0)
    return NULL;
  newSize = 0;
  char** ranges = (char**)malloc(sizeof(char*) * size);
  for (i = 0; i < size; i = k + 1){
    k = i;
    while(k < (size - 1)){
      if (((charRanges[k]->last) + 1) != charRanges[k + 1]->first)
        break;
      else
        k++;
    }
    newFirst = charRanges[i]->first;
    newLast = charRanges[k]->last;
    if (newFirst == newLast){
      ranges[newSize] = (char*)malloc(4 * sizeof(char));
      charToAscii(ranges[newSize], newFirst);
    }
    else{
      ranges[newSize] = (char*)malloc(10 * sizeof(char));
      fillOutCharRange(ranges[newSize], newFirst, newLast);
    }
    newSize++;
  }
  *p_size = newSize;
  return ranges;
}


int dfaPrintBDD(DFA *a, char *filename, int var)
{
    //table->noelems == nomber of bdd nodes
    //table->elem == bdd node
    Table *table = tableInit();
    int i;
    FILE *file;
    
    int sink = find_sink(a);
    
    if (filename) {
        if ((file = fopen(filename, "w")) == 0)
            return 0;
    }
    else {
        file = stdout;
        fprintf(file, "\n\n\n");
    }
    //fprintf(file, "*****************************************************\n");
    //fprintf(file, "*                  MONA DFA BDD                     *\n");
    //fprintf(file, "*****************************************************\n");
    
    /* remove all marks in a->bddm */
    bdd_prepare_apply1(a->bddm);
    
    /* build table of tuples (idx,lo,hi) */
    for (i = 0; i < a->ns; i++)
        export(a->bddm, a->q[i], table);
    
    /* renumber lo/hi pointers to new table ordering */
    for (i = 0; i < table->noelems; i++) {
        if (table->elms[i].idx != -1) {
            table->elms[i].lo = bdd_mark(a->bddm, table->elms[i].lo) - 1;
            table->elms[i].hi = bdd_mark(a->bddm, table->elms[i].hi) - 1;
        }
    }
    
    /* write to file */
    //fprintf(file,            "number of variables: %u\n", var);
    
    //fprintf(file,            "states: %u\n"            "bdd nodes: %u\n",            a->ns, table->noelems);    
    
  fprintf(file,
            "digraph MONA_DFA_BDD {\n"
            "  center = true;\n"
            "  size = \"100.5,70.5\"\n"
            //            "  orientation = landscape;\n"
            "  node [shape=record];\n"
            "   s1 [shape=record,label=\"");
    
    for (i = 0; i < a->ns; i++) {
        fprintf(file, "{%d|<%d> %d}",
                a->f[i],
                i, i);
        if (i+1 < table->noelems)
            fprintf(file, "|");
    }
    fprintf(file, "\"];\n");
    
    fprintf(file, "  node [shape = circle];");
    for (i = 0; i < table->noelems; i++)
        if (table->elms[i].idx != -1)
            fprintf(file, " %d [label=\"%d\"];", i, table->elms[i].idx);
    fprintf(file, "\n  node [shape = box];");
    for (i = 0; i < table->noelems; i++)
        if (table->elms[i].idx == -1)
            fprintf(file, " %d [label=\"%d\"];", i, table->elms[i].lo);
    fprintf(file, "\n");
    
    for (i = 0; i < a->ns; i++)
        fprintf(file, " s1:%d -> %d [style=bold];\n", i, bdd_mark(a->bddm, a->q[i]) - 1);
    
    for (i = 0; i < table->noelems; i++)
        if (table->elms[i].idx != -1) {
            int lo = table->elms[i].lo;
            int hi = table->elms[i].hi;
            fprintf(file, " %d -> %d [style=dashed];\n", i, lo);
            fprintf(file, " %d -> %d [style=filled];\n", i, hi);
        }
    
    fprintf(file, "}\n");
    
    
    
    if (filename)
        fclose(file);
    
    tableFree(table);
    
    return 1;
}


/**
 * printSink: 0 do not print sink nor its incomming/outgoing edges at all,
 *         1 print sink+edges but no edge labels,
 *         2 print everything
 * possible memory leak when printsink == 0 needs correction
 */
void dfaPrintGraphvizAsciiRange(DFA *a, int no_free_vars, int *offsets, int printSink)
{
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, l, size, maxexp, sink;
  pCharPair *buffer;//array of charpairs references
  char *character;
  pCharPair **toTrans;//array for all states, each entry is an array of charpair references
  int *toTransIndecies;
  char** ranges;

  sink = find_sink(a);
//  assert( sink > -1);//with reserved chars, sink is always reject even when negated
  assert(no_free_vars == 8);

  printf("digraph MONA_DFA {\n"
      " rankdir = LR;\n"
      " center = true;\n"
      " size = \"700.5,1000.5\";\n"
      " edge [fontname = Courier];\n"
      " node [height = .5, width = .5];\n"
      " node [shape = doublecircle];");
  for (i = 0; i < a->ns; i++)
    if (a->f[i] == 1)
      printf(" %d;", i);
  printf("\n node [shape = circle];");
  for (i = 0; i < a->ns; i++)
    if (a->f[i] == -1)
      if (i != sink || printSink != 0)
        printf(" %d;", i);
  printf("\n node [shape = box];");
  for (i = 0; i < a->ns; i++)
    if (a->f[i] == 0)
      printf(" %d;", i);
  printf("\n init [shape = plaintext, label = \"\"];\n"
      " init -> %d;\n", a->s);

  maxexp = 1<<no_free_vars;
  buffer = (pCharPair*) malloc(sizeof(pCharPair) * maxexp);//max no of chars from Si to Sj = 2^no_free_vars
  character = (char*) malloc((no_free_vars+1) * sizeof(char));
  toTrans = (pCharPair**) malloc(sizeof(pCharPair*) * a->ns);//need this to gather all edges out to state Sj from Si
  for (i = 0; i < a->ns; i++){
    toTrans[i] = (pCharPair*) malloc(maxexp * sizeof(pCharPair));
  }
  toTransIndecies = (int*) malloc(a->ns * sizeof(int));//for a state Si, how many edges out to each state Sj


  for (i = 0; i < a->ns; i++) {
    //get transitions out from state i
    state_paths = pp = make_paths(a->bddm, a->q[i]);

    //init buffer
    for (j = 0; j < a->ns; j++) {
      toTransIndecies[j] = 0;
    }
    for (j = 0; j < maxexp; j++){
      for (k = 0; k < a->ns; k++)
        toTrans[k][j] = 0;
      buffer[j] = 0;
    }

    //gather transitions out from state i
    //for each transition pp out from state i
    while (pp) {
      if (pp->to == sink && printSink == 0){
        pp = pp->next;
        continue;
      }
      //get mona character on transition pp
      for (j = 0; j < no_free_vars; j++) {
        for (tp = pp->trace; tp && (tp->index != offsets[j]);
            tp = tp->next)
          ;

        if (tp) {
          if (tp->value)
            character[j] = '1';
          else
            character[j] = '0';
        } else
          character[j] = 'X';
      }
      character[j] = '\0';
      if (no_free_vars == 8){
        //break mona character into ranges of ascii chars (example: "0XXX000X" -> [\s-!], [0-1], [@-A], [P-Q])
        size = 0;
        getTransitionChars(character, no_free_vars, buffer, &size);
        //get current index
        k = toTransIndecies[pp->to];
        //print ranges
        for (l = 0; l < size; l++) {
          toTrans[pp->to][k++] = buffer[l];
          buffer[l] = 0;//do not free just detach
        }
        toTransIndecies[pp->to] = k;
      } else {
//        k = toTransIndecies[pp->to];
//        toTrans[pp->to][k] = (char*) malloc(sizeof(char) * (strlen(character) + 1));
//        strcpy(toTrans[pp->to][k], character);
//        toTransIndecies[pp->to] = k + 1;
      }
      pp = pp->next;
    }

    //print transitions out of state i
    for (j = 0; j < a->ns; j++) {
      size = toTransIndecies[j];
      if (size == 0 || (sink == j && printSink == 0))
        continue;
      ranges = mergeCharRanges(toTrans[j], &size);
      //print edge from i to j
      printf(" %d -> %d [label=\"", i, j);
      boolean printLabel = (j != sink || printSink == 2);
      l = 0;//to help breaking into new line
      //for each trans k on char/range from i to j
      for (k = 0; k < size; k++) {
        //print char/range
        if (printLabel) printf(" %s", ranges[k]);
        l += strlen(ranges[k]);
        if (l > 18){
          if (printLabel) printf("\\n");
          l = 0;
        }
        else if (k < (size - 1))
          if (printLabel) putchar(',');
        free(ranges[k]);
      }//for
      printf("\"];\n");
      if (size > 0)
        free(ranges);
    }
    //for each state free charRange
    //merge with loop above for better performance
    for (j = 0; j < a->ns; j++){
      if (j == sink && printSink == 0)
        continue;
      size = toTransIndecies[j];
      for (k = 0; k < size; k++)
        free(toTrans[j][k]);
    }


    kill_paths(state_paths);
  }//end for each state

  free(character);
  free(buffer);
  for (i = 0; i < a->ns; i++){
    free(toTrans[i]);
  }
  free(toTrans);
  free(toTransIndecies);

  printf("}\n");
}

/**
 * printSink: 0 do not print sink nor its incomming/outgoing edges at all,
 *         1 print sink+edges but no edge labels,
 *         2 print everything
 * possible memory leak when printsink == 0 needs correction
 */
void dfaPrintGraphvizAsciiRangeFile(DFA *a, const char *filename, int no_free_vars, int *offsets, int printSink)
{
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k, l, size, maxexp, sink;
  pCharPair *buffer;//array of charpairs references
  char *character;
  pCharPair **toTrans;//array for all states, each entry is an array of charpair references
  int *toTransIndecies;
  char** ranges;
    
    
    FILE *file;
    if (filename) {
        if ((file = fopen(filename, "w")) == 0)
            return;
    }
    else {
        file = stdout;
    }
    
  sink = find_sink(a);
    //  assert( sink > -1);//with reserved chars, sink is always reject even when negated
  assert(no_free_vars == 8);
    
  fprintf(file, "digraph MONA_DFA {\n"
           " rankdir = LR;\n"
           " center = true;\n"
           " size = \"700.5,1000.5\";\n"
           " edge [fontname = Courier];\n"
           " node [height = .5, width = .5];\n"
           " node [shape = doublecircle];");
  for (i = 0; i < a->ns; i++)
    if (a->f[i] == 1)
      fprintf(file, " %d;", i);
  fprintf(file, "\n node [shape = circle];");
  for (i = 0; i < a->ns; i++)
    if (a->f[i] == -1)
      if (i != sink || printSink != 0)
        fprintf(file, " %d;", i);
  fprintf(file, "\n node [shape = box];");
  for (i = 0; i < a->ns; i++)
    if (a->f[i] == 0)
      fprintf(file, " %d;", i);
  fprintf(file, "\n init [shape = plaintext, label = \"\"];\n"
           " init -> %d;\n", a->s);
    
  maxexp = 1<<no_free_vars;
  buffer = (pCharPair*) malloc(sizeof(pCharPair) * maxexp);//max no of chars from Si to Sj = 2^no_free_vars
  character = (char*) malloc((no_free_vars+1) * sizeof(char));
  toTrans = (pCharPair**) malloc(sizeof(pCharPair*) * a->ns);//need this to gather all edges out to state Sj from Si
  for (i = 0; i < a->ns; i++){
    toTrans[i] = (pCharPair*) malloc(maxexp * sizeof(pCharPair));
  }
  toTransIndecies = (int*) malloc(a->ns * sizeof(int));//for a state Si, how many edges out to each state Sj
    
    
  for (i = 0; i < a->ns; i++) {
    //get transitions out from state i
    state_paths = pp = make_paths(a->bddm, a->q[i]);
        
    //init buffer
    for (j = 0; j < a->ns; j++) {
      toTransIndecies[j] = 0;
    }
    for (j = 0; j < maxexp; j++){
      for (k = 0; k < a->ns; k++)
        toTrans[k][j] = 0;
      buffer[j] = 0;
    }
        
    //gather transitions out from state i
    //for each transition pp out from state i
    while (pp) {
      if (pp->to == sink && printSink == 0){
        pp = pp->next;
        continue;
      }
      //get mona character on transition pp
      for (j = 0; j < no_free_vars; j++) {
        for (tp = pp->trace; tp && (tp->index != offsets[j]);
                     tp = tp->next)
          ;
                
        if (tp) {
          if (tp->value)
            character[j] = '1';
          else
            character[j] = '0';
        } else
          character[j] = 'X';
      }
      character[j] = '\0';
      if (no_free_vars == 8){
        //break mona character into ranges of ascii chars (example: "0XXX000X" -> [\s-!], [0-1], [@-A], [P-Q])
        size = 0;
        getTransitionChars(character, no_free_vars, buffer, &size);
        //get current index
        k = toTransIndecies[pp->to];
        //print ranges
        for (l = 0; l < size; l++) {
          toTrans[pp->to][k++] = buffer[l];
          buffer[l] = 0;//do not free just detach
        }
        toTransIndecies[pp->to] = k;
      } else {
                //        k = toTransIndecies[pp->to];
                //        toTrans[pp->to][k] = (char*) malloc(sizeof(char) * (strlen(character) + 1));
                //        strcpy(toTrans[pp->to][k], character);
                //        toTransIndecies[pp->to] = k + 1;
      }
      pp = pp->next;
    }
        
    //print transitions out of state i
    for (j = 0; j < a->ns; j++) {
      size = toTransIndecies[j];
      if (size == 0 || (sink == j && printSink == 0))
        continue;
      ranges = mergeCharRanges(toTrans[j], &size);
      //print edge from i to j
      fprintf(file, " %d -> %d [label=\"", i, j);
      boolean printLabel = (j != sink || printSink == 2);
      l = 0;//to help breaking into new line
      //for each trans k on char/range from i to j
      for (k = 0; k < size; k++) {
        //print char/range
        if (printLabel) fprintf(file, " %s", ranges[k]);
        l += strlen(ranges[k]);
        if (l > 18){
          if (printLabel) fprintf(file, "\\n");
          l = 0;
        }
        else if (k < (size - 1))
          if (printLabel) fputc(',', file);
        free(ranges[k]);
      }//for
      fprintf(file, "\"];\n");
      if (size > 0)
        free(ranges);
    }
    //for each state free charRange
    //merge with loop above for better performance
    for (j = 0; j < a->ns; j++){
      if (j == sink && printSink == 0)
        continue;
      size = toTransIndecies[j];
      for (k = 0; k < size; k++)
        free(toTrans[j][k]);
    }
        
        
    kill_paths(state_paths);
  }//end for each state
    
  free(character);
  free(buffer);
  for (i = 0; i < a->ns; i++){
    free(toTrans[i]);
  }
  free(toTrans);
  free(toTransIndecies);
    
  fprintf(file, "}\n");
    
    if (filename)
        fclose(file);
}



void dfaPrintGraphvizFile(DFA *a, const char *filename, int no_free_vars, unsigned *offsets)
{
    paths state_paths, pp;
    trace_descr tp;
    int i, j, k, l;
    char **buffer;
    int *used, *allocated;
    
    FILE *file;
    if (filename) {
        if ((file = fopen(filename, "w")) == 0)
            return;
    }
    else {
        file = stdout;
    }
    
    fprintf(file, "digraph MONA_DFA {\n"
           " rankdir = LR;\n"
           " center = true;\n"
           " size = \"700.5,1000.5\";\n"
           " edge [fontname = Courier];\n"
           " node [height = .5, width = .5];\n"
           " node [shape = doublecircle];");
    for (i = 0; i < a->ns; i++)
        if (a->f[i] == 1)
            fprintf(file, " %d;", i);
    fprintf(file, "\n node [shape = circle];");
    for (i = 0; i < a->ns; i++)
        if (a->f[i] == -1)
            fprintf(file, " %d;", i);
    fprintf(file, "\n node [shape = box];");
    for (i = 0; i < a->ns; i++)
        if (a->f[i] == 0)
            fprintf(file, " %d;", i);
    fprintf(file, "\n init [shape = plaintext, label = \"\"];\n"
           " init -> %d;\n", a->s);
    
    buffer = (char **) mem_alloc(sizeof(char *) * a->ns);
    used = (int *) mem_alloc(sizeof(int) * a->ns);
    allocated = (int *) mem_alloc(sizeof(int) * a->ns);
    
    for (i = 0; i < a->ns; i++) {
        state_paths = pp = make_paths(a->bddm, a->q[i]);
        
        for (j = 0; j < a->ns; j++) {
            buffer[j] = 0;
            used[j] = allocated[j] = 0;
        }
        
        while (pp) {
            if (used[pp->to] >= allocated[pp->to]) {
                allocated[pp->to] = allocated[pp->to]*2+2;
                buffer[pp->to] =
                (char *) mem_resize(buffer[pp->to], sizeof(char) *
                                    allocated[pp->to] * no_free_vars);
            }
            
            for (j = 0; j < no_free_vars; j++) {
                char c;
                for (tp = pp->trace; tp && (tp->index != offsets[j]); tp = tp->next);
                
                if (tp) {
                    if (tp->value)
                        c = '1';
                    else
                        c = '0';
                }
                else
                    c = 'X';
                
                buffer[pp->to][no_free_vars*used[pp->to] + j] = c;
            }
            used[pp->to]++;
            pp = pp->next;
        }
        
        for (j = 0; j < a->ns; j++)
            if (buffer[j]) {
                fprintf(file, " %d -> %d [label=\"", i, j);
                for (k = 0; k < no_free_vars; k++) {
                    for (l = 0; l < used[j]; l++) {
                        fputc(buffer[j][no_free_vars*l+k], file);
                        if (l+1 < used[j]) {
                            if (k+1 == no_free_vars)
                                fputc(',', file);
                            else
                                fputc(' ', file);
                        }
                    }
                    if (k+1 < no_free_vars)
                        fprintf(file, "\\n");
                }
                fprintf(file, "\"];\n");
                mem_free(buffer[j]);
            }
        
        kill_paths(state_paths);
    }
    
    mem_free(allocated);
    mem_free(used);
    mem_free(buffer);
    
    fprintf(file, "}\n");
    
    if (filename)
        fclose(file);
}


//return the max pairs[i]->count
int get_maxcount(struct int_list_type **pairs, int size) {
  int i;
  int result = 0;
  for (i = 0; i < size; i++) {
    if (pairs[i] != NULL)
      if (result < pairs[i]->count)
        result = pairs[i]->count;
  }
  return result;
}

//return the number of sharp1 state
int get_number_of_sharp1_state(struct int_list_type **pairs, int size) {
  int i;
  int result = 0;
  for (i = 0; i < size; i++)
    if (pairs[i] != NULL && pairs[i]->count > 0)
      result++;

  return result;
}

/**
 * Import Export functions
 *
 */

void dfaExportBddTable(DFA *a, char *file_name, int var) {
    // order 0 for boolean variables
    char *orders = (char *) mem_alloc(sizeof(char) * var);
    // we dont care about variable names but they are used in
    // MONA DFA file format with dfaExport()
    char **varnames = (char **) mem_alloc(sizeof(char *) * var);
    // use dummy variable name for MONA file format
    char* dummy = "var";
    int i = 0;

    // order is 0 for boolean variables
    // variable names are dummy value "var"
    for(i = 0; i < var; i++){
      orders[i] = 0;
      varnames[i] = dummy;
    }
    // dfaExport returns 1 for save success 0 for save fail
    dfaExport(a, file_name, var, varnames, orders);
}

DFA *dfaImportBddTable(char* file_name, int var) {
  char **varnames = (char **) mem_alloc(sizeof(char *) * var);
  char ***varnames_ptr = &varnames;
  int ** orders_ptr = (int **) mem_alloc(sizeof(int *) * var);
  return dfaImport(file_name, varnames_ptr, orders_ptr);
}

void __export(bdd_manager *bddm, unsigned p, Table *table) {
  export(bddm, p, table);
}

//
///***************************************************
//
// Replace function
//
// ***************************************************/
//
////Replace any c \in {sharp1} \vee bar \vee {sharp2} with \epsilon (Assume 00000000000)
//DFA *dfa_replace_delete(DFA *M, int var, int *oldindices) {
//  DFA *result = NULL;
//  DFA *tmpM = NULL;
//  int aux = 0;
//  struct int_list_type **pairs = NULL;
//  int maxCount;
//
//  paths state_paths, pp;
//  trace_descr tp;
//  int i, j, o, z;
//  char *exeps;
//  int *to_states;
//  long max_exeps, k;
//  char *statuces;
//  int len = var;
//  int sink;
//  int *indices = oldindices;
//  char *auxbit = NULL;
//  struct int_type *tmp = NULL;
//
//  //printf("Start get match exclude\n");
//  pairs = get_match_exclude_self(M, var, indices); //for deletion, exclude self state from the closure
//  //printf("End get match exclude\n");
//  maxCount = get_maxcount(pairs, M->ns);
//  if (maxCount > 0) { //Need auxiliary bits when there exist some outgoing edges
//    //printf("Deletion [insert auxiliary bits]!\n");
//    aux = get_hsig(maxCount);
//    len = var + aux;
//    auxbit = (char *) malloc(aux * sizeof(char));
//    indices = allocateArbitraryIndex(len);
//  }
//
//  max_exeps = 1 << len; //maybe exponential
//  sink = find_sink(M);
//  assert(sink>-1);
//
//  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
//
//
//  dfaSetup(M->ns, len, indices);
//  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
//  to_states = (int *) malloc(max_exeps * sizeof(int));
//  statuces = (char *) malloc((M->ns + 1) * sizeof(char));
//
//  for (i = 0; i < M->ns; i++) {
//
//    state_paths = pp = make_paths(M->bddm, M->q[i]);
//    k = 0;
//
//    while (pp) {
//      if (pp->to != sink) {
//        for (tp = pp->trace; tp && (tp->index != indices[var]); tp
//            = tp->next)
//          ; //find the bar value
//        if (!tp || !(tp->value)) {
//          to_states[k] = pp->to;
//          for (j = 0; j < var; j++) {
//            //the following for loop can be avoided if the indices are in order
//            for (tp = pp->trace; tp && (tp->index != indices[j]); tp
//                = tp->next)
//              ;
//
//            if (tp) {
//              if (tp->value)
//                exeps[k * (len + 1) + j] = '1';
//              else
//                exeps[k * (len + 1) + j] = '0';
//            } else
//              exeps[k * (len + 1) + j] = 'X';
//          }
//          for (j = var; j < len; j++) {
//            exeps[k * (len + 1) + j] = '0';
//          }
//          exeps[k * (len + 1) + len] = '\0';
//          k++;
//          if (pairs[pp->to] != NULL && pairs[pp->to]->count > 0) { //need to add extra edges to states in reachable closure
//            o = k - 1; //the original path
//            for (z = 0, tmp = pairs[pp->to]->head; z
//                < pairs[pp->to]->count; z++, tmp = tmp->next) {
//              to_states[k] = tmp->value;
//              for (j = 0; j < var; j++)
//                exeps[k * (len + 1) + j] = exeps[o * (len + 1)
//                    + j];
//              set_bitvalue(auxbit, aux, z + 1); // aux = 3, z=4, auxbit 001
//              for (j = var; j < len; j++) { //set to xxxxxxxx100
//                exeps[k * (len + 1) + j] = auxbit[len - j - 1];
//              }
//              k++;
//            }
//          }
//        }
//      }
//      pp = pp->next;
//    }//end while
//
//    dfaAllocExceptions(k);
//    for (k--; k >= 0; k--)
//      dfaStoreException(to_states[k], exeps + k * (len + 1));
//    dfaStoreState(sink);
//
//    if (M->f[i] == 1)
//      statuces[i] = '+';
//    else if (M->f[i] == -1)
//      statuces[i] = '-';
//    else
//      statuces[i] = '0';
//
//    kill_paths(state_paths);
//  }
//
//  statuces[M->ns] = '\0';
//  result = dfaBuild(statuces);
//  //dfaPrintVitals(result);
//  for (i = 0; i < aux; i++) {
//    j = len - i;
//    tmpM = dfaProject(result, (unsigned) j);
//    result = dfaMinimize(tmpM);
//  }
//  free(exeps);
//  //printf("FREE ToState\n");
//  free(to_states);
//  //printf("FREE STATUCES\n");
//  free(statuces);
//
//  if (maxCount > 0)
//    free(auxbit);
//
//  for (i = 0; i < M->ns; i++)
//    free_ilt(pairs[i]);
//  free(pairs);
//
//  return dfaMinimize(result); //MUST BE CAREFUL FOR INDICES..INDICES MAY NOT MATCH!!
//
//}
//
////Replace sharp1 bar sharp2 to str. str is a single char
////for all i, if pairs[i]!=NULL, add path to each state in pairs[i]
//DFA *dfa_replace_char(DFA *M, char a, int var, int *oldindices) {
//  DFA *result = NULL;
//  DFA *tmpM = NULL;
//  int aux = 0;
//  struct int_list_type **pairs = NULL;
//  int maxCount = 0;
//
//  paths state_paths, pp;
//  trace_descr tp;
//  int i, j, z;
//  char *exeps;
//  int *to_states;
//  long max_exeps, k;
//  char *statuces;
//  int len = var;
//  int sink;
//  int *indices = oldindices;
//  char *auxbit = NULL;
//  struct int_type *tmp = NULL;
//  char *apath = bintostr(a, var);
//
//  pairs = get_match(M, var, indices);
//  maxCount = get_maxcount(pairs, M->ns);
//
//  if (maxCount > 0) { //Need auxiliary bits when there exist some outgoing edges
//    aux = get_hsig(maxCount);
//    //  printf("Replace one char: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
//    auxbit = (char *) malloc(aux * sizeof(char));
//    len = var + aux; // extra aux bits
//    indices = allocateArbitraryIndex(len);
//  }
//
//  max_exeps = 1 << len; //maybe exponential
//  sink = find_sink(M);
//  assert(sink>-1);
//
//  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
//
//
//  dfaSetup(M->ns, len, indices);
//  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
//  to_states = (int *) malloc(max_exeps * sizeof(int));
//  statuces = (char *) malloc((M->ns + 1) * sizeof(char));
//
//  //printf("Before Replace Char\n");
//  //dfaPrintVerbose(M);
//
//  for (i = 0; i < M->ns; i++) {
//
//    state_paths = pp = make_paths(M->bddm, M->q[i]);
//    k = 0;
//
//    while (pp) {
//      if (pp->to != sink) {
//        for (tp = pp->trace; tp && (tp->index != indices[var]); tp
//            = tp->next)
//          ; //find the bar value
//        if (!tp || !(tp->value)) {
//          to_states[k] = pp->to;
//          for (j = 0; j < var; j++) {
//            //the following for loop can be avoided if the indices are in order
//            for (tp = pp->trace; tp && (tp->index != indices[j]); tp
//                = tp->next)
//              ;
//
//            if (tp) {
//              if (tp->value)
//                exeps[k * (len + 1) + j] = '1';
//              else
//                exeps[k * (len + 1) + j] = '0';
//            } else
//              exeps[k * (len + 1) + j] = 'X';
//          }
//          for (j = var; j < len; j++) {
//            exeps[k * (len + 1) + j] = '0';
//          }
//          exeps[k * (len + 1) + len] = '\0';
//          k++;
//
//        }
//      }
//      pp = pp->next;
//    }//end while
//
//    if (pairs[i] != NULL && pairs[i]->count > 0) { //need to add extra edges to states in reachable closure
//
//      for (z = 0, tmp = pairs[i]->head; z < pairs[i]->count; z++, tmp
//          = tmp->next) {
//        to_states[k] = tmp->value;
//        for (j = 0; j < var; j++)
//          exeps[k * (len + 1) + j] = apath[j];
//        set_bitvalue(auxbit, aux, z + 1); // aux = 3, z=4, auxbit 001
//        for (j = var; j < len; j++) { //set to xxxxxxxx100
//          exeps[k * (len + 1) + j] = auxbit[len - j - 1];
//        }
//        exeps[k * (len + 1) + len] = '\0';
//        k++;
//      }
//    }
//
//    dfaAllocExceptions(k);
//    for (k--; k >= 0; k--)
//      dfaStoreException(to_states[k], exeps + k * (len + 1));
//    dfaStoreState(sink);
//
//    if (M->f[i] == 1)
//      statuces[i] = '+';
//    else if (M->f[i] == -1)
//      statuces[i] = '-';
//    else
//      statuces[i] = '0';
//
//    kill_paths(state_paths);
//  }
//
//  statuces[M->ns] = '\0';
//  result = dfaBuild(statuces);
//  //dfaPrintVitals(result);
//  for (i = 0; i < aux; i++) {
//    j = len - i;
//    tmpM = dfaProject(result, (unsigned) j);
//    result = dfaMinimize(tmpM);
//  }
//  free(exeps);
//  //printf("FREE ToState\n");
//  free(to_states);
//  //printf("FREE STATUCES\n");
//  free(statuces);
//
//  free(apath);
//
//  if (maxCount > 0)
//    free(auxbit);
//
//  for (i = 0; i < M->ns; i++)
//    free_ilt(pairs[i]);
//  free(pairs);
//
//  return dfaMinimize(result);
//
//  //NEED TO FREE INDICES
//
//}
//
////Replace every pairs(i,j), so that i can reach j through sharp1 bar sharp0, to i M1 j, where M1 is an arbitrary DFA
//DFA *dfa_replace_M(DFA *M, DFA *M1, int var, int *indices) {
//  DFA *result = NULL;
//  return result;
//}
//
//char **get_bitstrings(char *str, int var, int aux) {
//
//  int i, j;
//  char **result;
//  i = strlen(str);
//  result = (char **) malloc(i * sizeof(char*));
//  for (j = 0; j < i; j++)
//    result[j] = bintostrWithExtraBitsZero(str[j], var, aux);
//  return result;
//}
//
////Replace sharp1 bar sharp2 to str.
//DFA *dfa_replace_string(DFA *M, char *str, int var, int *oldindices) {
//  DFA *result = NULL;
//  DFA *tmpM = NULL;
//  int aux = 0;
//  struct int_list_type **pairs = NULL;
//  int maxCount, numberOfSharp;
//
//  paths state_paths, pp;
//  trace_descr tp;
//  int i, j, z;
//  int s = 0;
//  char *exeps;
//  char *auxexeps = NULL;
//  int *to_states;
//  int *aux_to_states = NULL;
//  long max_exeps, k;
//  char *statuces;
//  int len = var;
//  int ns, sink;
//  int *indices = oldindices;
//  char *auxbit = NULL;
//  struct int_type *tmp = NULL;
//  int extrastates = strlen(str) - 1;
//  char **binOfStr = NULL;
//  int *startStates = NULL;
//
//  pairs = get_match(M, var, indices);
//
//  maxCount = get_maxcount(pairs, M->ns);
//  numberOfSharp = get_number_of_sharp1_state(pairs, M->ns);
//
//  if (maxCount > 0) { //Need auxiliary bits when there exist some outgoing edges
//    aux = get_hsig(maxCount);
//    //    printf("Replace string: %d hits, need to add %d auxiliary bits\n", maxCount, aux);
//    auxbit = (char *) malloc(aux * sizeof(char));
//    len = var + aux; // extra aux bits
//    indices = allocateArbitraryIndex(len);
//    binOfStr = get_bitstrings(str, var, aux); //initially extra bit are zero
//    s = 0;
//    startStates = (int *) malloc(numberOfSharp * sizeof(int));
//    for (i = 0; i < numberOfSharp; i++) {
//      startStates[i] = -1; //initially it is -1. There is an error if some of them are not set up later.
//    }
//    auxexeps = (char *) malloc(maxCount * (len + 1) * sizeof(char));
//    aux_to_states = (int *) malloc(maxCount * sizeof(int));
//  }
//
//  max_exeps = 1 << len; //maybe exponential
//  sink = find_sink(M);
//  assert(sink>-1);
//  ns = M->ns + numberOfSharp * extrastates;
//
//  //pairs[i] is the list of all reachable states by \sharp1 \bar \sharp0 from i
//  dfaSetup(ns, len, indices);
//  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char)); //plus 1 for \0 end of the string
//  to_states = (int *) malloc(max_exeps * sizeof(int));
//  statuces = (char *) malloc((ns + 1) * sizeof(char));
//
//  for (i = 0; i < M->ns; i++) {
//
//    state_paths = pp = make_paths(M->bddm, M->q[i]);
//    k = 0;
//
//    while (pp) {
//      if (pp->to != sink) {
//        for (tp = pp->trace; tp && (tp->index != indices[var]); tp
//            = tp->next)
//          ; //find the bar value
//        if (!tp || !(tp->value)) {
//          to_states[k] = pp->to;
//          for (j = 0; j < var; j++) {
//            //the following for loop can be avoided if the indices are in order
//            for (tp = pp->trace; tp && (tp->index != indices[j]); tp
//                = tp->next)
//              ;
//
//            if (tp) {
//              if (tp->value)
//                exeps[k * (len + 1) + j] = '1';
//              else
//                exeps[k * (len + 1) + j] = '0';
//            } else
//              exeps[k * (len + 1) + j] = 'X';
//          }
//          for (j = var; j < len; j++) {
//            exeps[k * (len + 1) + j] = '0'; //all original paths are set to zero
//          }
//          exeps[k * (len + 1) + len] = '\0';
//          k++;
//
//        }
//      }
//      pp = pp->next;
//    }//end while
//    if (pairs[i] != NULL && pairs[i]->count > 0) { //need to add extra edges to states in reachable closure
//      startStates[s] = i; //pairs[startStates[s]] is the destination that later we shall use for region s
//      to_states[k] = M->ns + s * (extrastates); // go to the initial state of string by the first char
//      s++;
//      for (j = 0; j < len; j++)
//        exeps[k * (len + 1) + j] = binOfStr[0][j];
//      exeps[k * (len + 1) + len - 1] = '1'; //to distinguish the original path
//      exeps[k * (len + 1) + len] = '\0';
//      k++;
//    }
//
//    dfaAllocExceptions(k);
//    for (k--; k >= 0; k--)
//      dfaStoreException(to_states[k], exeps + k * (len + 1));
//    dfaStoreState(sink);
//
//    if (M->f[i] == 1)
//      statuces[i] = '+';
//    else if (M->f[i] == -1)
//      statuces[i] = '-';
//    else
//      statuces[i] = '0';
//
//    kill_paths(state_paths);
//  }
//
//  assert(s==numberOfSharp);
//  assert(i==M->ns);
//
//  for (i = 0; i < numberOfSharp; i++) {
//    for (j = 0; j < extrastates - 1; j++) { //internal string (exclude the first and the last char)
//      dfaAllocExceptions(1);
//      dfaStoreException(M->ns + i * (extrastates) + j + 1,
//          binOfStr[j + 1]);
//      dfaStoreState(sink);
//    }
//    assert((pairs[startStates[i]]!=NULL) && (pairs[startStates[i]]->count> 0));
//
//    //for the end state add pathes to get back to pair[startStates[i]]
//
//
//    for (z = 0, tmp = pairs[startStates[i]]->head; z
//        < pairs[startStates[i]]->count; z++, tmp = tmp->next) {
//      aux_to_states[z] = tmp->value;
//      for (j = 0; j < var; j++)
//        auxexeps[z * (len + 1) + j] = binOfStr[extrastates][j];
//      set_bitvalue(auxbit, aux, z + 1); // aux = 3, z=4, auxbit 001
//      for (j = var; j < len; j++) { //set to xxxxxxxx100
//        auxexeps[z * (len + 1) + j] = auxbit[len - j - 1];
//      }
//      auxexeps[z * (len + 1) + len] = '\0';
//    }
//    dfaAllocExceptions(z);
//    for (z--; z >= 0; z--)
//      dfaStoreException(aux_to_states[z], auxexeps + z * (len + 1));
//    dfaStoreState(sink);
//  }
//
//  for (i = M->ns; i < ns; i++)
//    statuces[i] = '0';
//
//  statuces[ns] = '\0';
//  result = dfaBuild(statuces);
//
//  for (i = 0; i < aux; i++) {
//    j = len - i;
//    //printf("Project the %d bit\n", i);
//    //printf("Original: %d", i); // changed by muath : adding %d
//    //dfaPrintVitals(result);
//    tmpM = dfaProject(dfaMinimize(result), (unsigned) j);
//    //printf("Projected: %d", i);// changed by muath : adding %d
//    //dfaPrintVitals(tmpM);
//    dfaFree(result);
//    result = dfaMinimize(tmpM);
//    dfaFree(tmpM);
//    //printf("Minimized: %d", i);// changed by muath : adding %d
//    //dfaPrintVitals(result);
//  }
//  free(exeps);
//  //printf("FREE ToState\n");
//  free(to_states);
//  //printf("FREE STATUCES\n");
//  free(statuces);
//
//  if (maxCount > 0) {
//    free(auxbit);
//    free(aux_to_states);
//    free(auxexeps);
//    free(indices);
//    free(startStates);
//    for (i = 0; i < strlen(str); i++)
//      free(binOfStr[i]);
//    free(binOfStr);
//  }
//
//  for (i = 0; i < M->ns; i++)
//    free_ilt(pairs[i]);
//  free(pairs);
//
//  return dfaMinimize(result);
//
//}
//
//DFA *dfa_replace_step3_replace(DFA *M, char *str, int var, int *indices) {
//  DFA *result = NULL;
//  if ((str == NULL) || strlen(str) == 0) {
//    //printf("Replacement [%s]!\n", str);
//    result = dfa_replace_delete(M, var, indices);
//  } else if (strlen(str) == 1) {
//    //printf("Replacement [%s]!\n", str);
//    result = dfa_replace_char(M, str[0], var, indices);
//  } else {
//    //printf("Replacement [%s]!\n", str);
//    result = dfa_replace_string(M, str, var, indices);
//  }
//  return result;
//} //END dfa_replace_stpe3_replace
//
//
//DFA *dfa_replace_extrabit(M1, M2, str, var, indices)
//  DFA *M1;DFA *M2;char *str;int var;int *indices; {
//
//  DFA *result;
//  DFA *M1_bar;
//  DFA *M2_bar;
//  DFA *M_inter;
//  DFA *M_rep;
//  DFA *M_sharp = dfaSharpStringWithExtraBit(var, indices);
//
//  //printf("Insert sharp1 and sharp2 for duplicate M1\n");
//  M1_bar = dfa_replace_step1_duplicate(M1, var, indices);
//  //  dfaPrintVerbose(M1_bar);  //having extra bit
//  //printf("M1_bar: var %d\n", var);
//  //dfaPrintVerbose(M1_bar);
//  //  dfaPrintGraphviz(M1_bar, var+1, allocateAscIIIndex(var+1));
//  //printf("Generate M2 bar sharp1 M2 and sharp2\n");
//  M2_bar = dfa_replace_step2_match_compliment(M2, var, indices);
//  //  dfaPrintVerbose(M2_bar);  //having extra bit
//  //printf("M2_bar: var %d\n", var);
//  //dfaPrintVerbose(M2_bar);
//  //  dfaPrintGraphviz(M2_bar, var+1, allocateAscIIIndex(var+1));
//
//  //printf("Generate Intersection\n");
//  M_inter = dfa_intersect(M1_bar, M2_bar);
//  //printf("M_inter\n");
//  //dfaPrintVerbose(M_inter);
//  //  dfaPrintGraphviz(M_inter, var+1, allocateAscIIIndex(var+1));
//
//  //dfaPrintVerbose(M_inter);
//
//
//  if (check_intersection(M_sharp, M_inter, var, indices) > 0) {
//
//    //printf("Start Replacement!\n");
//    //replace match patterns
//    M_rep = dfa_replace_step3_replace(M_inter, str, var, indices);
//    result = dfaProject(M_rep, (unsigned) var);
//    dfaFree(M_rep);
//
//  } else { //no match
//    result = M1;
//  }
//
//  //printf("free M1_bar\n");
//  dfaFree(M1_bar);
//  //printf("free M2_bar\n");
//  dfaFree(M2_bar);
//  //printf("free M_inter\n");
//  dfaFree(M_inter);
//  //printf("free M_sharp\n");
//  dfaFree(M_sharp);
//
//  return dfaMinimize(result);
//}

/**
 * Baki
 */
DFA *dfaStringAutomatonL1toL2(int start, int end, int var, int* indices) {

  int i, number_of_states;
  char *statuces;
  DFA *result=NULL;
  char* sharp1 = NULL;
  char* sharp0 = NULL;

  if (start <= -1 && end <= -1) {
    return dfaASCIINonString(var, indices);
  }

  if ( start <= -1 ) {
    start = 0; // -1 means no lower bound, zero is the minimum lower bound
  }

  if(end <= -1) { //accept everything after l1 steps

    number_of_states = start + 2; // add one sink state
    statuces=(char *)malloc( (number_of_states + 1)*sizeof(char) );
    dfaSetup(number_of_states, var, indices);

    //the 0 to start - 1 states(unaccepted)
    for( i = 0; i < start; i++){
      dfaAllocExceptions(2);
      //char 255; //reserve word for sharp1
      sharp1 = getSharp1(var);
      dfaStoreException(number_of_states - 1, sharp1); // sink state is the number_of_states - 1
      free(sharp1); sharp1 = NULL;
      //char 254;
      sharp0 = getSharp0(var);
      dfaStoreException(number_of_states - 1, sharp0); // sink state is the number_of_states - 1
      free(sharp0); sharp0 = NULL;

      dfaStoreState(i + 1);
      statuces[i] = '-';


    }
    // the start state
    dfaAllocExceptions(2);
    //char 255; //reserve word for sharp1
    sharp1 = getSharp1(var);
    dfaStoreException(number_of_states - 1, sharp1); // sink state is the number_of_states - 1
    free(sharp1); sharp1 = NULL;
    //char 254;
    sharp0 = getSharp0(var);
    dfaStoreException(number_of_states - 1, sharp0); // sink state is the number_of_states - 1
    free(sharp0); sharp0 = NULL;

    dfaStoreState(i);     // i == start
    statuces[i] = '+';    // i == start
    i++;

  } else {
    assert( end >= start);

    number_of_states = end + 2; // add one sink state
    statuces=(char *)malloc( (number_of_states + 1)*sizeof(char) );
    dfaSetup(number_of_states, var, indices);

    //the start to end states(accepted)
    for( i = 0; i <= end; i++){
      dfaAllocExceptions(2);
      //char 255; //reserve word for sharp1
      sharp1 = getSharp1(var);
      dfaStoreException(number_of_states - 1, sharp1); // sink state is the number_of_states - 1
      free(sharp1); sharp1 = NULL;
      //char 254;
      sharp0 = getSharp0(var);
      dfaStoreException(number_of_states - 1, sharp0); // sink state is the number_of_states - 1
      free(sharp0); sharp0 = NULL;

      dfaStoreState(i + 1);
      if(i >= start) {
        statuces[i] = '+';
      } else {
        statuces[i] = '-';
      }
    }
  }

  //the sink state
  dfaAllocExceptions(0);
  dfaStoreState(number_of_states - 1);  // sink state
  statuces[number_of_states - 1] = '-';   // i == end + 1 == number_of_states - 1
  statuces[number_of_states] = '\0';    // number_of_states == end + 2

  result=dfaBuild(statuces);
  //dfaPrintVerbose(result);
  free(statuces);
  if(start == 0) result->f[result->s] = 1;
  DFA *tmp = dfaMinimize(result);
  dfaFree(result);
  return tmp;
}


/************************************

 Composite Functions:

 1. DFA* dfa_string_to_unaryDFA(DFA* M)
 2. struct semiliner_type* getSemilinerSetCoefficients(DFA *M) // M is a unary DFA
 3. DFA* dfa_seminliner_to_binaryDFA(struct semiliner_type* S) // S: R, C, c[], r[]
 4. DFA* dfa_restrict_by_unaryDFA(DFA* M, DFA* L)
 5. DFA* dfa_compose_DFA_tracks(DFA* M1, DFA* M2)
 6. Boolean checkIntersectionOfCompositeDFA(DFA* M1, DFA* M, DFA* F) //Length(M1 \wedge M2) \wedge F \neq Empty


 **************************************/

// Outputs M` that represents the length of automaton M
//Output M, so that L(M)={|w|| w \in L(M1)}
//Need to use extra bit to model NFA to DFA
//NOTE: Add 1 to all symbols
// 1. Duplicate paths (0->k, k is not sink) with extra bit set to 1 for each symbol.
// 2. Project all bits except extra bit away
DFA *dfa_string_to_unaryDFA(M, var, indices)
  DFA *M;int var;int *indices; {
  DFA *result;
  DFA *tmpM;
  paths state_paths, pp;
  trace_descr tp;
  int i, j, k;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps;
  char *statuces;
  int len;
  len = var + 1; //one extra bit

  max_exeps = 1 << len; //maybe exponential
  sink = find_sink(M);
  assert(sink> -1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(M->ns, len, indices);
  exeps = (char *) malloc(max_exeps * (len + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((M->ns + 1) * sizeof(char));

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
        exeps[k * (len + 1) + var] = '1'; //add 1 to the last  bit
        exeps[k * (len + 1) + len] = '\0';
        k++;
      }
      pp = pp->next;
    }
    dfaAllocExceptions(k);
    for (k--; k >= 0; k--)
      dfaStoreException(to_states[k], exeps + k * (len + 1));
    dfaStoreState(sink);

    if (M->f[i] == 1)
      statuces[i] = '+';
    else if (M->f[i] == -1)
      statuces[i] = '-';
    else
      statuces[i] = '0';

    kill_paths(state_paths);
  }
  statuces[i] = '\0';
  //result = dfaBuild(statuces);
  result = dfaBuild(statuces);

  for (i = 0; i < var; i++) {
    tmpM = dfaProject(result, i);
    result = dfaMinimize(tmpM);
//    printf("Projecting away the %dth bit\n", i);
//    dfaPrintVerbose(result);
  }

  //  result=dfaProject(tmpM, (unsigned) var); //var is the index of the extra bit

  free(exeps);
  free(to_states);
  free(statuces);
  dfaFree(tmpM);
  return result;

} // END dfa_string_to_unaryDFA



DFA *dfa_restrict_by_unaryDFA(DFA *M, DFA* uL, int var, int *indices){
  DFA *result, *length;
  paths state_paths, pp;
  int i, j, num, k;
  char *exeps;
  int *to_states;
  int sink;
  long max_exeps;
  char *statuces;
  char* chars[] = {"1111110X", "111110XX", "11110XXX", "1110XXXX", "110XXXXX", "10XXXXXX", "0XXXXXXX"};

  max_exeps = 1 << var; //maybe exponential
  sink = find_sink(uL);
  assert(sink> -1);
  //printf("\n\n SINK %d\n\n\n", sink);

  dfaSetup(uL->ns, var, indices);
  exeps = (char *) malloc(max_exeps * (var + 1) * sizeof(char));
  to_states = (int *) malloc(max_exeps * sizeof(int));
  statuces = (char *) malloc((uL->ns + 1) * sizeof(char));

  for (i = 0; i < uL->ns; i++) {
      state_paths = pp = make_paths(uL->bddm, uL->q[i]);
      num = 0;
      k = 0;
      while (pp) {
        if (pp->to != sink) {
          num++;
          while (k < 7){
            to_states[k] = pp->to;
            for (j = 0; j < var; j++)
              exeps[k * (var + 1) + j] = chars[k][j];
            exeps[k * (var + 1) + var] = '\0';
            k++;
          }
        }
        pp = pp->next;
      }
      //either we go to one state with 8 exceptions or we go to nothing
      assert((num == 1 && k == 7) || (num == 0 && k == 0));

      dfaAllocExceptions(k);
      for (k--; k >= 0; k--)
        dfaStoreException(to_states[k], exeps + k * (var + 1));
      dfaStoreState(sink);

      if (uL->f[i] == 1)
        statuces[i] = '+';
      else
        statuces[i] = '-';

      kill_paths(state_paths);
  }
  statuces[i] = '\0';
  length = dfaBuild(statuces);
//  printf("\n\nlength auto:\n");
//  dfaPrintGraphvizAsciiRange(length, var, indices, 0);
//  dfaPrintGraphviz(length, var, indices);
  result = dfa_intersect(M, length);
  dfaFree(length);


  free(exeps);
  free(to_states);
  free(statuces);
  return result;

}



/**
 Given a set of finite lengths fl, returns an automaton M` where for all w element_of L(M)
 if |w| is in fl then w is element_of L(M`)
 If the list fl is sorted incrementally (from smallest to largest) set ordered to true.
 */
DFA *dfaRestrictByFiniteLengths(DFA *M, unsigned *lengths, const unsigned size, bool sorted, int var, int *indices){
    DFA *lM = dfaSigmaLengthsSet(lengths, size, sorted, var, indices);
    DFA *result = dfa_intersect(M, lM);
    dfaFree(lM);
    return result;
}

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
struct semilinear_type* getSemilinerSetCoefficients(DFA *M) {
  struct semilinear_type *tmp;

  int m, s, i, C, R, nr, nc;
  paths pp;
  int flag = 0;
  int* tc = (int *) malloc(sizeof(int) * (M->ns));
  int sink = find_sink(M);
  assert(sink> -1);
  //s = M->ns-1; // the maximal steps to travel every state in a unary automaton
  //assert(s>=0);

  for (i = 0; i < M->ns; i++)
    tc[i] = -1;

  // idenitify the backtrack point as m
  m = M->s;
  for (s = 0; s < M->ns; s++) {
    tc[m] = 1;
    pp = make_paths(M->bddm, M->q[m]);
    while (pp) {
      if (pp->to != sink) {
        m = pp->to;
        if (tc[m] == 1) {
          flag = 1;
          //printf("reach cycle at state [%d]\n", m);
        }
        break;
      } else
        pp = pp->next;
    }
    if (flag)
      break;
  }

  i = M->s;
  C = 0;
  R = 0;
  nr = 0;
  nc = 0;

  //there is no cycle: construct {l2, c2, ..., c_n}
  if (flag == 0) {
    if (M->f[i] == 1) {
      tc[nc] = C;
      nc++;
    }
    for (s = 0; s < M->ns; s++) {
      pp = make_paths(M->bddm, M->q[i]);
      while (pp) {
        if (pp->to != sink) {
          i = pp->to;
          C += 1;
          if (M->f[i] == 1) {
            tc[nc] = C;
            nc++;
          }
          break;
        } else
          pp = pp->next;
      }
    }//end for
  } else {
    if (i == m)
      flag = 1;
    else
      flag = 0;

    if (M->f[i] == 1) {
      if (!flag) {
        tc[nc] = C;
        nc++;
      } else {
        tc[nc + nr] = R;
        nr++;
      }
    }
    for (s = 0; s < M->ns; s++) {
      pp = make_paths(M->bddm, M->q[i]);
      while (pp) {
        if (pp->to != sink) {
          i = pp->to;

          if (!flag)
            C += 1;
          else if (i != m)
            R += 1;
          if (!flag && i == m) {
            flag = 1;
            if (M->f[i] == 1) {
              tc[nc + nr] = R;
              nr++;
            }
          }

          if (M->f[i] == 1) {
            if (!flag) {
              tc[nc] = C;
              nc++;
            } else if (i != m) {
              tc[nc + nr] = R;
              nr++;
            }
          }
          break;
        } else
          pp = pp->next;
      }
    }//end for
    if (R == 0)
      R = 1;
  }
  tmp = (struct semilinear_type *) malloc(sizeof(struct semilinear_type));
  tmp -> C = C; // return m, such that \delta(q_n, 1)=q_m. O.w., return M->n
  tmp -> R = R;
  tmp -> nc = nc;
  tmp -> nr = nr;
  if (nc == 0) {
    tmp->c = NULL;
  } else {
    tmp -> c = (int *) malloc(sizeof(int) * (nc));
    for (i = 0; i < nc; i++)
      tmp->c[i] = tc[i];
  }
  if (nr == 0) {
    tmp->r = NULL;
  } else {
    tmp -> r = (int *) malloc(sizeof(int) * (nr));
    for (i = 0; i < nr; i++)
      tmp->r[i] = tc[i + nc];
  }
  free(tc);
  return tmp;
}

void print_semilinear_coefficients(struct semilinear_type* S) {

  int i;
  printf("Print The Semilinear Set: \n");
  printf("\t The length of tail (C):%d\n", S->C);
  printf("\t The length of cycle (R):%d\n", S->R);
  printf("\t The Semilinear Set is: ");
  for (i = 0; i < S->nc; i++)
    printf("{%d}, ", S->c[i]);
  for (i = 0; i < S->nr; i++)
    printf("{%d+%d+%d*k}, ", S->C, S->r[i], S->R);
  printf("\n\n");
  //printf("{%d+%d*k}\n", S->r[i+1]);
}

/**
 * returns true (1) if {|w| < n: w elementOf L(M) && n elementOf Integers}
 * In other words length of all strings in the language is bounded by a value n
 * TODO: possible leak by not fully freeing semilinerset
 */
int isLengthFinite(DFA* M, int var, int* indices){
  DFA* uL = dfa_string_to_unaryDFA(M, var, indices);
  struct semilinear_type* s;
  s = getSemilinerSetCoefficients(uL);
  int cycle = s->R;
  int result;
  if (cycle == 0){
    result = 1;
  }
  else
    result = 0;
  dfaFree(uL);
  free(s);
  return result;
}



/*************************

 t \in {0, 1, 2}: (val, rem_t, rem_f)
 v: value(t==0) or remainder(t==1 or 2)
 b: bit value(t==0) or remainder(t==1 or 2)
 C: link length
 R: cycle length

 *************************/

int add_binary_state(struct binary_state_type** M, int C, int R, int t, int v,
    int b) {

  struct binary_state_type* tmp;
  int i = 0;
  int d0 = -1;
  int d1 = -1;

  assert(R> 0 && C> 0);
  tmp = M[i];
  while (tmp != NULL) {
    if (tmp->t == t && tmp->v == v && tmp->b == b)
      return i;
    else {
      i += 1;
      tmp = M[i];
    }
  }

  // add a new state
  M[i] = (struct binary_state_type*) malloc(sizeof(struct binary_state_type));
  M[i]-> t = t;
  M[i]-> v = v;
  M[i]-> b = b;
  if (b < 0) {
    if (C == 1) {
      d1 = add_binary_state(M, C, R, 1, 1 % R, 1 % R);
      d0 = add_binary_state(M, C, R, 2, 0, 1 % R);
    } else {
      d1 = add_binary_state(M, C, R, 0, 1, 1);
      d0 = add_binary_state(M, C, R, 0, 0, 1);
    }
  } else if (t == 0 && (v + 2 * b >= C)) {
    d1 = add_binary_state(M, C, R, 1, (v + 2 * b) % R, (2 * b) % R);
    d0 = add_binary_state(M, C, R, 2, (v) % R, (2 * b) % R);
  } else if (t == 0 && (v + 2 * b < C)) {
    d1 = add_binary_state(M, C, R, 0, v + 2 * b, 2 * b);
    d0 = add_binary_state(M, C, R, 0, v, 2 * b);
  } else if (t == 1) {
    d1 = add_binary_state(M, C, R, 1, (v + 2 * b) % R, (2 * b) % R);
    d0 = add_binary_state(M, C, R, 1, v % R, (2 * b) % R);
  } else if (t == 2) {
    d1 = add_binary_state(M, C, R, 1, (v + 2 * b) % R, (2 * b) % R);
    d0 = add_binary_state(M, C, R, 2, v % R, (2 * b) % R);
  }

  M[i]-> d0 = d0;
  M[i]-> d1 = d1;
  return i;
} // end add_binary_state


int getNumOfBinaryStates(struct binary_state_type** Q) {

  int i = 0;
  struct binary_state_type* tmp = Q[0];
  while (tmp != NULL) {
    i++;
    tmp = Q[i];
  }
  return i;
}

char getBinaryStatus(struct binary_state_type *q, struct semilinear_type *S) {
  int i;
  assert(q!=NULL);
  assert(S != NULL);

  if (q->t == 0) {
    for (i = 0; i < S->nc; i++)
      if (S->c[i] == q->v)
        return '+';
  } else if (q->t == 1) {
    for (i = 0; i < S->nr; i++)
      if (q->v == ((S->r[i] + S->C) % (S->R)))
        return '+';
  }
  return '-';
}

DFA* dfa_semiliner_to_binaryDFA(struct semilinear_type *S) {
  DFA *result = NULL;

  int i, nQ, MAX;
  int* uni_indices = allocateArbitraryIndex(1);
  char* statuces;
  char* s = malloc(2);

  assert(S != NULL);
  s[1] = '\0';

  if ((S->C) >= (S->R))
    MAX = 3 * (S->C) * (S->C);
  else
    MAX = 3 * (S->R) * (S->R);

  struct binary_state_type* Q[MAX];

  //  Q = (struct binary_state_type**) malloc (sizeof(struct binary_state_type*)*MAX);

  for (i = 0; i < MAX; i++)
    Q[i] = NULL; //initialize

  nQ = add_binary_state(Q, S->C, S->R, 0, 0, -1);
  assert(nQ ==0);
  nQ = getNumOfBinaryStates(Q);

  dfaSetup(nQ + 1, 1, uni_indices); // one extra state as sink state
  statuces = (char *) malloc((nQ + 2) * sizeof(char));

  for (i = 0; i < nQ; i++) {
    if (Q[i]->d0 >= 0 && Q[i]->d1 >= 0) {
      dfaAllocExceptions(2);
      s[0] = '0';
      dfaStoreException(Q[i]->d0, s);
      s[0] = '1';
      dfaStoreException(Q[i]->d1, s);
    } else if (Q[i]->d0 >= 0 && Q[i]->d1 < 0) {
      dfaAllocExceptions(1);
      s[0] = '0';
      dfaStoreException(Q[i]->d0, s);
    } else if (Q[i]->d0 < 0 && Q[i]->d1 >= 0) {
      dfaAllocExceptions(1);
      s[0] = '1';
      dfaStoreException(Q[i]->d1, s);
    } else {
      dfaAllocExceptions(0);
    }
    dfaStoreState(nQ);
    statuces[i] = getBinaryStatus(Q[i], S);
  }
  assert(i==nQ);
  // for the sink state
  dfaAllocExceptions(0);
  dfaStoreState(nQ);
  statuces[nQ] = '-';
  statuces[nQ + 1] = '\0';
  result = dfaBuild(statuces);

  for (i = 0; i < nQ; i++)
    free(Q[i]);
  //free(Q);
  free(statuces);
  //return result;
  return dfaMinimize(result);

}

/********************************

 Print Function

 ***********************************/

static void print_example(char *example, char *name, int no_free_vars,
    char **free_variables, unsigned *offsets, char *types, int treestyle) {
  int i, j;
  int length;

  length = (int)strlen(example) / (no_free_vars + 1);

  if (treestyle) {
    printf("Free variables are: ");
    for (i = 0; i < no_free_vars; i++)
      printf("%s%s", free_variables[i], i == no_free_vars - 1 ? "" : ", ");

    printf("\n\nA %s of least length (%d) is:\n"
      "Booleans:\n", name, length - 1);
    for (i = 0; i < no_free_vars; i++)
      putchar(example[i * length]);

    printf("\nUniverse:\n");
    for (i = 1; i < length; i++) {
      putchar('(');
      for (j = 0; j < no_free_vars; j++)
        putchar(example[j * length + i]);
      putchar(',');
    }
    printf("()");
    for (i = 1; i < length; i++)
      printf(",())");
    printf("\n");

  } else {
    printf("A %s of least length (%d) is:\n", name, length - 1);
    for (i = 0; i < no_free_vars; i++) {
      printf("%-15s %c ", free_variables[i], example[i * length]);
      for (j = 0; j < length - 1; j++)
        putchar(example[i * length + 1 + j]);
      printf("\n");
    }
    printf("\n");

    for (i = 0; i < no_free_vars; i++)
      switch (types[i]) {
      case 0:
        printf("%s = %s\n", free_variables[i], example[i * length]
            == '1' ? "true" : "false");
        break;
      case 1: {
        int j = 0;
        while (example[i * length + j + 1] == '0' && j < length)
          j++;
        printf("%s = %i\n", free_variables[i], j);
      }
        break;
      case 2: {
        int j, t = 0;
        printf("%s = {", free_variables[i]);
        for (j = 0; j < length; j++)
          if (example[i * length + j + 1] == '1') {
            if (t++ != 0)
              printf(",");
            printf("%i", j);
          }
        printf("}\n");
      }
        break;
      }
  }

  mem_free(example);
}

int check_emptiness_with_example(M1, noFreeVars, free_variables, offsets)
  DFA *M1;int noFreeVars;char** free_variables;int *offsets; {
  char *satisfyingexample;
  int i;
  unsigned *unsignedOffsets = (unsigned *) malloc(noFreeVars
      * sizeof(unsigned));
  for (i = 0; i < noFreeVars; i++)
    unsignedOffsets[i] = (offsets[i] <= 0 ? 0 : offsets[i]);
  satisfyingexample = dfaMakeExample(M1, 1, noFreeVars, unsignedOffsets);

  ///* PRINT COUNTER EXAMPLE
  if (satisfyingexample)
    if (noFreeVars) {
      printf("\n");
      print_example(satisfyingexample, "satisfying example", noFreeVars,
          free_variables, unsignedOffsets, NULL, 1); //tree style
    }
  //*/
  mem_free(unsignedOffsets);
  return ((satisfyingexample) ? 0 : 1);
}

//This is modified from dfaExport() in external.c by changing char orders[] to int orders[];
int dfa_export(DFA *a, char *filename, int num, char *vars[], int orders[]) {
  Table *table = tableInit();
  int i;
  FILE *file;

  if (filename) {
    if ((file = fopen(filename, "w")) == 0)
      return 0;
  } else
    file = stdout;

  /* remove all marks in a->bddm */
  bdd_prepare_apply1(a->bddm);

  /* build table of tuples (idx,lo,hi) */
  for (i = 0; i < a->ns; i++)
    export(a->bddm, a->q[i], table);

  /* renumber lo/hi pointers to new table ordering */
  for (i = 0; i < table->noelems; i++) {
    if (table->elms[i].idx != -1) {
      table->elms[i].lo = bdd_mark(a->bddm, table->elms[i].lo) - 1;
      table->elms[i].hi = bdd_mark(a->bddm, table->elms[i].hi) - 1;
    }
  }

  /* write to file */
  fprintf(file, "MONA DFA\n"
    "number of variables: %u\n"
    "variables:", num);
  for (i = 0; i < num; i++)
    fprintf(file, " %s", vars[i]);
  fprintf(file, "\n"
    "orders:");
  for (i = 0; i < num; i++)
    fprintf(file, " %d", (unsigned) orders[i]);
  fprintf(file, "\n"
    "states: %u\n"
    "initial: %u\n"
    "bdd nodes: %u\n"
    "final:", a->ns, a->s, table->noelems);
  for (i = 0; i < a->ns; i++)
    fprintf(file, " %d", a->f[i]);
  fprintf(file, "\nbehaviour:");
  for (i = 0; i < a->ns; i++)
    fprintf(file, " %u", bdd_mark(a->bddm, a->q[i]) - 1);
  fprintf(file, "\nbdd:\n");
  for (i = 0; i < table->noelems; i++)
    fprintf(file, " %i %u %u\n", table->elms[i].idx, table->elms[i].lo,
        table->elms[i].hi);
  fprintf(file, "end\n");

  tableFree(table);
  if (filename)
    fclose(file);
  return 1;
}



/***************************************************************
 * Generating an example out of a dfa -- by Muath Alkhalaf
 * This will return a decoded example in a char *
 ***************************************************************/
// in case of choices we try to get a character that is readable i.e. alphabet
// That is why we check if < than 33
char arr_to_ascii(char * num){
  char c;
  int i = 0;
  int powr = (int)strlen(num) - 1;
  unsigned int result = 0;
  while ((c = num[i++]) != '\0'){
    if (c == 'X'){
      if (result < 33)
        c = '1';
      else
        c = '0';
    }
    result += (pow(2,powr--) * (((int) c) - 48));
  }
//  printf("%d\n", result);
  return (char) result;
}
// result returned by mona has a number of 1's before null
// so this will return the length upto the 1's not upto the
// null
unsigned int mystrlen(char * input){
  unsigned int i = 0;
  char c;
  while ((int)(c = input[i++]) != 1);
  i--;
  return i;
}
// returns a char * which contains an element of L(M)
// Could be null in case returned value is empty string or there
// is no solution
char *dfaGenerateExample(DFA* M, int var, unsigned indices[]){
  char *result = dfaMakeExample(M, 1, var, indices);
  if (result == NULL)
    return NULL;
//  printf("%s  %d\n", result, mystrlen(result));
  int jump = mystrlen(result) / 8;
  int i1, j1;
  // array of strings of 0's and 1's where each string represent an ASCII
  // value for a character on the automaton accepting path
//  char **decoded_result = malloc(sizeof(char *) * jump);
  char **decoded_result = calloc(jump, sizeof(char *));
  for (i1 = 0; i1 < jump; i1++) {
    char *temp_r = malloc(sizeof(char) * (8 + 1));// 1 for null
    int k = 0;
    for (j1 = i1; j1 < 8 * jump; j1 = j1 + jump) {
      *(temp_r + k) = result[j1];
      //      printf("%c", result[j1]);
      k++;
    }
    *(temp_r + k) = '\0';
    *(decoded_result + i1) = temp_r;
    //    printf("\n");
  }
//  char * final_result = malloc(sizeof(char) * (jump + 1));
  char * final_result = calloc(jump + 1, sizeof(char));
  for (i1 = 0; i1 < jump; i1++){
    final_result[i1] = arr_to_ascii(decoded_result[i1]);
  }
  final_result[jump+1] = '\0';
  return final_result;
}

/*******************************************
 PRINT FUNCTION
 *********************************************/

void flush_output(){
  fflush(stdout);
}

void print_bdd(bdd_manager *bddm, bdd_ptr b) {
  unsigned index;
  if (bdd_is_leaf(bddm, b)) {
    printf("(leafvalue: %d)", bdd_leaf_value(bddm, b));
  } else {
    index = bdd_ifindex(bddm, b);
    printf("(node %d, indx %d, high:", b, index);
    print_bdd(bddm, bdd_then(bddm, b));
    printf(")");
    printf("(node %d, indx %d, low:", b, index);
    print_bdd(bddm, bdd_else(bddm, b));
    printf(")");
  }
}
