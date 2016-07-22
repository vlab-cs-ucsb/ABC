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


#ifdef __cplusplus
extern "C" {
#endif


#ifndef STRANGER_LIB_INTERNAL_H_
#define STRANGER_LIB_INTERNAL_H_

#include "stranger.h"
#include "mona/mem.h"
  
/*when building an NFA, do we favor
 NFA with larger language but less
 non-deterministic transitions to
 sink*/
#define MORE_WORDS_LESS_NDTRANS 0

struct int_list_type *new_ilt();
int find_sink(DFA *M);
struct int_list_type *enqueue(struct int_list_type *list, int value);
int dequeue(struct int_list_type *list);
void print_ilt(struct int_list_type *list);
int isEqual2Lambda(char *str, char* lambda, int var);
int get_hsig(int i);
int* allocateArbitraryIndex(int length);
void set_bitvalue(char *bit, int length, int value);
void free_ilt(struct int_list_type *list);
int state_reachable(DFA *M, int dest, int var, int *indices);



DFA *mdfaOneToManyTrackNoLambda( DFA* M, int m, int i_track, int var, int* indices);
DFA* mdfaGPrefixM(DFA* M, int i_track, int j_track, int k_track, int m, int var, int* indices);
DFA *dfaGetTrack(DFA *M, int i_track, int m, int var, int* indices);
DFA* mdfaGSuffixM(DFA* M, int i_track, int j_track, int k_track, int m, int var, int* indices);
DFA *dfaGetTrackNoPreLambda(DFA *M, int i_track, int m, int var, int* indices);

DFA* mdfaMEqualLRc(DFA *M1, DFA *M2, char* str, int i_track, int j_track, int m, int var, int* indices);

char *getSharp1(int k);
char *getSharp0(int k);
char *bintostr(unsigned long n, int k);
char *bintostrWithExtraBit(unsigned long n, int k);
unsigned char strtobin(char* binChar, int var);
DFA *dfaSharpStringWithExtraBit(int var, int *indices);
unsigned* allocateAscIIIndexUnsigned(int length);
char *getSharp1(int k);
char *bintostr(unsigned long n, int k);
int check_init_reachable(DFA *M, int var, int *indices);
struct int_list_type *reachable_states_lambda_in_nout(DFA *M, char *lambda, int var);
int check_accept(DFA *M, struct int_list_type *states);
int isIncludeLambda(char *str, char* lambda, int var);
    void removeTransitionOnChars(char* monaCharacter, char **charachters, int numOfChars, int var, char** result, int* pSize);


struct int_list_type **get_match_exclude_self(DFA *M, int var, int *indices);
int get_maxcount(struct int_list_type **pairs, int size);
struct int_list_type **get_match(DFA *M, int var, int *indices);
char *bintostrWithExtraBitsZero(unsigned long n, int k, int aux);
int get_number_of_sharp1_state(struct int_list_type **pairs, int size);

DFA *dfa_replace_step1_duplicate(DFA *M, int var, int *indices);
DFA *dfa_replace_step2_match_compliment(DFA *M, int var, int *indices);
DFA *dfa_general_replace_extrabit(DFA* M1, DFA* M2, DFA* M3, int var, int* indices);
DFA* dfa_pre_replace(DFA* M1, DFA* M2, DFA* M3, int var, int* indices);
DFA* dfa_pre_replace_str(DFA* M1, DFA* M2, char *str, int var, int* indices);
DFA *dfa_replace(DFA *M1, DFA *M2, DFA *M3, int var, int *indices);
DFA *dfa_insert_everywhere(DFA *M, DFA* Mr, int var, int *indices);
    
int* allocateMultipleAscIIIndex(int m, int length);


typedef struct CharPair_ {
	unsigned char first;
	unsigned char last;
} CharPair, *pCharPair;
void getTransitionChars(char* transitions, int var, pCharPair result[], int* pSize);
char** mergeCharRanges(pCharPair charRanges[], int* p_size);


int check_value(struct int_list_type *list, int value);
DFA *dfa_union_empty_M(DFA *M, int var, int *indices);




#endif /* STRANGER_LIB_INTERNAL_H_ */

    
#ifdef __cplusplus
}
#endif
