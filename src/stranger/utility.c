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

#include <stdio.h>
#include "utility.h"
#include "stranger.h"
#include "stranger_lib_internal.h"
#include <locale.h>
#include <limits.h>


#ifndef SIZE_T_MAX
	#define SIZE_T_MAX ULONG_MAX
#endif



int intcmpfunc (const void * a, const void * b)
{
    const unsigned *x = a, *y = b;
    if(*x > *y)
        return 1;
    else
        return(*x < *y) ? -1: 0;
}



unsigned roundToNextPow2(unsigned v){
    // compute the next highest power of 2 of 32-bit v
    v--;
    v |= v >> 1;
    v |= v >> 2;
    v |= v >> 4;
    v |= v >> 8;
    v |= v >> 16;
    v++;
    return v;
}


// searches for a state in an ordered list of states using binary search
// inclusive indices
//   0 <= imin when using truncate toward zero divide
//     imid = (imin+imax)/2;
//   imin unrestricted when using truncate toward minus infinity divide
//     imid = (imin+imax)>>1; or
//     imid = (int)floor((imin+imax)/2.0);
bool findStateBS(const unsigned states[], unsigned keyState, unsigned imin, unsigned imax)
{
    // continually narrow search until just one element remains
    while (imin < imax)
    {
        
        int imid = (imax + imin)/2;
        // code must guarantee the interval is reduced at each iteration
        assert(imid < imax);
        // note: 0 <= imin < imax implies imid will always be less than imax
        
        // reduce the search
        if (states[imid] < keyState)
            imin = imid + 1;
        else
            imax = imid;
    }
    // At exit of while:
    //   if A[] is empty, then imax < imin
    //   otherwise imax == imin
    
    // deferred test for equality
    if ((imax == imin) && (states[imin] == keyState))
        return true;
    else
        return false;
}



// searches for a state in an ordered list of states using binary search
// inclusive indices
//   0 <= imin when using truncate toward zero divide
//     imid = (imin+imax)/2;
//   imin unrestricted when using truncate toward minus infinity divide
//     imid = (imin+imax)>>1; or
//     imid = (int)floor((imin+imax)/2.0);
bool binarySearchUIntList(const unsigned list[], unsigned elem, size_t imin, size_t imax, size_t *pIndex)
{
    // continually narrow search until just one element remains
    while (imin < imax)
    {
        
        size_t imid = (imax + imin)/((size_t)2);
        // code must guarantee the interval is reduced at each iteration
        assert(imid < imax);
        // note: 0 <= imin < imax implies imid will always be less than imax
        
        // reduce the search
        if (list[imid] < elem)
            imin = imid + ((size_t) 1);
        else
            imax = imid;
    }
    // At exit of while:
    //   if A[] is empty, then imax < imin
    //   otherwise imax == imin
    
    // deferred test for equality
    if ((imax == imin) && (list[imin] == elem)){
        if (pIndex)
            *pIndex = imin;
        return true;
    }
    else {
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
}

char *commaprint(unsigned long long n)
{
	static int comma = '\0';
//	static char retbuf[(4*(sizeof(unsigned long * CHAR_BIT + 2)/3/3+1)];
    static char retbuf[30];
	char *p = &retbuf[sizeof(retbuf)-1];
	int i = 0;
    
	if(comma == '\0') {
		struct lconv *lcp = localeconv();
		if(lcp != NULL) {
			if(lcp->thousands_sep != NULL &&
               *lcp->thousands_sep != '\0')
				comma = *lcp->thousands_sep;
			else	comma = ',';
		}
	}
    
	*p = '\0';
    
	do {
		if(i%3 == 0 && i != 0)
			*--p = comma;
		*--p = '0' + n % 10;
		n /= 10;
		i++;
	} while(n != 0);
    
	return p;
}

PUIntArrayList createUIntArrayList(size_t initialSize){
    if (initialSize <= 0)
        initialSize = 32;
    PUIntArrayList pUIntArrayList = (PUIntArrayList) mem_alloc(sizeof(UIntArrayList));
    mem_zero(pUIntArrayList, sizeof(UIntArrayList));
    pUIntArrayList->list = (unsigned *) mem_alloc(initialSize * sizeof(unsigned));
    mem_zero(pUIntArrayList->list, initialSize * sizeof(unsigned));
    pUIntArrayList->size = initialSize;
    pUIntArrayList->index = (size_t) 0;
    pUIntArrayList->sorted = false;
    return pUIntArrayList;
}

void insertIntoUIntArrayList(PUIntArrayList pUIntArrayList, unsigned elem){
    //allocate more memory if needed
    if (pUIntArrayList->index == pUIntArrayList->size){
        //double the size
        pUIntArrayList->size *= (size_t) 2;
        pUIntArrayList->list = mem_resize(pUIntArrayList->list, pUIntArrayList->size * sizeof(unsigned));
        mem_zero(pUIntArrayList->list + pUIntArrayList->index, (pUIntArrayList->size - pUIntArrayList->index) * sizeof(unsigned));
    }
    pUIntArrayList->list[pUIntArrayList->index++] = elem;
    pUIntArrayList->sorted = false;
}

void insertIntoUIntSortedArrayList(PUIntArrayList pUIntArrayList, unsigned elem){
    /*   assert either empty list or already sorted   */
    assert(pUIntArrayList->index == 0 || pUIntArrayList->sorted == true);
    
    /*   allocate more memory if needed    */
    
    if (pUIntArrayList->index == pUIntArrayList->size){
        //double the size
        pUIntArrayList->size *= (size_t) 2;
        pUIntArrayList->list = mem_resize(pUIntArrayList->list, pUIntArrayList->size * sizeof(unsigned));
        mem_zero(pUIntArrayList->list + pUIntArrayList->index, (pUIntArrayList->size - pUIntArrayList->index) * sizeof(unsigned));
    }

    /*     insert elem    */
    
    if (pUIntArrayList->index == 0){
        pUIntArrayList->list[pUIntArrayList->index++] = elem;
        pUIntArrayList->sorted = true;
    }
    else {
        //insertion sort
        size_t i;
        //shift right for elements greater than current element
        for (i = pUIntArrayList->index; i > 0  && elem < pUIntArrayList->list[i - 1]; i--){
            pUIntArrayList->list[i] = pUIntArrayList->list[i-1];
        }
        pUIntArrayList->list[i] = elem;
        pUIntArrayList->index++;
    }
}

bool deleteFromUIntArrayList(PUIntArrayList pUIntArrayList, unsigned elem){
    size_t elemIndex;
    //serach for elem and store its index in elemIndex
    if (searchUIntArrayList(pUIntArrayList, elem, &elemIndex)){
        size_t i;
        //shift left
        for (i = elemIndex; i < pUIntArrayList->index; i++) {
            pUIntArrayList->list[i] = pUIntArrayList->list[i + 1];
        }
        pUIntArrayList->index--;
        return true;//elem deleted
    }
    else {
        return false;//elem not found
    }
}

bool searchUIntArrayList(PUIntArrayList pUIntArrayList, unsigned elem, size_t *pIndex){
    if (pUIntArrayList->index == 0){
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
    if (pUIntArrayList->sorted){
        return (searchUIntArrayListBS(pUIntArrayList, elem, pIndex));
    }
    else {
        size_t i;
        for (i = 0; i < pUIntArrayList->index; i++){
            if (pUIntArrayList->list[i] == elem){
                if (pIndex)
                    *pIndex = i;
                return true;
            }
        }
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
}

bool searchUIntArrayListBS(PUIntArrayList pUIntArrayList, unsigned elem, size_t *pIndex){
    if (pUIntArrayList->index == 0){
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
    if (!pUIntArrayList->sorted)
        sortUIntArrayList(pUIntArrayList);
    
    return binarySearchUIntList(pUIntArrayList->list, elem, 0, pUIntArrayList->index - 1, pIndex);
}

void sortUIntArrayList(PUIntArrayList pUIntArrayList){
    qsort(pUIntArrayList->list, pUIntArrayList->index, sizeof(unsigned), intcmpfunc);
    pUIntArrayList->sorted = true;
}

void freeUIntArrayList(PUIntArrayList pUIntArrayList){
    free(pUIntArrayList->list);
    free(pUIntArrayList);
}

/************************************************************************************/
/************************************************************************************/
/************************************************************************************/

int compareStatePairs(const PStatePair x, const PStatePair y){
    if ( x->first > y->first )
        return 1;
    else if ( x->first < y->first )
        return -1;
    else if ( x->second > y->second )
        return 1;
    else if ( x->second < y->second )
        return -1;
    else
        return 0;

}

int statePaircmpfunc (const void * a, const void * b)
{
    const PStatePair *x = (PStatePair *) a, *y = (PStatePair *) b;
    if ( (*x)->first > (*y)->first )
        return 1;
    else if ( (*x)->first < (*y)->first )
        return -1;
    else if ( (*x)->second > (*y)->second )
        return 1;
    else if ( (*x)->second < (*y)->second )
        return -1;
    else
        return 0;
}

bool firstPairLessThanSecond(PStatePair p1, PStatePair p2){
    if ( compareStatePairs(p1, p2) == -1 )
        return true;
    else
        return false;

}

// searches for a state in an ordered list of states using binary search
// inclusive indices
//   0 <= imin when using truncate toward zero divide
//     imid = (imin+imax)/2;
//   imin unrestricted when using truncate toward minus infinity divide
//     imid = (imin+imax)>>1; or
//     imid = (int)floor((imin+imax)/2.0);
bool binarySearchStatePairList(const PStatePair list[], PStatePair elem, size_t imin, size_t imax, size_t *pIndex)
{
    // continually narrow search until just one element remains
    while (imin < imax)
    {
        
        size_t imid = (imax + imin)/((size_t)2);
        // code must guarantee the interval is reduced at each iteration
        assert(imid < imax);
        // note: 0 <= imin < imax implies imid will always be less than imax
        
        // reduce the search
        if (firstPairLessThanSecond(list[imid], elem))
            imin = imid + ((size_t) 1);
        else
            imax = imid;
    }
    // At exit of while:
    //   if A[] is empty, then imax < imin
    //   otherwise imax == imin
    
    // deferred test for equality
    if ((imax == imin) && compareStatePairs(list[imin], elem) == 0){
        if (pIndex)
            *pIndex = imin;
        return true;
    }
    else {
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
}


PStatePairArrayList createStatePairArrayList(size_t initialSize, size_t numOfEscapedChars){
    if (initialSize <= 0)
        initialSize = 32;
    
    PStatePairArrayList pStatePairArrayList = (PStatePairArrayList) mem_alloc(sizeof(StatePairArrayList));
    mem_zero(pStatePairArrayList, sizeof(StatePairArrayList));
    
    pStatePairArrayList->list = (PStatePair *) mem_alloc(initialSize * sizeof(PStatePair));
    mem_zero(pStatePairArrayList->list, initialSize * sizeof(PStatePair));
    
    pStatePairArrayList->size = initialSize;
    pStatePairArrayList->index = (size_t) 0;
    pStatePairArrayList->sorted = false;
    pStatePairArrayList->numOfEscapedChars = numOfEscapedChars;
    
    return pStatePairArrayList;
}

void insertIntoStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, char escapeChar){
    assert(escapeChar != (char) 255);
    //allocate more memory if needed
    if (pStatePairArrayList->index == pStatePairArrayList->size){
        //double the size
        pStatePairArrayList->size *= (size_t) 2;
        pStatePairArrayList->list = (PStatePair *) mem_resize(pStatePairArrayList->list, pStatePairArrayList->size * sizeof(PStatePair));
        mem_zero(pStatePairArrayList->list + pStatePairArrayList->index, (pStatePairArrayList->size - pStatePairArrayList->index) * sizeof(PStatePair));
    }
    
    PStatePair pStatePair = (PStatePair) mem_alloc((sizeof(StatePair)));
    mem_zero(pStatePair, sizeof(StatePair));
    pStatePair->first = first;
    pStatePair->second = second;
    pStatePair->escapedChars = (char *) mem_alloc( pStatePairArrayList->numOfEscapedChars * sizeof(char));
    memset(pStatePair->escapedChars, (char) 255, pStatePairArrayList->numOfEscapedChars * sizeof(char));
    pStatePair->escapedChars[0] = escapeChar;
    
    pStatePairArrayList->list[pStatePairArrayList->index++] = pStatePair;
    pStatePairArrayList->sorted = false;
}

void insertIntoStatePairSortedArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, char escapeChar){
    /*   assert either empty list or already sorted   */
    assert(pStatePairArrayList->index == 0 || pStatePairArrayList->sorted == true);
    assert(escapeChar != (char) 255);
    /*   allocate more memory if needed    */
    
    if (pStatePairArrayList->index == pStatePairArrayList->size){
        //double the size
        pStatePairArrayList->size *= (size_t) 2;
        pStatePairArrayList->list = (PStatePair *) mem_resize(pStatePairArrayList->list, pStatePairArrayList->size * sizeof(PStatePair));
        mem_zero(pStatePairArrayList->list + pStatePairArrayList->index, (pStatePairArrayList->size - pStatePairArrayList->index) * sizeof(PStatePair));
    }
    
    /*    create item      */
    
    PStatePair pStatePair = (PStatePair) mem_alloc((sizeof(StatePair)));
    mem_zero(pStatePair, sizeof(StatePair));
    pStatePair->first = first;
    pStatePair->second = second;
    pStatePair->escapedChars = (char *) mem_alloc( pStatePairArrayList->numOfEscapedChars * sizeof(char));
    memset(pStatePair->escapedChars, (char) 255, pStatePairArrayList->numOfEscapedChars * sizeof(char));
    pStatePair->escapedChars[0] = escapeChar;
    
    /*     insert elem    */
    
    if (pStatePairArrayList->index == 0){
        pStatePairArrayList->list[pStatePairArrayList->index++] = pStatePair;
        pStatePairArrayList->sorted = true;
    }
    else {
        //insertion sort
        size_t i;
        //shift right for elements greater than current element
        for (i = pStatePairArrayList->index; i > 0  && firstPairLessThanSecond(pStatePair, pStatePairArrayList->list[i - 1]); i--){
            pStatePairArrayList->list[i] = pStatePairArrayList->list[i-1];
        }
        pStatePairArrayList->list[i] = pStatePair;
        pStatePairArrayList->index++;
    }
}

void addEscapeCharToStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, char escapeChar){
    size_t index;
    assert(escapeChar != (char) 255);
    /*    add to existing   */
    
    if (searchStatePairArrayList(pStatePairArrayList, first, second, &index)){
        PStatePair pStatePair = pStatePairArrayList->list[index];
        size_t i = 0;
        for (i = 0; pStatePair->escapedChars[i] != (char) 255 && pStatePair->escapedChars[i] != escapeChar && i < pStatePairArrayList->numOfEscapedChars; i++);
        assert(i < pStatePairArrayList->numOfEscapedChars);
        pStatePair->escapedChars[i] = escapeChar;
    }
    
    /*    insert a new one   */
    
    else {
        insertIntoStatePairSortedArrayList(pStatePairArrayList, first, second, escapeChar);
    }
}


bool deleteFromStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second){
    size_t elemIndex;
    //serach for elem and store its index in elemIndex
    if (searchStatePairArrayList(pStatePairArrayList, first, second, &elemIndex)){
        size_t i;
        free(pStatePairArrayList->list[elemIndex]->escapedChars);
        free(pStatePairArrayList->list[elemIndex]);
        //shift left
        for (i = elemIndex; i < pStatePairArrayList->index; i++) {
            pStatePairArrayList->list[i] = pStatePairArrayList->list[i + 1];
        }
        pStatePairArrayList->index--;
        return true;//elem deleted
    }
    else {
        return false;//elem not found
    }
}

bool searchStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, size_t *pIndex){
    if (pStatePairArrayList->index == 0){
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
    if (pStatePairArrayList->sorted){
        return (searchStatePairArrayListBS(pStatePairArrayList, first, second, pIndex));
    }
    else {
        size_t i;
        
        /*    create item      */
        
        PStatePair pStatePair = (PStatePair) mem_alloc((sizeof(StatePair)));
        mem_zero(pStatePair, sizeof(StatePair));
        pStatePair->first = first;
        pStatePair->second = second;

        
        for (i = 0; i < pStatePairArrayList->index; i++){
            if (compareStatePairs(pStatePairArrayList->list[i], pStatePair) == 0){
                if (pIndex)
                    *pIndex = i;
                free(pStatePair);
                return true;
            }
        }
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        free(pStatePair);
        return false;
    }
}

bool searchStatePairArrayListBS(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, size_t *pIndex){
    if (pStatePairArrayList->index == 0){
        if (pIndex)
            *pIndex = SIZE_T_MAX;
        return false;
    }
    if (!pStatePairArrayList->sorted)
        sortStatePairArrayList(pStatePairArrayList);

    /*    create item      */
    
    PStatePair pStatePair = (PStatePair) mem_alloc((sizeof(StatePair)));
    mem_zero(pStatePair, sizeof(StatePair));
    pStatePair->first = first;
    pStatePair->second = second;
    
    bool result = binarySearchStatePairList(pStatePairArrayList->list, pStatePair, 0, pStatePairArrayList->index - 1, pIndex);
    free(pStatePair);
    return result;
}

void sortStatePairArrayList(PStatePairArrayList pStatePairArrayList){
    qsort(pStatePairArrayList->list, pStatePairArrayList->index, sizeof(PStatePair), statePaircmpfunc);
    pStatePairArrayList->sorted = true;
}

void printStatePairArrayList(PStatePairArrayList pStatePairArrayList ){
    size_t i;
    for (i = 0; i < pStatePairArrayList->index; i++) {
        printf("%d -> %d: ", pStatePairArrayList->list[i]->first, pStatePairArrayList->list[i]->second);
        size_t j;
        for (j = 0; pStatePairArrayList->list[i]->escapedChars[j] != (char) 255 && j < pStatePairArrayList->numOfEscapedChars; j++)
            printf("%c, ", pStatePairArrayList->list[i]->escapedChars[j]);
        printf("\n");
    }
}


void freeStatePairArrayList(PStatePairArrayList pStatePairArrayList){
    int i;
    for (i = 0; i < pStatePairArrayList->index; i++){
        free(pStatePairArrayList->list[i]->escapedChars);
        free(pStatePairArrayList->list[i]);
    }
    free(pStatePairArrayList->list);
    free(pStatePairArrayList);
}
