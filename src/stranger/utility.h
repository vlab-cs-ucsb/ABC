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

#ifndef strangerlib_utility_h
#define strangerlib_utility_h

#include <stdbool.h>
#include <string.h>


typedef struct UIntArrayList_ {
    unsigned *list;
    size_t size;
    size_t index;
    bool sorted;
} UIntArrayList, *PUIntArrayList;
PUIntArrayList createUIntArrayList(size_t size);
void insertIntoUIntArrayList(PUIntArrayList pUIntArrayList, unsigned elem);
void insertIntoUIntSortedArrayList(PUIntArrayList pUIntArrayList, unsigned elem);
bool deleteFromUIntArrayList(PUIntArrayList pUIntArrayList, unsigned elem);
bool searchUIntArrayList(PUIntArrayList pUIntArrayList, unsigned elem, size_t *pIndex);
bool searchUIntArrayListBS(PUIntArrayList pUIntArrayList, unsigned elem, size_t *pIndex);
void sortUIntArrayList(PUIntArrayList pUIntArrayList);
void freeUIntArrayList(PUIntArrayList pUIntArrayList);


typedef struct StatePair_ {
    unsigned first;
    unsigned second;
    char *escapedChars;
} StatePair, *PStatePair;

typedef struct StatePairArrayList_ {
    PStatePair *list;
    size_t size;
    size_t index;
    bool sorted;
    size_t numOfEscapedChars;
} StatePairArrayList, *PStatePairArrayList;

PStatePairArrayList createStatePairArrayList(size_t size, size_t numOfEscapedChars);
void insertIntoStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, char escapeChar);
void insertIntoStatePairSortedArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, char escapeChar);
void addEscapeCharToStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, char escapeChar);
bool deleteFromStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned  first, unsigned second);
bool searchStatePairArrayList(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, size_t *pIndex);
bool searchStatePairArrayListBS(PStatePairArrayList pStatePairArrayList, unsigned first, unsigned second, size_t *pIndex);
void sortStatePairArrayList(PStatePairArrayList pStatePairArrayList);
void printStatePairArrayList(PStatePairArrayList pStatePairArrayList);
void freeStatePairArrayList(PStatePairArrayList pStatePairArrayList);

unsigned roundToNextPow2(unsigned v);

int intcmpfunc (const void * a, const void * b);

int statePaircmpfunc (const void * a, const void * b);

bool findStateBS(const unsigned states[], unsigned keyState, unsigned imin, unsigned imax);

bool findStatePairsBS(const PStatePair statePairs[], PStatePair keyStatePair, unsigned imin, unsigned imax);

char *commaprint(unsigned long long n);

#endif
