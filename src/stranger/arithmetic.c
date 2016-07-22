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
 * Authors: Constantinos Bartzis, Fang Yu
 */


#include "stranger.h"

/*****************************************************************************

 Constantino's code


 *********************************************************************************/


/*BEGIN ARITHMATIC AUTOMATA CONSTRUCTION************************************************************************/
//Copied from lcautocode.c
//Added by Fang 09/30/2008


struct map_ent {
	int i, ir; //state index
	int s, sr; //status: 0=not yet processed
//        1=to be expanded
//        2=done
//ir and sr are for the rejecting clone
};

//returns the gcd of integers x and y
int gcd(int x, int y) {
	int temp;
	while (y != 0) {
		temp = x % y;
		x = y;
		y = temp;
	}
	if (x > 0)
		return x;
	else
		return -x;
}

//returns the sum of the coefficients for the non-zero bits up to the k-th
//ith coefficient corresponds to the ith least-significant bit
int count_ones(long n, int k, int *coeffs) {
	int ones = 0;
	for (k--; k >= 0; k--) {
		if (n & 1)
			ones += coeffs[k];
		n >>= 1;
	}
	return ones;
}

//reduces the coefficients by dividing them with their gcd
//kind: 0 for = ,  1 for <
//returns 1 for contradictions
int preprocess(int vars, int *coef, int *cons, int kind) {
	int i;
	int temp = abs(coef[0]);
	for (i = 1; i < vars; i++)
		temp = gcd(abs(coef[i]), temp);
	for (i = 0; i < vars; i++)
		coef[i] = coef[i] / temp;
	if (kind == 0) {
		if (*cons % temp == 0) {
			*cons = *cons / temp;
			return 0;
		} else
			return 1;
	}
	if (kind == 1) {
		*cons = *cons + temp - 1;
		if (*cons >= 0)
			*cons = *cons / temp;
		else
			*cons = (*cons + 1) / temp - 1;
		return 0;
	}
	return 0;
}

DFA *build_DFA_eq_nocoef(int vars, int constant, int *indices) {
	int i, j;
	char *s = malloc(vars + 1);
	s[vars] = '\0';

	if (constant == 0) {
		dfaSetup(2, vars, indices);

		dfaAllocExceptions(1);
		for (i = 0; i < vars; i++)
			s[i] = '0';
		dfaStoreException(0, s);
		dfaStoreState(1);

		dfaAllocExceptions(0);
		dfaStoreState(1);

		return dfaBuild("+-");
	}

	if (constant == 1) {
		dfaSetup(3, vars, indices);

		dfaAllocExceptions(vars);
		for (i = 0; i < vars; i++) {
			for (j = 0; j < vars; j++)
				if (j == i)
					s[j] = '1';
				else
					s[j] = '0';
			dfaStoreException(1, s);
		}
		dfaStoreState(2);

		dfaAllocExceptions(1);
		for (i = 0; i < vars; i++)
			s[i] = '0';
		dfaStoreException(1, s);
		dfaStoreState(2);

		dfaAllocExceptions(0);
		dfaStoreState(2);

		return dfaBuild("-+-");
	}
	return 0; //added by Muath to avoid compiler warning
}

//Constructs a DFA for the equation coeffs*variables+constant=0
DFA *build_DFA_eq(int vars, int *coeffs, int constant, int *indices) {
	int min, max, states, next_index, next_label, result, target, count;
	long i;
	unsigned long j, transitions;
	struct map_ent *map;
	char *statuces;
	DFA *equality, *temp;
	int coef0;

	if (preprocess(vars, coeffs, &constant, 0))
		return dfaFalse();

	if (constant == 0) {
		coef0 = coeffs[0];
		for (i = 1; (coeffs[i] == coef0) && (i < vars); i++)
			;
		if (i == vars)
			return build_DFA_eq_nocoef(vars, 0, indices);
	}

	else {
		coef0 = coeffs[0];
		for (i = 1; (coeffs[i] == coef0) && (i < vars); i++)
			;
		if (i == vars) {
			if (((constant == 1) && (coef0 < 0)) || ((constant == -1) && (coef0
					> 0)))
				return build_DFA_eq_nocoef(vars, 1, indices);
		}
	}

	//initialization

	min = 0;
	max = 0;
	for (i = 0; i < vars; i++)
		if (coeffs[i] > 0)
			max += coeffs[i];
		else
			min += coeffs[i];

	if (constant > max)
		max = constant;
	else if (constant < min)
		min = constant;
	states = max - min + 2;

	//This array maps state labels (carries) to state indices
	map = (struct map_ent *) malloc(states * sizeof(struct map_ent)) - min;
	for (i = min; i < max + 2; i++) {
		map[i].s = 0;
		map[i].i = -1;
	}
	map[constant].s = 1; //the first state to be expanded
	next_index = 0; //the next available state index
	next_label = constant; //the next available state label
	map[constant].i = 0;
	count = 0;

	transitions = 1 << vars; //number of transitions from each state

	//Begin building
	dfaSetup(states, vars, indices);

	while (next_label < max + 1) { //there is a state to expand (excuding sink)
		map[next_label].s = 2;
		dfaAllocExceptions(transitions / 2);
		for (j = 0; j < transitions; j++) {
			result = next_label + count_ones(j, vars, coeffs);
			if (!(result & 1)) {
				target = result / 2;
				if (map[target].s == 0) {
					map[target].s = 1;
					next_index++;
					map[target].i = next_index;
				}
				dfaStoreException(map[target].i, bintostr(j, vars));
			}
		}
		dfaStoreState(states - 1);
		count++;
		for (next_label = min; (next_label <= max) && (map[next_label].i
				!= count); next_label++)
			;
		//find next state to expand
	}
	for (; count < states; count++) {
		dfaAllocExceptions(0);
		dfaStoreState(states - 1);
	}

	//define accepting and rejecting states
	statuces = (char *) malloc(states + 1);
	for (i = 0; i < states; i++)
		statuces[i] = '-';
	if (map[0].s == 2)
		statuces[map[0].i] = '+';
	statuces[states] = '\0';
	temp = dfaBuild(statuces);
	equality = dfaMinimize(temp);
	dfaFree(temp);
	return equality;
}

//Constructs a DFA for the equation coeffs*variables+constant=0
DFA *build_DFA_eq_new(int vars, int *coeffs, int constant, int *indices) {
	int min, max, states, next_index, next_label, result, target, count;
	long i;
	unsigned long j, transitions;
	struct map_ent *map;
	char *statuces;
	DFA *equality, *temp;

	if (preprocess(vars, coeffs, &constant, 0))
		return dfaFalse();
	//initialization

	min = 0;
	max = 0;
	for (i = 0; i < vars; i++)
		if (coeffs[i] > 0)
			max += coeffs[i];
		else
			min += coeffs[i];

	if (constant > max)
		max = constant;
	else if (constant < min)
		min = constant;
	states = max - min + 2;

	//This array maps state labels (carries) to state indices
	map = (struct map_ent *) malloc(states * sizeof(struct map_ent)) - min;
	for (i = min; i < max + 2; i++) {
		map[i].s = 0;
		map[i].i = -1;
	}
	map[constant].s = 1; //the first state to be expanded
	next_index = 0; //the next available state index
	next_label = constant; //the next available state label
	map[constant].i = 0;
	count = 0;

	transitions = 1 << vars; //number of transitions from each state

	//Begin building
	dfaSetup(states + 1, vars, indices);

	dfaAllocExceptions(0);
	dfaStoreState(1);
	//count++;

	while (next_label < max + 1) { //there is a state to expand (excuding sink)
		map[next_label].s = 2;
		dfaAllocExceptions(transitions / 2);
		for (j = 0; j < transitions; j++) {
			result = next_label + count_ones(j, vars, coeffs);
			if (!(result & 1)) {
				target = result / 2;
				if (map[target].s == 0) {
					map[target].s = 1;
					next_index++;
					map[target].i = next_index;
				}
				dfaStoreException(map[target].i + 1, bintostr(j, vars));
			}
		}
		dfaStoreState(states);
		count++;
		for (next_label = min; (next_label <= max) && (map[next_label].i
				!= count); next_label++)
			;
		//find next state to expand
	}
	for (; count <= states; count++) {
		dfaAllocExceptions(0);
		dfaStoreState(states);
	}

	//define accepting and rejecting states
	statuces = (char *) malloc(states + 2);
	for (i = 0; i <= states; i++)
		statuces[i] = '-';
	if (map[0].s == 2)
		statuces[map[0].i + 1] = '+';
	statuces[states + 1] = '\0';
	temp = dfaBuild(statuces);
	equality = dfaMinimize(temp);
	dfaFree(temp);
	return equality;
}

// Constructs a DFA for the equation coeffs*variables+constant=0
// in two's complement arithmetic
DFA *build_DFA_eq_2sc(int vars, int *coeffs, int constant, int *indices) {
	int min, max, states, next_index, next_label, result, target, count;
	long i;
	unsigned long j, transitions;
	struct map_ent *map;
	char *statuces;
	DFA *equality, *temp;

	if (preprocess(vars, coeffs, &constant, 0))
		return dfaFalse();

	//initialization

	min = 0;
	max = 0;
	for (i = 0; i < vars; i++)
		if (coeffs[i] > 0)
			max += coeffs[i];
		else
			min += coeffs[i];

	if (constant > max)
		max = constant;
	else if (constant < min)
		min = constant;
	states = 2 * max - 2 * min + 3;

	//This array maps state labels (carries) to state indices
	map = (struct map_ent *) malloc(states * sizeof(struct map_ent)) - min;
	for (i = min; i < max + 1; i++) {
		map[i].s = 0;
		map[i].sr = 0;
		map[i].i = -1;
		map[i].ir = -1;
	}
	map[constant].sr = 1; //the first state to be expanded
	next_index = 0; //the next available state index
	next_label = constant; //the next available state label
	map[constant].i = -1;
	map[constant].ir = 0;
	count = 0;

	transitions = 1 << vars; //number of transitions from each state

	//Begin building
	dfaSetup(states, vars, indices);

	while (next_label < max + 1) { //there is a state to expand (excuding sink)
		if (map[next_label].i == count)
			map[next_label].s = 2;
		else
			map[next_label].sr = 2;
		dfaAllocExceptions(transitions / 2);
		for (j = 0; j < transitions; j++) {
			result = next_label + count_ones(j, vars, coeffs);
			if (!(result & 1)) {
				target = result / 2;
				if (target == next_label) {
					if (map[target].s == 0) {
						map[target].s = 1;
						next_index++;
						map[target].i = next_index;
					}
					dfaStoreException(map[target].i, bintostr(j, vars));
				} else {
					if (map[target].sr == 0) {
						map[target].sr = 1;
						next_index++;
						map[target].ir = next_index;
					}
					dfaStoreException(map[target].ir, bintostr(j, vars));
				}
			}
		}
		dfaStoreState(states - 1);
		count++;
		for (next_label = min; (next_label <= max) && (map[next_label].i
				!= count) && (map[next_label].ir != count); next_label++)
			;
		//find next state to expand
	}
	for (; count < states; count++) {
		dfaAllocExceptions(0);
		dfaStoreState(states - 1);
	}

	//define accepting and rejecting states
	statuces = (char *) malloc(states + 1);
	for (i = 0; i < states; i++)
		statuces[i] = '-';
	for (next_label = min; next_label <= max; next_label++)
		if (map[next_label].s == 2)
			statuces[map[next_label].i] = '+';
	statuces[states] = '\0';
	temp = dfaBuild(statuces);
	equality = dfaMinimize(temp);
	dfaFree(temp);
	return equality;
}

//Constructs a DFA for the inequation coeffs*variables+constant<0
DFA *build_DFA_ineq(int vars, int *coeffs, int constant, int *indices) {
	int min, max, states, next_index, next_label, result, target, count;
	long i, transitions;
	unsigned long j;
	struct map_ent *map;
	char *statuces;
	DFA *inequality, *temp;

	preprocess(vars, coeffs, &constant, 1);

	//initialization

	min = 0;
	max = 0;
	for (i = 0; i < vars; i++)
		if (coeffs[i] > 0)
			max += coeffs[i];
		else
			min += coeffs[i];

	if (constant > max)
		max = constant;
	else if (constant < min)
		min = constant;
	states = max - min + 1;

	//This array maps state labels (carries) to state indices
	map = (struct map_ent *) malloc(states * sizeof(struct map_ent)) - min;
	for (i = min; i < max + 1; i++) {
		map[i].s = 0;
		map[i].i = -1;
	}
	map[constant].s = 1; //the first state to be expanded
	next_index = 0; //the next available state index
	next_label = constant; //the next available state label
	map[constant].i = 0;
	count = 0;

	transitions = 1 << vars; //number of transitions from each state

	//Begin building
	dfaSetup(states, vars, indices);

	while (next_label < max + 1) { //there is a state to expand
		map[next_label].s = 2;
		dfaAllocExceptions(transitions);
		for (j = 0; j < transitions; j++) {
			result = next_label + count_ones(j, vars, coeffs);
			if (result >= 0)
				target = result / 2;
			else
				target = (result - 1) / 2;
			if (map[target].s == 0) {
				map[target].s = 1;
				next_index++;
				map[target].i = next_index;
			}
			dfaStoreException(map[target].i, bintostr(j, vars));
		}
		dfaStoreState(count);
		count++;
		for (next_label = min; (next_label <= max) && (map[next_label].i
				!= count); next_label++)
			;
		//find next state to expand
	}
	for (i = count; i < states; i++) {
		dfaAllocExceptions(0);
		dfaStoreState(i);
	}

	//define accepting and rejecting states
	statuces = (char *) malloc(states + 1);
	for (i = 0; i < count; i++)
		statuces[i] = '-';
	for (; i < states; i++)
		statuces[i] = '0';
	for (i = min; i < 0; i++)
		if (map[i].s == 2)
			statuces[map[i].i] = '+';
	statuces[states] = '\0';
	temp = dfaBuild(statuces);
	temp->ns -= states - count;
	inequality = dfaMinimize(temp);
	return inequality;
}

//Constructs a DFA for the inequation coeffs*variables+constant<0
DFA *build_DFA_ineq_new(int vars, int *coeffs, int constant, int *indices) {
	int min, max, states, next_index, next_label, result, target, count;
	long i, transitions;
	unsigned long j;
	struct map_ent *map;
	char *statuces;
	DFA *inequality, *temp;

	preprocess(vars, coeffs, &constant, 1);

	//initialization

	min = 0;
	max = 0;
	for (i = 0; i < vars; i++)
		if (coeffs[i] > 0)
			max += coeffs[i];
		else
			min += coeffs[i];

	if (constant > max)
		max = constant;
	else if (constant < min)
		min = constant;
	states = max - min + 1;

	//This array maps state labels (carries) to state indices
	map = (struct map_ent *) malloc(states * sizeof(struct map_ent)) - min;
	for (i = min; i < max + 1; i++) {
		map[i].s = 0;
		map[i].i = -1;
	}
	map[constant].s = 1; //the first state to be expanded
	next_index = 0; //the next available state index
	next_label = constant; //the next available state label
	map[constant].i = 0;
	count = 0;

	transitions = 1 << vars; //number of transitions from each state

	//Begin building
	dfaSetup(states + 1, vars, indices);

	dfaAllocExceptions(0);
	dfaStoreState(1);
	//count++;

	while (next_label < max + 1) { //there is a state to expand
		map[next_label].s = 2;
		dfaAllocExceptions(transitions);
		for (j = 0; j < transitions; j++) {
			result = next_label + count_ones(j, vars, coeffs);
			if (result >= 0)
				target = result / 2;
			else
				target = (result - 1) / 2;
			if (map[target].s == 0) {
				map[target].s = 1;
				next_index++;
				map[target].i = next_index;
			}
			dfaStoreException(map[target].i + 1, bintostr(j, vars));
		}
		dfaStoreState(count);
		count++;
		for (next_label = min; (next_label <= max) && (map[next_label].i
				!= count); next_label++)
			;
		//find next state to expand
	}
	for (i = count; i <= states; i++) {
		dfaAllocExceptions(0);
		dfaStoreState(i);
	}

	//define accepting and rejecting states
	statuces = (char *) malloc(states + 2);
	for (i = 0; i <= count; i++)
		statuces[i] = '-';
	for (; i <= states; i++)
		statuces[i] = '0';
	for (i = min; i < 0; i++)
		if (map[i].s == 2)
			statuces[map[i].i + 1] = '+';
	statuces[states + 1] = '\0';
	temp = dfaBuild(statuces);
	temp->ns -= states - count;
	inequality = dfaMinimize(temp);
	return inequality;
}

// Constructs a DFA for the inequation coeffs*variables+constant<0
// in two's complement arithmetic
DFA *build_DFA_ineq_2sc(int vars, int *coeffs, int constant, int *indices) {
	int min, max, states, next_index, next_label, result, target, count;
	long i;
	unsigned long j, transitions;
	struct map_ent *map;
	char *statuces;
	DFA *inequality, *temp;
	//int write1, overbits, label1, label2, co;
	int write1, label1, label2, co;



	preprocess(vars, coeffs, &constant, 1);

	//initialization

	min = 0;
	max = 0;
	for (i = 0; i < vars; i++)
		if (coeffs[i] > 0)
			max += coeffs[i];
		else
			min += coeffs[i];

	if (constant > max)
		max = constant;
	else if (constant < min)
		min = constant;
	states = max - min + 1;
	//overbits= ceil(log(states)/log(2));
	states *= 2;

	//This array maps state labels (carries) to state indices
	map = (struct map_ent *) malloc(states * sizeof(struct map_ent)) - min;
	for (i = min; i < max + 1; i++) {
		map[i].s = 0;
		map[i].sr = 0;
		map[i].i = -1;
		map[i].ir = -1;
	}
	map[constant].sr = 1; //the first state to be expanded
	next_index = 0; //the next available state index
	next_label = constant; //the next available state label
	map[constant].i = -1;
	map[constant].ir = 0;
	count = 0;

	transitions = 1 << vars; //number of transitions from each state

	//Begin building
	dfaSetup(states, vars, indices);

	while (next_label < max + 1) { //there is a state to expand (excuding sink)
		if (map[next_label].i == count)
			map[next_label].s = 2;
		else
			map[next_label].sr = 2;
		dfaAllocExceptions(transitions);
		for (j = 0; j < transitions; j++) {
			co = count_ones(j, vars, coeffs);
			result = next_label + co;
			if (result >= 0)
				target = result / 2;
			else
				target = (result - 1) / 2;
			write1 = result & 1;
			label1 = next_label;
			label2 = target;

			while (label1 != label2) {
				label1 = label2;
				result = label1 + co;
				if (result >= 0)
					label2 = result / 2;
				else
					label2 = (result - 1) / 2;
				write1 = result & 1;
			}

			if (write1) {
				if (map[target].s == 0) {
					map[target].s = 1;
					next_index++;
					map[target].i = next_index;
				}
				dfaStoreException(map[target].i, bintostr(j, vars));
			} else {
				if (map[target].sr == 0) {
					map[target].sr = 1;
					next_index++;
					map[target].ir = next_index;
				}
				dfaStoreException(map[target].ir, bintostr(j, vars));
			}
		}
		dfaStoreState(count);
		count++;
		for (next_label = min; (next_label <= max) && (map[next_label].i
				!= count) && (map[next_label].ir != count); next_label++)
			;
		//find next state to expand
	}
	for (i = count; i < states; i++) {
		dfaAllocExceptions(0);
		dfaStoreState(i);
	}

	//define accepting and rejecting states
	statuces = (char *) malloc(states + 1);
	for (i = 0; i < states; i++)
		statuces[i] = '-';
	for (next_label = min; next_label <= max; next_label++)
		if (map[next_label].s == 2)
			statuces[map[next_label].i] = '+';
	statuces[states] = '\0';
	temp = dfaBuild(statuces);
	temp->ns -= states - count;
	inequality = dfaMinimize(temp);
	return inequality;
}

/*THE END OF ARITHMATIC AUTOMATA CONSTRUCTION************************************************************************/

/**************************************************************************************
 *  END of Constantino's Code
 ***************************************************************************************/

