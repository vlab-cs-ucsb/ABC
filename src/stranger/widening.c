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
 * Authors: Constantinos Bartzis
 */

#include "stranger.h"


/*****************************************************************************

 Constantino's code


 *********************************************************************************/

int xx1, xx2;

int *corresP; //used by dfaEquivalence

// A DFA that accepts everything except for the null (empty) string
DFA *dfaNotNullString() {

	dfaSetup(2, 0, NULL);

	dfaAllocExceptions(0);
	dfaStoreState(1);
	dfaAllocExceptions(0);
	dfaStoreState(1);

	return dfaBuild("-+");
}

// A DFA that accepts only the null (empty) string
DFA *dfaOnlyNullString() {

	dfaSetup(2, 0, NULL);

	dfaAllocExceptions(0);
	dfaStoreState(1);
	dfaAllocExceptions(0);
	dfaStoreState(1);

	return dfaBuild("+-");
}

//recursively checks if state sa of a is equivalent to state sb of b
int checK(DFA *a, DFA *b, bdd_ptr sa, bdd_ptr sb) {
	int leafa, leafb, nexta, nextb;
	bdd_manager *abddm, *bbddm;
	unsigned indexa, indexb;

	abddm = a->bddm;
	bbddm = b->bddm;

	leafa = bdd_is_leaf(abddm, sa);
	leafb = bdd_is_leaf(bbddm, sb);

	if (leafa && leafb) { //both are leaf BDD nodes poining to next state
		nexta = bdd_leaf_value(abddm, sa);
		nextb = bdd_leaf_value(bbddm, sb);
		if (corresP[nexta] == -1) {
			if (a->f[nexta] != b->f[nextb])
				return 0;
			corresP[nexta] = nextb;
			if (!checK(a, b, a->q[nexta], b->q[nextb]))
				return 0;
		} else
			return corresP[nexta] == nextb;
	} else if (leafa || leafb) { //one is a leaf but the other is not
		return 0;
	} else { //both are internal BDD nodes
		LOAD_index(&abddm->node_table[sa], indexa);
		LOAD_index(&bbddm->node_table[sb], indexb);
		if (indexa != indexb)
			return 0;
		return checK(a, b, bdd_then(abddm, sa), bdd_then(bbddm, sb)) && checK(
				a, b, bdd_else(abddm, sa), bdd_else(bbddm, sb));
	}
	return 1;
}

//checks if L(A)=L(B)
int dfaEquivalence(DFA *A, DFA *B) {
	int i, nsa, nsb;
	DFA *a, *b, *temp, *t;

	if ((A->f[A->s] == 1) && (B->f[B->s] == -1)) {
		t = dfaNotNullString();
		temp = dfaProduct(A, t, dfaAND);
		a = dfaMinimize(temp);
		dfaFree(temp);
		dfaFree(t);
		b = dfaMinimize(B);
	} else if ((A->f[A->s] == -1) && (B->f[B->s] == 1)) {
		t = dfaNotNullString();
		temp = dfaProduct(B, t, dfaAND);
		b = dfaMinimize(temp);
		dfaFree(temp);
		dfaFree(t);
		a = dfaMinimize(A);
	} else {
		a = dfaMinimize(A);
		b = dfaMinimize(B);
	}

	nsa = a->ns;
	nsb = b->ns;
	if (nsa != nsb)
		return 0;
	corresP = (int *) malloc(nsa * sizeof(int));
	for (i = 0; i < nsa; i++)
		corresP[i] = -1;
	corresP[a->s] = b->s;
	i = checK(a, b, a->q[a->s], b->q[b->s]);
	free(corresP);
	dfaFree(a);
	dfaFree(b);
	return i;
}

//#define maxl 1000
int maxl;
int *corresPc, *corresPcc, *corresPPc;
int **corresPl, **corresPll, **corresPPl;
int SINKa, SINKb;
int added;
int hi;
char **done;

void check22(DFA *a, bdd_ptr sa, bdd_ptr sb) {
	int leafa, leafb, nexta, nextb, i;
	bdd_manager *abddm;
	unsigned indexa, indexb;

	abddm = a->bddm;

	leafa = bdd_is_leaf(abddm, sa);
	leafb = bdd_is_leaf(abddm, sb);

	if (leafa && leafb) { //both are leaf BDD nodes poining to next state
		nexta = bdd_leaf_value(abddm, sa);
		nextb = bdd_leaf_value(abddm, sb);
		if ((nexta == SINKb) || (nextb == SINKb))
			return;
		for (i = 0; (i < corresPcc[nexta]) && (corresPll[i][nexta] != nextb); i++)
			;
		if (i >= maxl) {
			printf("Limit exeeded. Increase maxl.\n");
			exit(0);
		} else if (i == corresPcc[nexta]) {
			//    if(nexta>=hi)
			added = 1;
			corresPll[corresPcc[nexta]++][nexta] = nextb;
			if (!done[nexta][nextb] && !done[nextb][nexta]) {
				done[nexta][nextb] = 1;
				check22(a, a->q[nexta], a->q[nextb]);
			}
		}
		return;
	} else if (leafa) {
		check22(a, sa, bdd_then(abddm, sb));
		check22(a, sa, bdd_else(abddm, sb));
		return;
	} else if (leafb) {
		check22(a, bdd_then(abddm, sa), sb);
		check22(a, bdd_else(abddm, sa), sb);
		return;
	} else { //both are internal BDD nodes
		LOAD_index(&abddm->node_table[sa], indexa);
		LOAD_index(&abddm->node_table[sb], indexb);
		if (indexa == indexb) {
			check22(a, bdd_then(abddm, sa), bdd_then(abddm, sb));
			check22(a, bdd_else(abddm, sa), bdd_else(abddm, sb));
			return;
		} else if (indexa < indexb) {
			check22(a, bdd_then(abddm, sa), sb);
			check22(a, bdd_else(abddm, sa), sb);
			return;
		} else {
			check22(a, sa, bdd_then(abddm, sb));
			check22(a, sa, bdd_else(abddm, sb));
			return;
		}
	}
	return;
}
// this is a flag for the type of widening we should run
// 1 means the coarse widening which guarantees termination
int _COARSEWIDEN = 0;

void setCoarseWiden(){
	_COARSEWIDEN = 1;
}

void setPreciseWiden(){
	_COARSEWIDEN = 0;
}

//used by dfaClasses
void check2(DFA *a, DFA *b, bdd_ptr sa, bdd_ptr sb) {
	int leafa, leafb, nexta, nextb, i;
	bdd_manager *abddm, *bbddm;
	unsigned indexa, indexb;

	abddm = a->bddm;
	bbddm = b->bddm;

	leafa = bdd_is_leaf(abddm, sa);
	leafb = bdd_is_leaf(bbddm, sb);

	if (leafa && leafb) { //both are leaf BDD nodes poining to next state
		nexta = bdd_leaf_value(abddm, sa);
		nextb = bdd_leaf_value(bbddm, sb);
		if (((nexta == SINKa) || (nextb == SINKb)) && (!_COARSEWIDEN))
			return;
		for (i = 0; (i < corresPc[nexta]) && (corresPl[i][nexta] != nextb); i++)
			;
		if (i >= maxl) {
			printf("Limit exeeded. Increase maxl.\n");
			exit(0);
		} else if (i == corresPc[nexta]) {
			corresPl[corresPc[nexta]++][nexta] = nextb;
			check2(a, b, a->q[nexta], b->q[nextb]);
			//    for(i-=1;i>=0;i--)
			//      check22(b,b->q[corresPl[i][nexta]],b->q[nextb]);
		}
		return;
	} else if (leafa) {
		check2(a, b, sa, bdd_then(bbddm, sb));
		check2(a, b, sa, bdd_else(bbddm, sb));
		return;
	} else if (leafb) {
		check2(a, b, bdd_then(abddm, sa), sb);
		check2(a, b, bdd_else(abddm, sa), sb);
		return;
	} else { //both are internal BDD nodes
		LOAD_index(&abddm->node_table[sa], indexa);
		LOAD_index(&bbddm->node_table[sb], indexb);
		if (indexa == indexb) {
			check2(a, b, bdd_then(abddm, sa), bdd_then(bbddm, sb));
			check2(a, b, bdd_else(abddm, sa), bdd_else(bbddm, sb));
			return;
		} else if (indexa < indexb) {
			check2(a, b, bdd_then(abddm, sa), sb);
			check2(a, b, bdd_else(abddm, sa), sb);
			return;
		} else {
			check2(a, b, sa, bdd_then(bbddm, sb));
			check2(a, b, sa, bdd_else(bbddm, sb));
			return;
		}
	}
	return;
}

int *classRepA, *classRepB, *classRepC;
int find_sink(DFA *a);
int numClasses;

int detail(DFA *a, DFA *b, bdd_ptr sa, bdd_ptr sb) {
	int leafa, leafb;
	bdd_manager *abddm, *bbddm;
	unsigned indexa, indexb;
	int A, B;

	abddm = a->bddm;
	bbddm = b->bddm;

	leafa = bdd_is_leaf(abddm, sa);
	leafb = bdd_is_leaf(bbddm, sb);

	if (leafa && leafb) { //both are leaf BDD nodes poining to next state
		return 0;
	} else if (leafa) {
		return 2;
	} else if (leafb) {
		return 1;
	} else { //both are internal BDD nodes
		LOAD_index(&abddm->node_table[sa], indexa);
		LOAD_index(&bbddm->node_table[sb], indexb);
		if (indexa < indexb)
			return 1;
		else if (indexb < indexa)
			return 2;
		A = detail(a, b, bdd_then(abddm, sa), bdd_then(bbddm, sb));
		B = detail(a, b, bdd_else(abddm, sa), bdd_else(bbddm, sb));
		if (A == B)
			return A;
		else if (A == 0)
			return B;
		else if (B == 0)
			return A;
		else
			return 3;
	}
}

void dfaClasses(DFA *A, DFA *B) {
	int i, j, k, l, nsa, nsb;
	DFA *a, *b, *temp, *t;
	int *visiteda, *visitedb;

	if ((A->f[A->s] == 1) && (B->f[B->s] == -1)) {
		t = dfaNotNullString();
		temp = dfaProduct(A, t, dfaAND);
		a = dfaMinimize(temp);
		dfaFree(temp);
		dfaFree(t);
		b = dfaMinimize(B);
	} else if ((A->f[A->s] == -1) && (B->f[B->s] == 1)) {
		t = dfaOnlyNullString();
		temp = dfaProduct(A, t, dfaOR);
		a = dfaMinimize(temp);
		dfaFree(temp);
		dfaFree(t);
		b = dfaMinimize(B);
	} else {
		a = dfaMinimize(A);
		b = dfaMinimize(B);
	}

	nsa = a->ns;
	nsb = b->ns;

	maxl = b->ns;

	//find "forward corresponding" states
	corresPc = (int *) malloc((nsa + nsb) * sizeof(int));
	corresPl = (int **) malloc(maxl * sizeof(int *));
	done = (char **) malloc(maxl * sizeof(char *));
	corresPcc = corresPc + nsa;
	corresPll = (int **) malloc(maxl * sizeof(int *));
	for (i = 0; i < maxl; i++)
		corresPl[i] = (int *) malloc((nsa + nsb) * sizeof(int));
	for (i = 0; i < maxl; i++)
		done[i] = (char *) malloc(nsb * sizeof(char));
	for (i = 0; i < maxl; i++)
		for (j = 0; j < maxl; j++)
			done[i][j] = 0;
	for (i = 0; i < maxl; i++)
		corresPll[i] = corresPl[i] + nsa;
	for (i = 0; i < nsa; i++)
		corresPc[i] = 0;
	for (i = 0; i < nsb; i++)
		corresPcc[i] = 1;
	for (i = 0; i < nsb; i++)
		corresPll[0][i] = i;
	corresPc[a->s] = 1;
	corresPl[0][a->s] = b->s;
	SINKa = find_sink(a);
	SINKb = find_sink(b);
	check2(a, b, a->q[a->s], b->q[b->s]);

	//find equivalent states
	corresP = (int *) malloc(nsa * sizeof(int));
	visiteda = (int *) malloc(nsa * sizeof(int));
	visitedb = (int *) malloc(nsb * sizeof(int));

	for (i = 0; i < nsa; i++)
		visiteda[i] = 0;
	for (i = 0; i < nsb; i++)
		visitedb[i] = 0;
	i = 0;
	while (i < nsa) {
		while ((visiteda[i] != 0) && (i < nsa))
			i++;
		if (i == nsa)
			break;
		j = 0;
		while (j < nsb) {
			while ((visitedb[j] != 0) && (j < nsb))
				j++;
			if (j == nsb)
				break;
			if (a->f[i] == b->f[j]) {
				for (k = 0; k < nsa; k++)
					corresP[k] = -1;
				corresP[i] = j;
				if (checK(a, b, a->q[i], b->q[j])) {
					for (k = 0; k < nsa; k++)
						if (corresP[k] != -1) {
							visiteda[k] = 1;
							visitedb[corresP[k]] = 1;
							//printf("%d<=>%d\n",k,corresP[k]);
							//also modify corresPc and corresPl
							for (l = 0; (l < corresPc[k]) && (corresPl[l][k]
									!= corresP[k]); l++)
								;
							if (l >= maxl) {
								printf("Limit exeeded. Increase maxl.\n");
								exit(0);
							} else if (l == corresPc[k]) {
								corresPl[corresPc[k]++][k] = corresP[k];
								//               for(l-=1;l>=0;l--)
								//                 check22(b,b->q[corresPl[l][k]],b->q[corresP[k]]);
							}
						}
					j = nsb;
				} else
					j++;
			} else
				j++;
		}
		i++;
	}

	do {

		//merge classes
		added = 0;

		for (i = nsa + nsb - 1; i > 0; i--) {
			for (j = i - 1; j >= 0; j--) {
				l = 0;
				for (k = 0; k < corresPc[i]; k++) {
					for (l = 0; (l < corresPc[j]) && (corresPl[k][i]
							!= corresPl[l][j]); l++)
						;
					if (l < corresPc[j])
						break;
				}
				if (k < corresPc[i]) {
					for (k = 0; k < corresPc[i]; k++) {
						for (l = 0; (l < corresPc[j]) && (corresPl[k][i]
								!= corresPl[l][j]); l++)
							;
						if (l == corresPc[j]) {
							if (l >= maxl) {
								printf("Limit exeeded. Increase maxl.\n");
								exit(0);
							}
							corresPl[l][j] = corresPl[k][i];
							corresPc[j]++;

							/*
							 //Here begins the mess
							 for(l-=1;l>=0;l--)
							 if(!done[corresPl[l][j]][corresPl[k][i]]&&!done[corresPl[k][i]][corresPl[l][j]]){
							 done[corresPl[l][j]][corresPl[k][i]]=1;
							 hi=i-nsa;
							 check22(b,b->q[corresPl[l][j]],b->q[corresPl[k][i]]);
							 }
							 */

						}
					}
					if (i < nsa)
						corresPc[i] = 0;
					j = -1;
				}
			}
		}

		added = 0;
		for (k = 0; k < nsa + nsb; k++)
			for (i = 0; (i < corresPc[k] - 1); i++)
				for (j = i + 1; j < corresPc[k]; j++)
					if (!done[corresPl[i][k]][corresPl[j][k]]
							&& !done[corresPl[j][k]][corresPl[i][k]]) {
						done[corresPl[i][k]][corresPl[j][k]] = 1;
						check22(b, b->q[corresPl[i][k]], b->q[corresPl[j][k]]);
					}

	} while (added == 1);

	/*
	 //make accepting classes, accepting
	 for(i=0;i<nsa;i++){
	 if((corresPc[i]>0)&&(b->f[corresPl[0][i]]!=1)){
	 for(j=1;j<corresPc[i];j++){
	 if(b->f[corresPl[j][i]]==1){
	 b->f[corresPl[0][i]]=1;
	 break;
	 }
	 }
	 }
	 }
	 */

	corresPPc = (int *) malloc(maxl * sizeof(int));
	corresPPl = (int **) malloc(maxl * sizeof(int *));
	for (i = 0; i < maxl; i++)
		corresPPl[i] = (int *) malloc(maxl * sizeof(int));
	classRepC = (int *) malloc(nsb * sizeof(int));
	for (i = 0; i < nsb; i++)
		classRepC[i] = -1;
	j = 0;
	for (i = 0; i < nsa; i++)
		if (corresPc[i] > 0) {
			for (k = 0; k < corresPc[i]; k++) {
				corresPPl[k][j] = corresPl[k][i];
				classRepC[corresPPl[k][j]] = j;
			}
			corresPPc[j] = corresPc[i];
			j++;
		}

	for (i = 0; i < nsb; i++)
		if (classRepC[i] == -1) {
			if (corresPcc[i] > 1) {
				for (k = 0; k < corresPcc[i]; k++) {
					corresPPl[k][j] = corresPll[k][i];
					classRepC[corresPPl[k][j]] = j;
				}
				corresPPc[j] = corresPcc[i];
				j++;
			}
		}

	for (i = 0; i < nsb; i++)
		if (classRepC[i] == -1) {
			corresPPc[j] = 1;
			corresPPl[0][j] = i;
			classRepC[i] = j;
			j++;
		}
	numClasses = j;

	/*
	 //define class representatives
	 classRepA=(int *)malloc(nsb*sizeof(int));
	 classRepB=(int *)malloc(nsb*sizeof(int));

	 for(i=0;i<nsb;i++){
	 classRepB[i]=i;
	 classRepA[i]=-1;
	 }
	 for(i=0;i<nsa;i++)
	 for(j=0;j<corresPc[i];j++){
	 classRepB[corresPl[j][i]]=corresPl[0][i];
	 classRepA[corresPl[j][i]]=i;
	 }
	 for(i=0;i<nsb;i++){
	 if(b->f[classRepB[i]]==1)
	 b->f[i]=1;
	 }
	 */

	//clear the mess
	free(corresP);
	free(visiteda);
	free(visitedb);
	for (i = 0; i < maxl; i++)
		free(done[i]);
	free(done);
	dfaFree(a);
	dfaFree(b);
	return;
}

int fromS;
int fromPath[50];
int fromIndy[50];
int *fromIndex;
int fromCount;
int at;

int nonsink(bdd_manager *abddm, bdd_ptr sa) {
	unsigned l, r, index;

	LOAD_lri(&abddm->node_table[sa], l, r, index);
	if (index == BDD_LEAF_INDEX) {
		if (l == SINKb)
			return -1;
		else
			return classRepB[l];
	}

	else {

		while ((fromIndex[at] < index) && (at <= fromCount))
			at++;

		if (at <= fromCount) {
			if (fromPath[at++] == 0)
				return nonsink(abddm, l);
			else
				return nonsink(abddm, r);
		}

		else {
			if ((nonsink(abddm, l) == -1) && (nonsink(abddm, r) == -1))
				return -1;
			else
				return -2;
		}
	}
}

int torepcaller;
bdd_manager *cbddm;

bdd_ptr torep(DFA *a, bdd_ptr sa) {
	unsigned l, r, index;
	int dest, i, tempdest;

	bdd_manager *abddm;
	bdd_ptr L, R;
	int split;

	abddm = a->bddm;

	LOAD_lri(&abddm->node_table[sa], l, r, index);
	if (index == BDD_LEAF_INDEX) {
		dest = classRepB[l];
		if (dest == SINKb) {
			if (classRepA[fromS] != -1) {
				split = 0;
				for (i = 1; i < corresPc[classRepA[fromS]]; i++) {
					at = 0;
					tempdest = nonsink(abddm,
							a->q[corresPl[i][classRepA[fromS]]]);
					if (tempdest >= 0) {
						return bdd_find_leaf_hashed_add_root(cbddm, tempdest);
					} else if (tempdest == -2)
						split = 1;
				}
				if (split) {
					fromCount++;
					fromIndex[fromCount] = fromIndex[fromCount - 1] + 2;
					fromPath[fromCount] = 0;
					L = torep(a, sa);
					torepcaller = sa;
					fromPath[fromCount] = 1;
					R = torep(a, sa);
					fromCount--;
					return bdd_find_node_hashed_add_root(cbddm, L, R,
							fromIndex[fromCount + 1]);
				}
			}
		}
		return bdd_find_leaf_hashed_add_root(cbddm, dest);
	} else if (index == fromIndex[fromCount] + 2) {
		torepcaller = sa;
		fromCount++;
		fromIndex[fromCount] = index;
		fromPath[fromCount] = 0;
		L = torep(a, l);
		torepcaller = sa;
		fromPath[fromCount] = 1;
		R = torep(a, r);
		fromCount--;
		return bdd_find_node_hashed_add_root(cbddm, L, R, index);
	} else {
		fromCount++;
		fromIndex[fromCount] = fromIndex[fromCount - 1] + 2;
		fromPath[fromCount] = 0;
		L = torep(a, sa);
		torepcaller = sa;
		fromPath[fromCount] = 1;
		R = torep(a, sa);
		fromCount--;
		return bdd_find_node_hashed_add_root(cbddm, L, R, fromIndex[fromCount
				+ 1]);

	}
}

int *reachable;
int reachc;

void reach(DFA *a, bdd_ptr sa) {
	unsigned l, r, index;

	LOAD_lri(&(a->bddm)->node_table[sa], l, r, index);

	if (index == BDD_LEAF_INDEX) {
		if (reachable[l] == 0) {
			reachable[l] = 1;
			reachc++;
			reach(a, a->q[l]);
		}
	} else {
		reach(a, r);
		reach(a, l);
	}
}

int *ren;

void reName(bdd_manager *abddm, bdd_ptr sa) {
	unsigned l, r, index;

	if ((&abddm->node_table[sa])->mark)
		return;
	(&abddm->node_table[sa])->mark++;
	LOAD_lri(&abddm->node_table[sa], l, r, index);
	if (index == BDD_LEAF_INDEX) {
		{
			STR_lri(&abddm->node_table[sa], ren[l], r, index);
		}
		return;
	} else {
		reName(abddm, r);
		reName(abddm, l);
		return;
	}
}

DFA *dfaClean(DFA *a) {
	DFA *c;
	int i, j;



	//dfaPrint(a,1,names,ind);
	reachable = (int *) malloc(a->ns * sizeof(int));
	for (i = 0; i < a->ns; i++)
		reachable[i] = 0;
	reachable[a->s] = 1;
	reachc = 1;
	reach(a, a->q[a->s]);

	c = dfaMake(reachc);
	c->ns = reachc;
	c->s = a->s;

	bdd_prepare_apply1(a->bddm);

	j = 0;
	for (i = 0; i < a->ns; i++)
		if (reachable[i]) {
			(void) bdd_apply1(a->bddm, a->q[i], c->bddm, &fn_identity);
			c->f[j++] = a->f[i];
		}

	mem_copy(c->q, bdd_roots(c->bddm), sizeof(bdd_ptr) * reachc);

	ren = (int *) malloc(a->ns * sizeof(int));
	j = 0;
	for (i = 0; i < a->ns; i++)
		if (reachable[i])
			ren[i] = i - j;
		else
			j++;
	bdd_prepare_apply1(c->bddm);
	for (i = 0; i < c->ns; i++)
		reName(c->bddm, c->q[i]);

	free(ren);
	free(reachable);
	return c;
}

int SINK5;
int num5;
int *indices5;

bdd_ptr visit5(DFA *a, bdd_ptr sa, bdd_ptr sb) {
	bdd_ptr la, ra, indexa, lb, rb, indexb, L, R;
	int i;

	LOAD_lri(&a->bddm->node_table[sa], la, ra, indexa);
	LOAD_lri(&a->bddm->node_table[sb], lb, rb, indexb);

	if (indexa == BDD_LEAF_INDEX && indexb == BDD_LEAF_INDEX) {
		if (la != SINK5)
			return bdd_find_leaf_hashed_add_root(a->bddm, la);
		else
			return bdd_find_leaf_hashed_add_root(a->bddm, lb);
	}

	else if (indexa == BDD_LEAF_INDEX) {
		L = visit5(a, sa, lb);
		R = visit5(a, sa, rb);
		for (i = 0; (i < num5) && (indices5[i] != indexb); i++)
			;
		if (i == num5)
			return bdd_find_node_hashed_add_root(a->bddm, L, R, indexb);
		else
			return visit5(a, L, R);
	}

	else if (indexb == BDD_LEAF_INDEX) {
		L = visit5(a, la, sb);
		R = visit5(a, ra, sb);
		for (i = 0; (i < num5) && (indices5[i] != indexa); i++)
			;
		if (i == num5)
			return bdd_find_node_hashed_add_root(a->bddm, L, R, indexa);
		else
			return visit5(a, L, R);
	}

	else {
		if (indexa < indexb) {
			L = visit5(a, la, sb);
			R = visit5(a, ra, sb);
			for (i = 0; (i < num5) && (indices5[i] != indexa); i++)
				;
			if (i == num5)
				return bdd_find_node_hashed_add_root(a->bddm, L, R, indexa);
			else
				return visit5(a, L, R);
		} else if (indexb < indexa) {
			L = visit5(a, sa, lb);
			R = visit5(a, sa, rb);
			for (i = 0; (i < num5) && (indices5[i] != indexb); i++)
				;
			if (i == num5)
				return bdd_find_node_hashed_add_root(a->bddm, L, R, indexb);
			else
				return visit5(a, L, R);
		} else {
			L = visit5(a, la, lb);
			R = visit5(a, ra, rb);
			for (i = 0; (i < num5) && (indices5[i] != indexb); i++)
				;
			if (i == num5)
				return bdd_find_node_hashed_add_root(a->bddm, L, R, indexb);
			else
				return visit5(a, L, R);
		}
	}
}

void project5(DFA *a, int num, int *indices) {
	//DFA *d;
	int i;

	num5 = num;
	indices5 = indices;
	SINK5 = find_sink(a);

	//d=dfaMake(a->ns);
	//d->ns=a->ns;
	//d->s=a->s;
	for (i = 0; i < a->ns; i++) {
		a->q[i] = visit5(a, a->q[i], a->q[i]);
	}
}

bdd_ptr merge1(DFA *a, DFA *d, bdd_ptr sa, bdd_ptr sb) {
	bdd_ptr la, lb, ra, rb, indexa, indexb;
	bdd_ptr L, R;

	LOAD_lri(&a->bddm->node_table[sa], la, ra, indexa);
	LOAD_lri(&a->bddm->node_table[sb], lb, rb, indexb);

	if (indexa == BDD_LEAF_INDEX && indexb == BDD_LEAF_INDEX) {
		if (la != SINKa) {
			return bdd_find_leaf_hashed_add_root(d->bddm, la);
		} else {
			return bdd_find_leaf_hashed_add_root(d->bddm, lb);
		}
	}

	else if (indexa == BDD_LEAF_INDEX) {
		L = merge1(a, d, sa, lb);
		R = merge1(a, d, sa, rb);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexb);
	}

	else if (indexb == BDD_LEAF_INDEX) {
		L = merge1(a, d, la, sb);
		R = merge1(a, d, ra, sb);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
	}

	else {
		if (indexa < indexb) {
			L = merge1(a, d, la, sb);
			R = merge1(a, d, ra, sb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
		} else if (indexb < indexa) {
			L = merge1(a, d, sa, lb);
			R = merge1(a, d, sa, rb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexb);
		} else {
			L = merge1(a, d, la, lb);
			R = merge1(a, d, ra, rb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
		}
	}
}

bdd_ptr visit6(DFA *a, DFA *d, bdd_ptr sa, unsigned index) {
	bdd_ptr la, ra, indexa;
	bdd_ptr L, R;

	LOAD_lri(&a->bddm->node_table[sa], la, ra, indexa);

	if (indexa == BDD_LEAF_INDEX) {
		return bdd_find_leaf_hashed_add_root(d->bddm, la);
	}

	else if (indexa == index) {
		L = merge1(a, d, la, ra);
		return L;
	}

	else {
		L = visit6(a, d, la, index);
		R = visit6(a, d, ra, index);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
	}
}

DFA *project6(DFA *a, unsigned index) {
	DFA *d;
	int i;

	SINKa = find_sink(a);
	d = dfaMake(a->ns);
	d->ns = a->ns;
	d->s = a->s;
	for (i = 0; i < a->ns; i++) {
		d->q[i] = visit6(a, d, a->q[i], index);
		d->f[i] = a->f[i];
	}
	return d;
}

//merge nodes sa and sb of DFA a in a "new" node in DFA d
bdd_ptr merge(DFA *a, DFA *d, bdd_ptr sa, bdd_ptr sb) {
	bdd_ptr la, lb, ra, rb, indexa, indexb;
	bdd_ptr L, R;

	LOAD_lri(&a->bddm->node_table[sa], la, ra, indexa);
	LOAD_lri(&a->bddm->node_table[sb], lb, rb, indexb);

	if (indexa == BDD_LEAF_INDEX && indexb == BDD_LEAF_INDEX) {
		if (la != SINKb) {
			if (a == d)
				L = la;
			else {
				L = classRepC[la];
				if ((lb != SINKb) && (classRepC[la] != classRepC[lb])) {
					printf("Classes inconsistent\n");
					//          printf("We got a problem here. %d goes to %d, but %d goes to %d\n",xx1,la,xx2,lb);
					// char *names[10]={"x","x","x","x","x","x","x","x","x","x"};
					// int ind[10]={0,2,4,6,8,10,12,14,16,18};
					//          dfaPrint(a,10,names,ind);
					exit(0);
				}
			}
			return bdd_find_leaf_hashed_add_root(d->bddm, L);
		} else {
			if (a == d)
				L = lb;
			else
				L = classRepC[lb];
			return bdd_find_leaf_hashed_add_root(d->bddm, L);
		}
	}

	else if (indexa == BDD_LEAF_INDEX) {
		L = merge(a, d, sa, lb);
		R = merge(a, d, sa, rb);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexb);
	}

	else if (indexb == BDD_LEAF_INDEX) {
		L = merge(a, d, la, sb);
		R = merge(a, d, ra, sb);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
	}

	else {
		if (indexa < indexb) {
			L = merge(a, d, la, sb);
			R = merge(a, d, ra, sb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
		} else if (indexb < indexa) {
			L = merge(a, d, sa, lb);
			R = merge(a, d, sa, rb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexb);
		} else {
			L = merge(a, d, la, lb);
			R = merge(a, d, ra, rb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
		}
	}
}

bdd_ptr merge_single(DFA *a, DFA *d, bdd_ptr sa) {
	bdd_ptr la, ra, indexa;

	LOAD_lri(&a->bddm->node_table[sa], la, ra, indexa);

	if (indexa == BDD_LEAF_INDEX) {
		return bdd_find_leaf_hashed_add_root(d->bddm, classRepC[la]);
	}

	else {
		return bdd_find_node_hashed_add_root(d->bddm, merge_single(a, d, la),
				merge_single(a, d, ra), indexa);
	}
}

//d is larger
DFA *dfaWiden(DFA *a, DFA *d) {
	DFA *c, *b;
	int i, j;

	b = dfaCopy(d);
	dfaClasses(a, b);
	c = dfaMake(numClasses);
	cbddm = c->bddm;
	c->ns = numClasses;
	c->s = classRepC[b->s];

	//printf("# of b nodes before merge: %d\n",bdd_size(b->bddm));
	//printf("# of c nodes before merge: %d\n",bdd_size(c->bddm));
	//printf("MONA memory:%d\n",mem_allocated());

	for (i = 0; i < numClasses; i++) {
		if (corresPPc[i] == 1)
			c->q[i] = merge_single(b, c, b->q[corresPPl[0][i]]);
		else {
			c->q[i] = b->q[corresPPl[0][i]];
			for (j = 1; j < corresPPc[i] - 1; j++) {
				xx1 = i;
				xx2 = corresPPl[j][i];
				c->q[i] = merge(b, b, c->q[i], b->q[corresPPl[j][i]]);
			}
			xx1 = i;
			xx2 = corresPPl[j][i];
			c->q[i] = merge(b, c, c->q[i], b->q[corresPPl[j][i]]);
		}
	}

	//printf("# of b nodes after merge: %d\n",bdd_size(b->bddm));
	//printf("# of c nodes after merge: %d\n",bdd_size(c->bddm));
//	printf("MONA memory:%d\n",mem_allocated());

	for (i = 0; i < numClasses; i++) {
		c->f[i] = -1;
		for (j = 0; j < corresPPc[i]; j++)
			if (b->f[corresPPl[j][i]] == 1) {
				c->f[i] = 1;
				break;
			}
	}

	free(classRepC);
	free(corresPPc);
	for (i = 0; i < maxl; i++)
		free(corresPPl[i]);

	//free(classRepA);
	//free(classRepB);
	free(corresPc);
	for (i = 0; i < maxl; i++)
		free(corresPl[i]);
	dfaFree(b);
	b = dfaClean(c);
	dfaFree(c);
	return b;
}

static int **preds; /* preds[i] is the set of predecessors of i */
static int *predalloc, *predused; /* allocated/used size of preds[i] */

static int current_state;

void successors0(bdd_manager *bddm, bdd_ptr p) {
	if (bdd_is_leaf(bddm, p)) {
		int i;
		int s = bdd_leaf_value(bddm, p); /* current_state is a predecessor of s */

		for (i = 0; i < predused[s]; i++)
			/* already there? */
			if (preds[s][i] == current_state)
				return;

		if (predalloc[s] == predused[s]) { /* need to reallocate? */
			predalloc[s] = predalloc[s] * 2 + 8;
			preds[s] = (int *) mem_resize(preds[s], sizeof(int) * predalloc[s]);
		}

		preds[s][predused[s]++] = current_state;
	} else {
		successors0(bddm, bdd_else(bddm, p));
	}

}

void dfaPrefixClose0(DFA *a) {
	unsigned i;
	int *queue = (int *) mem_alloc(sizeof(int) * a->ns);
	int queueused = 0, next = 0;

	predalloc = (int *) mem_alloc(sizeof(int) * a->ns);
	predused = (int *) mem_alloc(sizeof(int) * a->ns);
	preds = (int **) mem_alloc(sizeof(int *) * a->ns);
	for (i = 0; i < a->ns; i++) {
		predalloc[i] = predused[i] = 0;
		preds[i] = 0;
	}

	/* find predecessor sets and initialize queue with final states */
	for (i = 0; i < a->ns; i++) {
		current_state = i;
		successors0(a->bddm, a->q[i]);
		if (a->f[i] == 1)
			queue[queueused++] = i;
	}

	/* color */
	while (next < queueused) {
		for (i = 0; i < predused[queue[next]]; i++)
			if (a->f[preds[queue[next]][i]] != 1) {
				a->f[preds[queue[next]][i]] = 1;
				queue[queueused++] = preds[queue[next]][i];
			}
		next++;
	}

	for (i = 0; i < a->ns; i++)
		mem_free(preds[i]);
	mem_free(preds);
	mem_free(predused);
	mem_free(predalloc);
	mem_free(queue);
}

#define MAXV 50
int label[MAXV];//this array hold a path from the root to a leaf
//0 is low, 1 is high, 2 is don't care
//MAXV is the maximum number of variables, can be set accordingly
int numnexts;
int *nexts;
DFA *autom;

void toaccepting(bdd_manager *abddm, bdd_ptr sa) {
	unsigned index;

	if (bdd_is_leaf(abddm, sa)) {
		nexts[numnexts++] = bdd_leaf_value(abddm, sa);
	} else { //not a leaf
		LOAD_index(&abddm->node_table[sa], index);
		if (label[index] == 0)
			toaccepting(abddm, bdd_else(abddm, sa));
		if (label[index] == 1)
			toaccepting(abddm, bdd_then(abddm, sa));
		if (label[index] == 2) {
			toaccepting(abddm, bdd_else(abddm, sa));
			toaccepting(abddm, bdd_then(abddm, sa));
		}
	}
}

//Idea: krata to monopati apo th riza mexri ekei pou eisai twra
//an eisai fyllo s, kame evaluate to monopati sth next state n
//bale to s stous preds tou n
void successors1(bdd_manager *bddm, bdd_ptr p) {
	unsigned ind;
	if (bdd_is_leaf(bddm, p)) {
		int i, j;
		int s = bdd_leaf_value(bddm, p); /* current_state is a predecessor of s*/
		//    printf("%d,",current_state);
		//    for(i=0;i<MAXV;i++)
		//      printf("%d",label[i]);
		//    printf(",%d\n",s);

		numnexts = 0;
		toaccepting(bddm, autom->q[s]);
		for (j = 0; j < numnexts; j++) {
			for (i = 0; i < predused[nexts[j]]; i++)
				/* already there? */
				if (preds[nexts[j]][i] == s)
					break;
			if (i < predused[nexts[j]])
				continue;

			if (predalloc[nexts[j]] == predused[nexts[j]]) { /* need to reallocate? */
				predalloc[nexts[j]] = predalloc[nexts[j]] * 2 + 8;
				preds[nexts[j]] = (int *) mem_resize(preds[nexts[j]],
						sizeof(int) * predalloc[nexts[j]]);
			}
			preds[nexts[j]][predused[nexts[j]]++] = s;
		}
	} else {
		ind = bdd_ifindex(bddm, p);
		label[ind] = 0;
		successors1(bddm, bdd_else(bddm, p));
		label[ind] = 1;
		successors1(bddm, bdd_then(bddm, p));
		label[ind] = 2;
	}

}

void dfaPrefixClose1(DFA *a) {
	unsigned i;
	int *queue = (int *) mem_alloc(sizeof(int) * a->ns);
	int queueused = 0, next = 0;

	for (i = 0; i < MAXV; i++)
		label[i] = 2;
	autom = a;
	nexts = (int *) mem_alloc(sizeof(int) * a->ns);
	predalloc = (int *) mem_alloc(sizeof(int) * a->ns);
	predused = (int *) mem_alloc(sizeof(int) * a->ns);
	preds = (int **) mem_alloc(sizeof(int *) * a->ns);
	for (i = 0; i < a->ns; i++) {
		predalloc[i] = predused[i] = 0;
		preds[i] = 0;
	}

	/* find predecessor sets and initialize queue with final states */
	for (i = 0; i < a->ns; i++) {
		current_state = i;
		successors1(a->bddm, a->q[i]);
		if (a->f[i] == 1)
			queue[queueused++] = i;
	}

	/* color */
	while (next < queueused) {
		for (i = 0; i < predused[queue[next]]; i++)
			if (a->f[preds[queue[next]][i]] != 1) {
				a->f[preds[queue[next]][i]] = 1;
				queue[queueused++] = preds[queue[next]][i];
			}
		next++;
	}

	for (i = 0; i < a->ns; i++)
		mem_free(preds[i]);
	mem_free(nexts);
	mem_free(preds);
	mem_free(predused);
	mem_free(predalloc);
	mem_free(queue);
}

DFA *dfatrue() {
	dfaSetup(1, 0, NULL);

	dfaAllocExceptions(0);
	dfaStoreState(0);

	return dfaBuild("+");
}

DFA *dfafalse() {
	dfaSetup(1, 0, NULL);

	/* boolvar */
	dfaAllocExceptions(0);
	dfaStoreState(0);

	return dfaBuild("-");
}

DFA *dfaBoolVar(int b) {
	int var_index[1];
	var_index[0] = b;

	dfaSetup(3, 1, var_index);

	/* boolvar */
	dfaAllocExceptions(1);
	dfaStoreException(2, "0");
	dfaStoreState(1);

	/* state 1 */
	dfaAllocExceptions(0);
	dfaStoreState(1);

	/* state 2 */
	dfaAllocExceptions(0);
	dfaStoreState(2);

	return dfaBuild("-+-");
}

bdd_ptr target;
int *clone;

bdd_ptr merge2(DFA *a, DFA *d, bdd_ptr sa, bdd_ptr sb) {
	bdd_ptr la, lb, ra, rb, indexa, indexb, to;
	bdd_ptr L, R;

	LOAD_lri(&a->bddm->node_table[sa], la, ra, indexa);
	LOAD_lri(&a->bddm->node_table[sb], lb, rb, indexb);

	if (indexa == BDD_LEAF_INDEX && indexb == BDD_LEAF_INDEX) {
		if (a->f[lb] == 1 && la == target) {
			if (a->q[lb] == a->q[la])
				to = lb;
			else
				to = clone[la];
			return bdd_find_leaf_hashed_add_root(d->bddm, to);
		} else {
			return bdd_find_leaf_hashed_add_root(d->bddm, la);
		}
	}

	else if (indexa == BDD_LEAF_INDEX) {
		L = merge2(a, d, sa, lb);
		R = merge2(a, d, sa, rb);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexb);
	}

	else if (indexb == BDD_LEAF_INDEX) {
		L = merge2(a, d, la, sb);
		R = merge2(a, d, ra, sb);
		return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
	}

	else {
		if (indexa < indexb) {
			L = merge2(a, d, la, sb);
			R = merge2(a, d, ra, sb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
		} else if (indexb < indexa) {
			L = merge2(a, d, sa, lb);
			R = merge2(a, d, sa, rb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexb);
		} else {
			L = merge2(a, d, la, lb);
			R = merge2(a, d, ra, rb);
			return bdd_find_node_hashed_add_root(d->bddm, L, R, indexa);
		}
	}
}

void successorz(DFA *a, bdd_ptr p) {
	bdd_manager *bddm = a->bddm;
	if (bdd_is_leaf(bddm, p)) {
		int i;
		int s = bdd_leaf_value(bddm, p); /* current_state is a predecessor of s */
		if (a->f[s] != 1 && s != current_state) {
			for (i = 0; i < predused[s]; i++)
				/* already there? */
				if (preds[s][i] == current_state)
					return;

			if (predalloc[s] == predused[s]) { /* need to reallocate? */
				predalloc[s] = predalloc[s] * 2 + 8;
				preds[s] = (int *) mem_resize(preds[s], sizeof(int)
						* predalloc[s]);
			}
			preds[s][predused[s]++] = current_state;
		}
	} else {
		successorz(a, bdd_else(bddm, p));
		successorz(a, bdd_then(bddm, p));
	}

}


DFA * dfaPrefixClose3(DFA *a) {
	int i, j;
	DFA *c;

	predalloc = (int *) mem_alloc(sizeof(int) * a->ns);
	predused = (int *) mem_alloc(sizeof(int) * a->ns);
	preds = (int **) mem_alloc(sizeof(int *) * a->ns);
	for (i = 0; i < a->ns; i++) {
		predalloc[i] = predused[i] = 0;
		preds[i] = 0;
	}

	/* find predecessor sets */
	for (i = 0; i < a->ns; i++)
		if (a->f[i] != 1) {
			current_state = i;
			successorz(a, a->q[i]);
		}

	int cns = a->ns;
	clone = (int *) malloc(cns * sizeof(int));
	for (i = 0; i < a->ns; i++)
		if (a->f[i] != 1)
			cns++;

	c = dfaMake(cns);//was cns
	c->ns = cns;//was cns
	c->s = a->s;
	mem_copy(c->f, a->f, sizeof(*a->f) * a->ns);
	bdd_prepare_apply1(a->bddm);
	for (i = 0; i < a->ns; i++)
		(void) bdd_apply1(a->bddm, a->q[i], c->bddm, &fn_identity);
	mem_copy(c->q, bdd_roots(c->bddm), sizeof(bdd_ptr) * a->ns);
	j = a->ns;
	for (i = 0; i < a->ns; i++)
		if (a->f[i] != 1) {
			c->q[j] = c->q[i];
			c->f[j] = 1;
			clone[i] = j;
			j++;
		}

	for (i = 0; i < a->ns; i++) {
		for (j = 0; j < predused[i]; j++) {
			target = i;
			c->q[preds[i][j]] = merge2(c, c, c->q[preds[i][j]], c->q[i]);
		}
	}

	DFA *d = dfaClean(c);
	dfaFree(c);
	free(clone);
	mem_free(preds);
	mem_free(predused);
	mem_free(predalloc);

	return d;
}

DFA *dfaPrefixClose2(DFA *temp) {
	DFA *a = dfaTrue();
	do {
		dfaFree(a);
		a = temp;
		temp = dfaPrefixClose3(a);
	} while (!dfaEquivalence(temp, a));
	dfaFree(temp);
	return (a);
}

/**************************************************************************************
 *  END of Constantino's Code
 ***************************************************************************************/


