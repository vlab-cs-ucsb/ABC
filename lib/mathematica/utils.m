(* ::Package:: *)


(* Get the transition relation as a list of tuples from a 
Graph object which was created by importing a dot file *)
TransitionRelation[G_] := Module[{edgelabels, tr, el, e},
	edgelabels = Options[G, EdgeLabels][[1]][[2]];
	Map[Map[ToExpression[#] + 1 &, First[#]]  -> 
   InstantiateTransitions[
    ToExpression[
     Transpose[
      Map[StringSplit[#, " "] &, 
       StringSplit[StringReplace[Last[#], "," -> " "], 
        "\n"]]]]] &, edgelabels] 
]

(* Get the transfer-matrix of a transition relation.
T = TransferMatrix[TR] is a matrix such that T[i,j]
is the number of direct transitions between v_i and v_j *)
TransferMatrix[transitionRelation_] := SparseArray[
	Map[Function[tr, {First[First[tr]] ,Last[First[tr]] } -> Length[Last[tr]]], 
	transitionRelation]
]

(* Replace "don't care" transitions with 0 and 1 *)
InstantiateX[list_] := Tuples[ReplaceAll[Map[List, list], {X} -> {0, 1}]]

(* Instantiate each transition in a relation *)
InstantiateTransitions[ts_] := Flatten[Map[InstantiateX, ts], 1]

(* Compute a matrix of generating functions.
For GF = MatrixFenFun[A,k], GF is a matrix with the
same dimensions as A such that GF[i,j] is a function of 
z[k] whose nth series coefficient is equal to (A^n)[i,j].
k is used to assign an index to the variable z*)
MatrixGenFun[A_, boundOrder_] := Module[{n,Id,X},
	n = Dimensions[A][[1]];
	Id = IdentityMatrix[n];
	X = Id - A z[boundOrder];
	Table[(-1)^(i+j) Det[SubMatrix[X,j,i]] / Det[X], {i,n}, {j,n}]
]

(* Get the submatrix of M by deleting row r and column c*)
SubMatrix[M_, r_, c_] := Delete[#,c]& /@ Delete[M,r] 

(* Predicate the determine if the nth track of a transition tuple is 
equal to a provided value k *)
NthTrackIsValueQ[tuple_, tracknum_, value_] := Equal[tuple[[tracknum]], value]

(* Project a transition trans where tracknum equals value *)
ProjectTransition[trans_, tracknum_, value_] := 
	Select[trans, NthTrackIsValueQ[#, tracknum, value]&]

(* Project entire transition relation tr by tracknum and value *)
ProjectTransitionRelation[tr_, tracknum_, value_]:= 
	Map[Function[trans, trans[[1]] -> 
		ProjectTransition[trans[[2]], tracknum, value]], 
		tr]

(* Get the accepting states from the dot file *)
GetAcceptStates[va_] := Map[ToExpression[#["Label"]]&, Select[va, Equal[#["Shape"], "doublecircle"]&]] + 1 

(* Get the Init state from the dot file *)
GetInitState[edgeRules_] := ToExpression[edgeRules["init"]] + 1;

(* Convert transition relation tr into list of relations 
for matrix-based DFA algorithms *)
RelationList[tr_] := Map[{#[[1]][[1]], #[[1]][[2]], #[[2]]} &, tr] 

ImportDFA[filename_] := Module[{G,va,er,initState,acceptStates,tr, states},
	G = Import[filename];
	a = 55;
	va = Map[Association, Import[filename, "VertexAttributes"]];
	states = Sort[ToExpression[Options[G, VertexLabels][[1]][[2]][[All,2]]]]+1;
	er = Association[Import[filename, "EdgeRules"]];
	initState = GetInitState[er];
	acceptStates = GetAcceptStates[va];
	tr = TransitionRelation[G];
	Return[Association[Q -> states, init -> initState, final -> acceptStates, delta -> tr]];
];

GeneratingFunctionSingleBitBound[DFA_] := Module[{T,GFT,GF},
	T = TransferMatrix[DFA[delta]];
	GFT = MatrixGenFun[T, 1];
	GF = Total[GFT[[DFA[init],DFA[final]]]];
	Return[Function[bound, SeriesCoefficient[GF, {z[1], 0, bound}]]]
];

CountingFunctionMatrixPower[DFA_] := Module[{A},
	A = TransferMatrix[DFA[delta]];
	Return[Function[bound, Total[MatrixPower[A, bound][[DFA[init],DFA[final]]]]]]
];

(*Functions for Binary DFA ops as Tensor products*)
TransitionRelationToSequenceAssociation[tr_] := 
 Association[
  Map[Function[
    t, {t[[1]], t[[2]]} ->    Map[seq @@ {#} &, t[[3]]]     ], tr]] 
SparseSetArray[array_] := Function[{i,j}, If[MemberQ[Keys[array], {i,j}], array[{i,j}], {}]]
Dims[assoc_] := Map[Max, Transpose[Keys[assoc]]]
SetMatrix[assoc_] := Module[{d},
	d = Dims[assoc];
    Table[SparseSetArray[assoc][i,j], {i,1,d[[1]]}, {j,1,d[[2]]}] 
]
RelationToMatrix[R_] := Module[{A, SA},
	A = TransitionRelationToSequenceAssociation[R];
	SA = SparseSetArray[A];
	SetMatrix[A]
]

Concat[{u_,v_}] := seq @@ Catenate[{List @@ u, List @@ v}]

SetConcat[U_, V_] := DeleteDuplicates[Map[Concat, Tuples[{U,V}]]] 
DotProductConcat[u_, v_] := Flatten[MapThread[SetConcat, {u,v}]] 
DFAMatrixProduct[A_, B_] := Table[DotProductConcat[u,v], {u,A}, {v, Transpose[B]}]
MatrixMultiplyBy[A_] := DFAMatrixProduct[#, A] &
StringIdentity[n_] := ID = Table[If[i==j, {seq[]}, {}], {i, 1, n}, {j, 1, n}]
DFAMatrixPower[matrix_, power_] := Nest[DFAMatrixProduct[#, matrix] &, StringIdentity[Length[matrix]], power] 
SeqToString[s_] := StringJoin[Map[ToString,List @@ s]]
TupleSeqToString[t_] := Map[SeqToString,Transpose[List @@ t] ]
TupleSeqToNum[t_] := Map[SeqToNum, Transpose[List @@ t]]
SeqToNum[s_] := Total[MapIndexed[#1 * 2^ (#2[[1]]-1) &, List @@ s]]
TupleSeqToNumTwosComplement[t_] := Map[TwosComplement, Transpose[List @@ t]]
TwosComplement[v_] := If[Last[v] == 0, SeqToNum[Drop[v,-1]], -(2^(Length[v]-1) - SeqToNum[Drop[v,-1]])]
NumsReachingStateLength[A_, state_, len_] := Map[SeqToNum, DFAMatrixPower[A,len][[1,state]] ]
NumsReachingStatesLength[A_, state1_, state2_, len_] := Map[SeqToNum, DFAMatrixPower[A,len][[state1,state2]] ]
StringsReachingStateLength[A_, state_, len_] := Map[SeqToString, DFAMatrixPower[A,len][[1,state]] ]
StringTuplesReachingStateLength[A_, state_, len_] := Map[TupleSeqToString, DFAMatrixPower[A,len][[1,state]] ]
NumTuplesReachingStateLength[A_, state_, len_] := Map[TupleSeqToNum, DFAMatrixPower[A,len][[1,state]] ]
NumTuplesReachingStateLengthTwosComplement[A_, state_, len_] := Map[TupleSeqToNumTwosComplement, DFAMatrixPower[A,len][[1,state]] ]

AcceptedNumericSetByLength[DFA_] := Module[{rl, tm},
	rl = RelationList[DFA[delta]];
	tm = RelationToMatrix[rl];
	Function[bound, Map[TupleSeqToNumTwosComplement, Flatten[DFAMatrixPower[tm, bound][[DFA[init],DFA[final]]]]]]
]


