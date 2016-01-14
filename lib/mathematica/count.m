(* ::Package:: *)

filepath = $CommandLine[[4]];

bound = ToExpression[$CommandLine[[5]]];

Get["utils.m"];

DFA = ImportDFA[filepath];
(* gf = GeneratingFunctionSingleBitBound[DFA]; *)
mcf = CountingFunctionMatrixPower[DFA];

Print[mcf[bound]];
(* Print[gf[bound]]; *)





