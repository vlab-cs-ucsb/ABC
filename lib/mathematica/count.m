(* ::Package:: *)

filepath = $CommandLine[[4]];
(*
filelist = If[DirectoryQ[filepath], 
			FileNames["*.dot", filepath, 
			ToExpression[$CommandLine[[5]]]], {filepath}];

filepath = "/home/lucas/Dropbox/UCSB/research/multitrack/dots/y_lte_x.dot";
*)

bound = ToExpression[$CommandLine[[5]]];

Print[filepath];

Get["utils.m"];

DFA = ImportDFA[filepath];
gf = GeneratingFunctionSingleBitBound[DFA];
mcf = CountingFunctionMatrixPower[DFA];

Print[gf[bound]];
(* Print[mcf[bound]]; *)





