
BeginPackage["Wolfram`Lambda`Compiled`"]

BetaReduce
BetaReduceSizes
BetaReduceSizesBLC

Begin["`Private`"]

offsetFree[expr_, offset_, depth_] := If[offset == 0, expr,
  	With[{head = expr[[0]]},
   		Which[
    		head === InertExpression[\[FormalLambda]],
    		head[offsetFree[First[expr], offset, depth + 1]]
    		,
    		Length[expr] == 1,
    		offsetFree[head, offset, depth][offsetFree[First[expr], offset, depth]]
    		,
    		head === InertExpression[Integer],
    		With[{var = Cast[expr, "MachineInteger"]}, 
     			If[var > depth, Cast[var + offset, "InertExpression"], expr]
			]
    		,
    		True,
    		expr
    	]
   	]
]

betaSubstitute[expr_, arg_, paramIdx_] := With[{head = expr[[0]]},
  	Which[
   		head === InertExpression[\[FormalLambda]],
   		head[betaSubstitute[First[expr], arg, paramIdx + 1]]
   		,
   		Length[expr] == 1,
   		betaSubstitute[head, arg, paramIdx][betaSubstitute[First[expr], arg, paramIdx]]
   		,
   		head === InertExpression[Integer],
   		With[{var = Cast[expr, "MachineInteger"]}, 
    		Which[var < paramIdx, expr, var == paramIdx, 
     			offsetFree[arg, paramIdx - 1, 0], True, 
     			Cast[var - 1, "InertExpression"]
			]
		]
   		,
   		True,
   		expr
   	]
]

betaReduce[expr_] := If[
  	Length[expr] == 1
  	,
  	With[{head = expr[[0]]},
   		If[	head === InertExpression[\[FormalLambda]],
    		With[{bodyReduce = betaReduce[expr[[1]]]},
     			If[	bodyReduce[[2]] === InertExpression[True], 
      				InertExpression[List][head[bodyReduce[[1]]], True], 
      				InertExpression[List][expr, False]
				]
     		]
			,
    		If[
     			head[[0]] === InertExpression[\[FormalLambda]], 
     			With[{arg = betaReduce[expr[[1]]]},
      				InertExpression[List][
						If[arg[[2]] === InertExpression[True], head[arg[[1]]], betaSubstitute[head[[1]], arg[[1]], 1]],
						True
					]
      			]
     			,
     			With[{headReduce = betaReduce[head]},
      				If[	headReduce[[2]] === InertExpression[True],
       					InertExpression[List][headReduce[[1]][expr[[1]]], True],
       					With[{argReduce = betaReduce[expr[[1]]]},
       						If[	argReduce[[2]] === InertExpression[True],
								InertExpression[List][headReduce[[1]][argReduce[[1]]], True],
								InertExpression[List][expr, False]
         					]
        				]
       				]
      			]
     		]
    	]
   	]
  	,
  	InertExpression[List][expr, False]
]

leafCount[expr_] := If[Length[expr] == 1, leafCount[expr[[0]]] + leafCount[expr[[1]]], 1]

lambdaBLC[expr_] := Block[{bits, i},
  	If[	expr[[0]] === InertExpression[\[FormalLambda]]
   		,
		bits = lambdaBLC[expr[[1]]];
		bits["Prepend", 0];
		bits["Prepend", 0];
		,
   		If[	Length[expr] == 1,
			bits = lambdaBLC[expr[[0]]];
			bits["Prepend", 1];
			bits["Prepend", 0];
			bits["JoinBack", lambdaBLC[expr[[1]]]];
			,
    		If[	expr[[0]] === InertExpression[Integer], 
     			bits = CreateDataStructure["ExtensibleVector"::["MachineInteger"]];
     			For[i = 0, i < Cast[expr, "MachineInteger"], i++, 
      				bits["Append", 1]
				];
     			bits["Append", 0];
     			,
     			bits = CreateDataStructure["ExtensibleVector"::["MachineInteger"]];
     		]
    	]
   	];
  	bits
]

decl = {
	FunctionDeclaration[offsetFree, Typed[DownValuesFunction[offsetFree], {"InertExpression", "MachineInteger", "MachineInteger"} -> "InertExpression"]],
   	FunctionDeclaration[betaSubstitute, Typed[DownValuesFunction[betaSubstitute], {"InertExpression", "InertExpression", "MachineInteger"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduce, Typed[DownValuesFunction[betaReduce], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[leafCount, Typed[DownValuesFunction[leafCount], {"InertExpression"} -> "MachineInteger"]],
   	FunctionDeclaration[lambdaBLC, Typed[DownValuesFunction[lambdaBLC], {"InertExpression"} -> "ExtensibleVector"::["MachineInteger"]]]
}

BetaReduce := BetaReduce = FunctionCompile[decl, Function[Typed[expr, "InertExpression"], betaReduce[expr][[1]]]]

betaReduceSizes := betaReduceSizes = FunctionCompile[decl, 
	Function[
		{Typed[expr, "InertExpression"], Typed[n, "MachineInteger"], Typed[f, {"InertExpression"} -> "MachineInteger"]},
		Block[{
			curExpr = expr, k, reduce,
			sizes = CreateDataStructure["ExtensibleVector"]
		},
			For[k = 0, k < n, k++,
				sizes["Append", f[curExpr]];
				reduce = betaReduce[curExpr];
				If[ reduce[[2]] === InertExpression[False], Break[]];
					curExpr = reduce[[1]];
				];
				InertExpression[List][curExpr, sizes["Elements"]]
			]
		]
	]

$CompiledFunctions := $CompiledFunctions = FunctionCompile[decl, <|"LeafCount" -> leafCount, "BLCsize" -> Function[Typed[expr, "InertExpression"], Length[lambdaBLC[expr]]]|>]

BetaReduceSizes[expr_, n_ : 2 ^ ($SystemWordLength - 1) - 1] := betaReduceSizes[expr, n, $CompiledFunctions["LeafCount"]]

BetaReduceSizesBLC[expr_, n_ : 2 ^ ($SystemWordLength - 1) - 1] := betaReduceSizes[expr, n, $CompiledFunctions["BLCsize"]]


End[];

EndPackage[];
