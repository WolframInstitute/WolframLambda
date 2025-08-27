
BeginPackage["Wolfram`Lambda`Compiled`"]

ClearAll[
	BetaReduceCompiled,
	BetaReduceListCompiled,
	BetaReduceSizesCompiled,
	$CompiledFunctions
]


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
    		Which[
				var < paramIdx, expr,
				var == paramIdx, offsetFree[arg, paramIdx - 1, 0],
				True, Cast[var - 1, "InertExpression"]
			]
		]
   		,
   		True,
   		expr
   	]
]

betaReduceApplicative[expr_] := If[
  	Length[expr] == 1
  	,
  	With[{head = expr[[0]]},
   		If[	head === InertExpression[\[FormalLambda]],
    		With[{bodyReduce = betaReduceApplicative[expr[[1]]]},
     			If[	bodyReduce[[2]] === InertExpression[True], 
      				InertExpression[List][head[bodyReduce[[1]]], True], 
      				InertExpression[List][expr, False]
				]
     		]
			,
    		If[
     			head[[0]] === InertExpression[\[FormalLambda]], 
     			With[{argReduce = betaReduceApplicative[expr[[1]]]},
      				InertExpression[List][
						If[	argReduce[[2]] === InertExpression[True], head[argReduce[[1]]],
							With[{bodyReduce = betaReduceApplicative[head[[1]]]},
								If[ bodyReduce[[2]] === InertExpression[True],
									InertExpression[\[FormalLambda]][bodyReduce[[1]]][expr[[1]]],
									betaSubstitute[head[[1]], argReduce[[1]], 1]
								]
							]
						],
						True
					]
      			]
     			,
     			With[{headReduce = betaReduceApplicative[head]},
      				If[	headReduce[[2]] === InertExpression[True],
       					InertExpression[List][headReduce[[1]][expr[[1]]], True],
       					With[{argReduce = betaReduceApplicative[expr[[1]]]},
       						If[	argReduce[[2]] === InertExpression[True],
								InertExpression[List][head[argReduce[[1]]], True],
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
     			InertExpression[List][betaSubstitute[head[[1]], expr[[1]], 1], True]
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

betaReduceInner[expr_] := If[
  	Length[expr] == 1
  	,
  	With[{head = expr[[0]]},
   		If[	head === InertExpression[\[FormalLambda]],
    		With[{bodyReduce = betaReduceInner[expr[[1]]]},
     			If[	bodyReduce[[2]] === InertExpression[True], 
      				InertExpression[List][head[bodyReduce[[1]]], True], 
      				InertExpression[List][expr, False]
				]
     		]
			,
            With[{headReduce = betaReduceInner[head]},
                If[	headReduce[[2]] === InertExpression[True],
                    InertExpression[List][headReduce[[1]][expr[[1]]], True],
                    With[{argReduce = betaReduceInner[expr[[1]]]},
                        If[	argReduce[[2]] === InertExpression[True],
                            InertExpression[List][headReduce[[1]][argReduce[[1]]], True],
                            If[
                                head[[0]] === InertExpression[\[FormalLambda]], 
                                InertExpression[List][betaSubstitute[head[[1]], expr[[1]], 1], True],
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


(* Non-recursive beta reduction *)

offsetFreeIterative[expr_, offset_, depth0_] := Module[{
	listHead = InertExpression[List],
	lambdaHead = InertExpression[\[FormalLambda]],
	intHead = InertExpression[Integer],
	work = CreateDataStructure["Stack"],
	res = CreateDataStructure["Stack"],
	frame, tag, node, depth, head, var, body, arg, headVal, argRes
},
    
  	work["Push", listHead["enter", expr, depth0]];
  	
  	While[! work["EmptyQ"],
   		frame = work["Pop"];  
   		tag = frame[[1]];
   		Switch[tag,
			InertExpression["enter"],
				node = frame[[2]];
				depth = frame[[3]];
				head = node[[0]];
				
				Which[
					head === lambdaHead && Length[node] == 1,
						work["Push", listHead["exitLambda", depth]];
						work["Push", listHead["enter", node[[1]], Cast[depth, "MachineInteger"] + 1]]
					,
					Length[node] == 1,
						work["Push", listHead["exitAppHead", depth, node[[1]]]];
						work["Push", listHead["enter", head, depth]]
					,
					head === intHead,
						var = Cast[node, "MachineInteger"];
						If[	var > Cast[depth, "MachineInteger"],
							res["Push", Cast[var + offset, "InertExpression"]],
							res["Push", node]
						]
					,
					True,
						res["Push", node]
				]
			,
			InertExpression["exitLambda"],
				depth = frame[[2]];
				body = res["Pop"];
				res["Push", lambdaHead[body]]
			,
			InertExpression["exitAppHead"],
				depth = frame[[2]];
				arg = frame[[3]];
				headVal = res["Pop"];
				work["Push", listHead["exitApp", depth, headVal]];
				work["Push", listHead["enter", arg, depth]]
			,
			InertExpression["exitApp"],
				argRes = res["Pop"];
				headVal = frame[[3]];
				res["Push", headVal[argRes]]
		]
   	];
  	res["Pop"]
]

betaSubstituteIterative[body_, arg_, paramIdx_] := Module[{
	listHead = InertExpression[List],
	lambdaHead = InertExpression[\[FormalLambda]],
	intHead = InertExpression[Integer],
	work = CreateDataStructure["Stack"],
	res = CreateDataStructure["Stack"],
	frame, tag, node, depth, d, head, var, bodyRes, argRes
},
    
  	work["Push", listHead["enter", body, paramIdx]];
  	
  	While[! work["EmptyQ"],
   		frame = work["Pop"];
   		tag = frame[[1]];
   		Switch[tag,
			InertExpression["enter"],
				node = frame[[2]];
				depth = frame[[3]];
				
				head = node[[0]];
				Which[
					head === lambdaHead && Length[node] == 1,
						work["Push", listHead["exitLambda", depth]];
						work["Push", listHead["enter", node[[1]], Cast[depth, "MachineInteger"] + 1]]
					,
					Length[node] == 1,
						work["Push", listHead["exitAppHead", depth, node[[1]]]];
						work["Push", listHead["enter", head, depth]]
					,
					head === intHead,
						var = Cast[node, "MachineInteger"];
						d = Cast[depth, "MachineInteger"];
						Which[
							var < d,
								res["Push", node],
							var == d,
								res["Push", offsetFreeIterative[arg, d - 1, 0]],
							var > d,
								res["Push", Cast[var - 1, "InertExpression"]]
						]
					,
					True,
						res["Push", node]
				]
			,
			InertExpression["exitLambda"],
				depth = frame[[2]];
				bodyRes = res["Pop"];
				res["Push", lambdaHead[bodyRes]]
			,
			InertExpression["exitAppHead"],
				depth = frame[[2]];
				argRes = frame[[3]];
				head = res["Pop"];
				work["Push", listHead["exitApp", depth, head]];
				work["Push", listHead["enter", argRes, depth]]
			,
			InertExpression["exitApp"],
				argRes = res["Pop"];
				head = frame[[3]];
				res["Push", head[argRes]]
		]
   	];
  	res["Pop"]
]

betaReduceIterative[expr_] := Module[{
	listHead = InertExpression[List],
	lambdaHead = InertExpression[\[FormalLambda]],
	work = CreateDataStructure["Stack"],
	res = CreateDataStructure["Stack"],
	frame, tag, node, depth, head, body, arg, headVal, argRes,
	reducedQ = False
},

    work["Push", listHead["enter", expr, 0]];
    
  	While[! work["EmptyQ"],
   		frame = work["Pop"];
   		tag = frame[[1]];
   		Switch[tag,
			InertExpression["enter"],
				node = frame[[2]];
				depth = frame[[3]];
				head = node[[0]];
				If[ reducedQ,
					res["Push", node]
					,
					Which[
						head === lambdaHead && Length[node] == 1,
							work["Push", listHead["exitLambda", depth]];
							work["Push", listHead["enter", node[[1]], Cast[depth, "MachineInteger"] + 1]]
						,
						Length[node] == 1,
							If[ head[[0]] === lambdaHead && Length[head] == 1,
								body = head[[1]];
								arg = node[[1]];
								res["Push", betaSubstituteIterative[body, arg, 1]];
								reducedQ = True
								,
								work["Push", listHead["exitAppHead", depth, node[[1]]]];
								work["Push", listHead["enter", head, depth]]
							]
						,
						True,
							res["Push", node]
					]
				]
			,
			InertExpression["exitLambda"],
				body = res["Pop"];
				res["Push", lambdaHead[body]]
			,
			InertExpression["exitAppHead"],
				depth = frame[[2]];
				arg = frame[[3]];
				headVal = res["Pop"];
				work["Push", listHead["exitApp", depth, headVal]];
				work["Push", listHead["enter", arg, depth]]
			,
			InertExpression["exitApp"],
				argRes = res["Pop"];
				headVal = frame[[3]];
				res["Push", headVal[argRes]]
		]
   	];
  	
  	listHead[res["Pop"], reducedQ]
]


betaReduceInnerIterative[expr_] := Module[{
    listHead = InertExpression[List],
    lambdaHead = InertExpression[\[FormalLambda]],
    work = CreateDataStructure["Stack"],
    res = CreateDataStructure["Stack"],
    frame, tag, node, headVal, argVal, reducedQ = False
},
  
	work["Push", listHead["enter", expr]];
	
	While[! work["EmptyQ"],
		frame = work["Pop"];
		tag = frame[[1]];
		Switch[tag,
			InertExpression["enter"],
				node = frame[[2]];
				If[ Length[node] == 1,
					If[ node[[0]] === lambdaHead,
						work["Push", listHead["exitLambda"]];
						work["Push", listHead["enter", node[[1]]]]
						,
						work["Push", listHead["exitApp"]];
						work["Push", listHead["enter", node[[1]]]];
						work["Push", listHead["enter", node[[0]]]]
					]
					,
					res["Push", node]
				]
			,
			InertExpression["exitLambda"],
				res["Push", lambdaHead[res["Pop"]]]
			,
			InertExpression["exitApp"],
				argVal = res["Pop"];
				headVal = res["Pop"];
				If[ ! reducedQ && headVal[[0]] === lambdaHead && Length[headVal] == 1,
					res["Push", betaSubstituteIterative[headVal[[1]], argVal, 1]];
					reducedQ = True
					,
					res["Push", headVal[argVal]]
				]
			]
	];
	listHead[res["Pop"], reducedQ]
]


betaReduceApplicativeIterative[expr_] := Module[{
    listHead = InertExpression[List],
    lambdaHead = InertExpression[\[FormalLambda]],
    work = CreateDataStructure["Stack"],
    res = CreateDataStructure["Stack"],
    frame, tag, node, headVal, argVal, reducedQ = False
},
  
	work["Push", listHead["enter", expr]];
	
	While[! work["EmptyQ"],
		frame = work["Pop"];
		tag = frame[[1]];
		Switch[tag,
			InertExpression["enter"],
				node = frame[[2]];
				If[ Length[node] == 1,
					If[ node[[0]] === lambdaHead,
						work["Push", listHead["exitLambda"]];
						work["Push", listHead["enter", node[[1]]]]
						,
						If[ node[[0]][[0]] === lambdaHead,
							work["Push", listHead["exitApp", "right"]];
							work["Push", listHead["enter", node[[0]]]];
							work["Push", listHead["enter", node[[1]]]]
							,
							work["Push", listHead["exitApp", "left"]];
							work["Push", listHead["enter", node[[1]]]];
							work["Push", listHead["enter", node[[0]]]]
						]
					]
					,
					res["Push", node]
				]
			,
			InertExpression["exitLambda"],
				res["Push", lambdaHead[res["Pop"]]]
			,
			InertExpression["exitApp"],
				If[ frame[[2]] === InertExpression["left"],
					argVal = res["Pop"];
					headVal = res["Pop"]
					,
					headVal = res["Pop"];
					argVal = res["Pop"]
				];
				If[ ! reducedQ && headVal[[0]] === lambdaHead && Length[headVal] == 1,
					res["Push", betaSubstituteIterative[headVal[[1]], argVal, 1]];
					reducedQ = True
					,
					res["Push", headVal[argVal]]
				]
			]
	];
	listHead[res["Pop"], reducedQ]
]


leafCountIterative[expr_] := Module[{
    stack = CreateDataStructure["Stack"],
 	node, count = 0
},
  
	stack["Push", expr];
	
	While[! stack["EmptyQ"],
		node = stack["Pop"];
		If[ Length[node] == 1,
			stack["Push", node[[0]]];
			stack["Push", node[[1]]]
			,
			count++
		]
	];
	count
]

lambdaBLCIterative[expr_] := Module[{
    listHead = InertExpression[List],
    lambdaHead = InertExpression[\[FormalLambda]],
    intHead = InertExpression[Integer],
    work = CreateDataStructure["Stack"],
    res = CreateDataStructure["Stack"],
    frame, tag, node, headBits, argBits, bodyBits, var, bits, head, arg
},
  
  	work["Push", listHead["enter", expr]];
  
	While[! work["EmptyQ"],
		frame = work["Pop"];
		tag = frame[[1]];
		Switch[tag,
			InertExpression["enter"],
				node = frame[[2]];
				head = node[[0]];
				Which[
					head === lambdaHead && Length[node] == 1,
						work["Push", listHead["exitLambda"]];
						work["Push", listHead["enter", node[[1]]]]
					,
					Length[node] == 1,
						work["Push", listHead["exitApp"]];
						arg = node[[1]];
						head = node[[0]];
						work["Push", listHead["enter", arg]];
						work["Push", listHead["enter", head]]
					,
										head === intHead,
						var = Cast[node, "MachineInteger"];
						bits = CreateDataStructure["ExtensibleVector"::["MachineInteger"]];
						Do[ bits["Append", 1], {var} ];
						bits["Append", 0];
						res["Push", bits]
					,
					True,
						bits = CreateDataStructure["ExtensibleVector"::["MachineInteger"]];
						res["Push", bits]
				]
			,
			InertExpression["exitLambda"],
				bodyBits = res["Pop"];
				bodyBits["Prepend", 0];
				bodyBits["Prepend", 0];
				res["Push", bodyBits]
			,
			InertExpression["exitApp"],
				argBits = res["Pop"];
				headBits = res["Pop"];
				headBits["Prepend", 1];
				headBits["Prepend", 0];
				headBits["JoinBack", argBits];
				res["Push", headBits]
			]
	];
	res["Pop"]
]


decl = {
	FunctionDeclaration[offsetFree, Typed[DownValuesFunction[offsetFree], {"InertExpression", "MachineInteger", "MachineInteger"} -> "InertExpression"]],
   	FunctionDeclaration[betaSubstitute, Typed[DownValuesFunction[betaSubstitute], {"InertExpression", "InertExpression", "MachineInteger"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduceApplicative, Typed[DownValuesFunction[betaReduceApplicative], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduceInner, Typed[DownValuesFunction[betaReduceInner], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduce, Typed[DownValuesFunction[betaReduce], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[leafCount, Typed[DownValuesFunction[leafCount], {"InertExpression"} -> "MachineInteger"]],
   	FunctionDeclaration[lambdaBLC, Typed[DownValuesFunction[lambdaBLC], {"InertExpression"} -> "ExtensibleVector"::["MachineInteger"]]],
	FunctionDeclaration[offsetFreeIterative, Typed[DownValuesFunction[offsetFreeIterative], {"InertExpression", "MachineInteger", "MachineInteger"} -> "InertExpression"]],
   	FunctionDeclaration[betaSubstituteIterative, Typed[DownValuesFunction[betaSubstituteIterative], {"InertExpression", "InertExpression", "MachineInteger"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduceApplicativeIterative, Typed[DownValuesFunction[betaReduceApplicativeIterative], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduceInnerIterative, Typed[DownValuesFunction[betaReduceInnerIterative], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[betaReduceIterative, Typed[DownValuesFunction[betaReduceIterative], {"InertExpression"} -> "InertExpression"]],
   	FunctionDeclaration[leafCountIterative, Typed[DownValuesFunction[leafCountIterative], {"InertExpression"} -> "MachineInteger"]],
   	FunctionDeclaration[lambdaBLCIterative, Typed[DownValuesFunction[lambdaBLCIterative], {"InertExpression"} -> "ExtensibleVector"::["MachineInteger"]]]
}

$CompiledFunctions := $CompiledFunctions = Enclose[
    ConfirmBy[Once[CloudGet["https://www.wolframcloud.com/obj/nikm/CompiledLambdaFunctions"]], AssociationQ],
    FunctionCompile	[decl, <|
        "BetaReduce" -> betaReduce,
        "BetaReduceApplicative" -> betaReduceApplicative,
        "BetaReduceInner" -> betaReduceInner,
        "LeafCount" -> leafCount,
		"LambdaBLC" -> lambdaBLC,
        "BLCsize" -> Function[Typed[expr, "InertExpression"], Length[lambdaBLC[expr]]],

        "BetaReduceIterative" -> betaReduceIterative,
        "BetaReduceApplicativeIterative" -> betaReduceApplicativeIterative,
        "BetaReduceInnerIterative" -> betaReduceInnerIterative,
        "LeafCountIterative" -> leafCountIterative,
		"LambdaBLCIterative" -> lambdaBLCIterative,
        "BLCsizeIterative" -> Function[Typed[expr, "InertExpression"], Length[lambdaBLCIterative[expr]]],

        "BetaReduceSizes" -> Function[
            {Typed[expr, "InertExpression"], Typed[n, "InertExpression"], Typed[f, {"InertExpression"} -> "MachineInteger"], Typed[reduce, {"InertExpression"} -> "InertExpression"]},
            Block[{
                sizes = CreateDataStructure["ExtensibleVector"],
                fixPointQ = Head[n] === InertExpression[UpTo],
                curExpr = expr, reduced,
                limit, k
            },
                limit = Cast[If[fixPointQ, n[[1]], n], "MachineInteger"];
                For[k = 0, k < limit, k++,
                    sizes["Append", f[curExpr]];
                    reduced = reduce[curExpr];
                    If[ fixPointQ && reduced[[2]] === InertExpression[False], Break[]];
                    curExpr = reduced[[1]];
                ];
                InertExpression[List][curExpr, sizes["Elements"]]
            ]
        ]
	|>, TargetSystem -> Automatic] &
]

$ReduceFunction = "BetaReduce" | "BetaReduceInner" | "BetaReduceApplicative" | "BetaReduceIterative" | "BetaReduceInnerIterative" | "BetaReduceApplicativeIterative"
$SizeFunction = "LeafCount" | "BLCsize" | "LeafCountIterative" | "BLCsizeIterative"

BetaReduceCompiled[expr_, n : _Integer : Infinity, reduce : $ReduceFunction : "BetaReduce"] :=
    NestWhile[$CompiledFunctions[reduce][#[[1]]] &, {expr, True}, #[[2]] &, 1, n][[1]]

BetaReduceListCompiled[expr_, n : _Integer | Infinity : Infinity, reduce : $ReduceFunction : "BetaReduce"] :=
    NestWhileList[$CompiledFunctions[reduce][#[[1]]] &, {expr, True}, #[[2]] &, 1, n][[All, 1]]

BetaReduceSizesCompiled[expr_, n : _Integer | UpTo[_Integer] : UpTo[2 ^ ($SystemWordLength - 1) - 1], reduce : $ReduceFunction : "BetaReduce", size : $SizeFuntcion : "LeafCountIterative"] :=
    $CompiledFunctions["BetaReduceSizes"][expr, n, $CompiledFunctions[size], $CompiledFunctions[reduce]]

ResourceFunction["AddCodeCompletion"]["BetaReduceCompiled"][None, None, List @@ $ReduceFunction]
ResourceFunction["AddCodeCompletion"]["BetaReduceListCompiled"][None, None, List @@ $ReduceFunction]
ResourceFunction["AddCodeCompletion"]["BetaReduceSizesCompiled"][None, None, List @@ $ReduceFunction, List @@ $SizeFunction]


End[];

EndPackage[];
