BeginPackage["Wolfram`Lambda`"]

ClearAll[
    EnumerateLambdas,
    EnumerateAffineLambdas,
    EnumerateLinearLambdas,
    AffineLambdaQ,
    LinearLambdaQ,
    EnumerateSizeLambdas,
    LambdaSize,
    RandomLambda,
    RandomSizeLambda
]

Begin["`Private`"]

constructGroupings = Function[Groupings[#, Construct -> 2]]

EnumerateLambdas[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1, partsQ_ : True] := EnumerateLambdas[maxDepth, maxLength, depth, partsQ] =
	Catenate @ Map[
		constructGroupings @ Tuples[
			$Lambda /@ If[ depth == maxDepth,
				constructGroupings @ Catenate[Tuples[Range[maxDepth], #] & /@ Range[maxLength]],
				constructGroupings @ Catenate[Tuples[Join[Range[depth], EnumerateLambdas[maxDepth, maxLength - # + 1, depth + 1, False]], #] & /@ Range[maxLength]]
			],
			#
		] &,
	Range[If[partsQ, maxLength, 1]]
]

enumerateLambdas[limit : _Integer | UpTo[_Integer] : 1, n_Integer, vars_List : {}, depth_Integer : 1, partsQ : _ ? BooleanQ : True] :=
	enumerateLambdas[limit, n, vars, depth, partsQ] =
	If[ n == 0,
		constructGroupings[Permutations[vars]],
		Join[
			$Lambda /@ Catenate[
				enumerateLambdas[
					limit,
					n - 1,
					Join[
						vars + 1,
						#
					],
					depth + 1
				] & /@ Replace[limit, {UpTo[x_Integer] :> (ConstantArray[1, #] & /@ Range[0, x]), x_Integer :> {ConstantArray[1, x]}}]
			]
			,
			Catenate @ Map[
				subVars |-> Catenate[{#1[#2], #2[#1]} & @@@ Tuples[{enumerateLambdas[limit, n, DeleteElements[vars, 1 -> subVars], depth], constructGroupings @ Permutations[subVars]}]],
				DeleteDuplicates @ Rest[Subsets[vars]]
			]
			,	
			If[	partsQ && n > 1,
				Flatten[
					Table[
						constructGroupings /@ Tuples[MapThread[enumerateLambdas[limit, ##, depth, False] &, {partition, subVars}]],
						{partition, Catenate[Permutations /@ IntegerPartitions[n, {2, n}]]},
						{subVars, Catenate[Permutations[PadRight[#, Length[partition], {{}}]] & /@
							Catenate[ResourceFunction["KSetPartitions"][vars, #] & /@ Range[0, Min[Length[vars], Length[partition]]]]]}
					],
					3
				],
				{}
			]
		]
	]

EnumerateAffineLambdas[n_Integer ? Positive, limit_Integer : 1] := enumerateLambdas[UpTo[limit], n]

EnumerateLinearLambdas[n_Integer ? Positive, limit_Integer : 1] := enumerateLambdas[limit, n]

AffineLambdaQ[lambda_, n_Integer : 1] := AllTrue[LambdaPositions[lambda], Length[#] <= n &]

LinearLambdaQ[lambda_, n_Integer : 1] := AllTrue[LambdaPositions[lambda], Length[#] == n &]


EnumerateSizeLambdas[
	size_Integer,
	lambdaSize : _Integer ? Positive : 1,
	appSize_Integer : 0,
	varSize_Integer : 0,
	depth_Integer : 1,
	partsQ : _ ? BooleanQ : True
] := EnumerateSizeLambdas[size, lambdaSize, appSize, varSize, depth, partsQ] = Join[
	$Lambda /@ Catenate @ Map[m |->
		Catenate @ Map[
			Catenate[constructGroupings /@ Tuples @
				Map[k |->
					Join[
						EnumerateSizeLambdas[k, lambdaSize, appSize, varSize, depth + 1, False],
						If[	varSize > 0,
							If[k > 1, With[{i = (k - 1) / varSize}, If[IntegerQ[i] && i <= depth, {i}, {}]], {}],
							If[k == 1, Range[depth], {}]
						]
					],
					#
				]
			] &,
			Catenate[Permutations /@ IntegerPartitions[size - lambdaSize - (m - 1) * appSize, {m}]]
		],
		Range[size - lambdaSize]
	]
	,
	If[	partsQ,
		Catenate @ Map[
			Catenate[constructGroupings /@ Tuples @ Map[EnumerateSizeLambdas[#, lambdaSize, appSize, varSize, depth] & , #]] &,
			Catenate[Permutations /@ IntegerPartitions[size - appSize, {2}, Range[lambdaSize + 1, size - appSize - lambdaSize - 1]]]
		],
		{}
	]
]


LambdaSize[expr_, lambdaSize : _Integer ? Positive : 1, appSize_Integer : 0, varSize_Integer : 0] := With[{lambda = UntagLambda[expr]},
	Total[Cases[lambda, #, All, Heads -> True] & /@ {$Lambda[_] -> lambdaSize, Except[$Lambda][_] -> appSize, x_Integer :> varSize * x + 1}, 2]
]


randomGrouping[xs_List] := Replace[xs, {
	{x_} :> x,
	{x_, y_} :> x[y],
	{x_, y_, z__} :> With[{g = randomGrouping[{y, z}]},
		MapAt[x, g, {RandomChoice[Cases[Position[g, Except[$LambdaPattern], Heads -> True], {0 ...}]]}]
	]
}]

randomIntegerPartition[n_Integer] := If[n <= 3, {n}, With[{x = RandomChoice[Append[Range[2, n - 2], n]]}, If[x == n, {n}, Prepend[randomIntegerPartition[n - x], x]]]]

randomLambda[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1] := If[ depth == maxDepth,
	With[{lambdaQ = RandomReal[] < .5}, If[lambdaQ, $Lambda, Identity] @ randomGrouping @ RandomInteger[{1, If[lambdaQ, depth, depth - 1]}, RandomInteger[{1, maxLength}]]],
	$Lambda @ randomGrouping @ Table[randomLambda[maxDepth, maxLength, depth + 1], RandomInteger[{1, maxLength}]]
]


RandomLambda[maxDepth_Integer : 2, maxLength_Integer : 2, n : _Integer | Automatic : Automatic] := If[n === Automatic, randomLambda[maxDepth, maxLength], Table[randomLambda[maxDepth, maxLength], n]]


randomPopulateLambda[head_[arg_], depth_Integer : 1] := With[{
	headLambda = If[AtomQ[head], RandomChoice[Prepend[$Lambda] @ Range[depth]], randomPopulateLambda[head, depth]]
}, {
	newDepth = depth + If[headLambda === $Lambda, 1, 0]
},
	headLambda[If[AtomQ[arg], RandomInteger[{1, newDepth}], randomPopulateLambda[arg, newDepth]]]
]
randomPopulateLambda[_, depth_Integer : 1] := RandomInteger[{1, depth}]

randomSizeLambda[size_Integer] := randomGrouping[$Lambda[randomPopulateLambda[randomGrouping[Range[# - 1]]]] & /@ randomIntegerPartition[size]]

RandomSizeLambda[size_Integer, n : _Integer | Automatic : Automatic] /; size > 1 :=
	If[n === Automatic, randomSizeLambda[size], Table[randomSizeLambda[size], n]]


End[]

EndPackage[]