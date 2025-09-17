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
    RandomSizeLambda,
	FindMinimalLambdaCombinator
]

Begin["`Private`"]

constructGroupings = Function[Groupings[#, Construct -> 2]]

EnumerateLambdas[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1, partsQ_ : True] :=
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
] := Join[
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



Options[FindMinimalLambdaCombinator] =
	DeleteDuplicatesBy[First] @ Join[
		{TimeConstraint -> 10, MaxSteps -> 100, "MaxSize" -> 100, "IncludeArguments" -> False, "Parallel" -> False},
		Options[BetaReduce],
		Options[ResourceFunction["CombinatorFixedPoint"]]
	];

$CombinatorOrder = "Leftmost" | "Rightmost" | "Outermost" | "Innermost";

FindMinimalLambdaCombinator[lambda_,
	maxSize : _Integer | Automatic : Automatic,
	n : _Integer | Infinity : Infinity, m : _Integer | Infinity : 1,
	scheme : {$CombinatorOrder, $CombinatorOrder} | {$CombinatorOrder, $CombinatorOrder, _Integer | Infinity} : {"Leftmost", "Outermost"},
	i_Integer : 1,
	opts : OptionsPattern[]
] :=
Enclose @ Block[{
	term, j = i, args = {},
	lambdaOptions = FilterRules[{opts}, Options[BetaReduce]],
	combinatorOptions = FilterRules[{opts}, Options[ResourceFunction["CombinatorFixedPoint"]]],
	includeArgsQ = TrueQ[OptionValue["IncludeArguments"]]
},
	term = BetaReduce[UntagLambda[lambda], n, m, lambdaOptions];

	Confirm @ TimeConstrained[
		Until[BetaNormalQ[term[\[FormalX]]],
			AppendTo[args, AlphabetString[j++]];
			term = BetaReduce[term[args[[-1]]], n, m, lambdaOptions];
		],
		OptionValue[TimeConstraint]
	];

	term = term /. l : $Lambda[_] :> If[ClosedLambdaQ[l], Confirm @ FindMinimalLambdaCombinator[l, maxSize, n, m, scheme, j, opts], LambdaCombinator[l]];
	If[FreeQ[term, Alternatives @@ args], Sow[args]; Return[LambdaCombinator[lambda]]];
	Block[{step, combs, total, found = Missing["NotFound", term], parallelQ = TrueQ[OptionValue["Parallel"]]},
		If[ parallelQ,
			SetSharedVariable[step, Unevaluated[found], Unevaluated[args], Unevaluated[term], Unevaluated[combinatorOptions], Unevaluated[includeArgsQ]]
		];
		Do[
			If[! MissingQ[found], Break[]];
			step = 0;
			combs = ResourceFunction["EnumerateCombinators"][k];
			total = Length[combs];
			Progress`EvaluateWithProgress[
				If[ k > 5 && parallelQ, ParallelDo, Do][
					CheckAbort[
						If[! MissingQ[found], Break[]];
						step++;
						With[{combTerm = Fold[Construct, comb, args]},
							If[
								term === ResourceFunction["CombinatorFixedPoint"][
									combTerm,
									scheme,
									combinatorOptions
								]
								,
								found = If[includeArgsQ, combTerm, comb]
							]
						],
						found = $Aborted;
						Break[]
					]
					,
					{comb, combs}
				]
				,
				<|"Text" -> StringTemplate["Searching size-`` combinators"][k], "Percentage" :> step / total, "ElapsedTime" -> Automatic, "RemainingTime" -> Automatic|>
			];
			,
			{k, Replace[maxSize, Automatic :> LeafCount[LambdaCombinator[lambda]]]}
		];
			
		Sow[args];
		found
	]
]


End[]

EndPackage[]