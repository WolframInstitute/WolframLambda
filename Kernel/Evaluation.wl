BeginPackage["Wolfram`Lambda`"];

ClearAll[
	LambdaSubstitute,
	EvalLambda,

	BetaSubstitute,
	BetaReducePositions,
	BetaReductions,
	BetaPositionReductions,
	BetaReduce,
    BetaReduceTag,
	BetaReduceFixedPointList,
	BetaReduceList,
	BetaReduceListPositions,
	BetaReduceSizes,
	LambdaLifetime,
	EtaReduce,

	BetaReducePath,
	LambdaPathEvents,

	FindMinimalLambdaCombinator,
	FindMinimalCombinatorLambda
]

Begin["`Private`"]


(* offset only the free variables in a lambda term *)
offsetFree[expr_, 0, ___] := expr
offsetFree[(lambda : $LambdaPattern)[body_], offset_, depth_ : 0] := lambda[offsetFree[body, offset, depth + 1]]
offsetFree[v : Interpretation[var_Integer, _], offset_, depth_ : 0] := ReplacePart[v, 1 -> offsetFree[var, offset, depth]]
offsetFree[v : Interpretation[Style[var_Integer, style___], _], offset_, depth_ : 0] := ReplacePart[v, 1 -> Style[offsetFree[var, offset, depth], style]]
offsetFree[fun_[x_], offset_, depth_ : 0] := offsetFree[fun, offset, depth][offsetFree[x, offset, depth]]
offsetFree[var_Integer, offset_, depth_ : 0] := If[var > depth, var + offset, var]
offsetFree[expr_, offset_, depth_ : 0] := expr


$betaSubstituteCounter

(* perform a substitution of an argument into the body of a lambda, and also decrement the free parameters by one *)
betaSubstitute[(lambda : $LambdaPattern)[body_], arg_, paramIdx_ : 1] := lambda[betaSubstitute[body, arg, paramIdx + 1]]
betaSubstitute[v : Interpretation[var_Integer | Style[var_Integer, style___], tag_], arg_, paramIdx_ : 1] := Block[{index = <||>},
	Which[
		var < paramIdx, v,
		var == paramIdx, offsetFree[arg, paramIdx - 1] //.
			Interpretation[l : "\[Lambda]" | Style["\[Lambda]", ___], subTag : Except[tag -> _]][body_] :> With[{
				i = Lookup[$betaSubstituteCounter, subTag, $betaSubstituteCounter[subTag] = 0]
			}, {newTag = Hash[Unevaluated[Subscript[subTag, i]]]},
				$betaSubstituteCounter[subTag]++;
				Function[Null,
					Interpretation[l, tag -> newTag -> #][body /. Interpretation[e_, subTag] :> Interpretation[e, tag -> newTag -> #]],
					HoldFirst
				] @@ Replace[Hold[subTag], Hold[_ -> x_] :> Hold[x]]
			],
		var > paramIdx, Interpretation[Evaluate @ Switch[v, Interpretation[_Style, _], Style[var - 1, style], _, var - 1], tag]
	]
]

betaSubstitute[fun_[x_], arg_, paramIdx_ : 1] := betaSubstitute[fun, arg, paramIdx][betaSubstitute[x, arg, paramIdx]]
betaSubstitute[var_Integer, arg_, paramIdx_ : 1] := Which[
	var < paramIdx, var,
	var == paramIdx, offsetFree[arg, paramIdx - 1],
	var > paramIdx, var - 1
]
betaSubstitute[expr_, arg_, paramIdx_ : 1] := expr

BetaSubstitute[$LambdaPattern[body_][arg_]] := Block[{$betaSubstituteCounter = <||>}, betaSubstitute[body, arg]]
BetaSubstitute[expr_] := expr

Options[BetaReducePositions] = Options[TreePosition]

BetaReducePositions[expr_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := With[{order = OptionValue[TreeTraversalOrder]},
	Switch[order,
		"Applicative",
		ApplicativePosition[expr, n],
		Automatic | "Normal" | "Leftmost",
		NormalPosition[expr, $LambdaPattern[_][_], n],
		"Outer" | "Outermost",
		OuterPosition[expr, $LambdaPattern[_][_], n],
		"Random",
		RandomSample[Position[expr, $LambdaPattern[_][_], Heads -> True], UpTo[n]],
		"ChildrenFirst",
		Take[Catenate @ GatherBy[LexicographicSort @ Position[expr, $LambdaPattern[_][_], Heads -> True], Drop[#, - Min[Length[#], 1] ] &], UpTo[n]],
		_,
		TreePosition[ExpressionTree[expr, "Subexpressions", Heads -> True], $LambdaPattern[_][_], All, n, TreeTraversalOrder -> order] - 1
	]
]

Options[BetaReductions] = Options[BetaPositionReductions] = Options[BetaReducePositions]

BetaReductions[expr_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] :=
	MapAt[BetaSubstitute, expr, {#}] & /@ BetaReducePositions[expr, n, opts]

BetaPositionReductions[expr_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := 
	AssociationMap[MapAt[BetaSubstitute, expr, {#}] &, BetaReducePositions[expr, n, opts]]


Options[BetaReduce] = Options[BetaReduceFixedPointList] = Options[BetaReducePositions]

BetaReduce[expr_, n : _Integer | Infinity : Infinity, m : _Integer | Infinity : 1, opts : OptionsPattern[]] := 
 	FixedPoint[MapAt[BetaSubstitute, #, Sow[BetaReducePositions[#, m, opts], "Positions"]] &, expr, n]


BetaReduceTag[lambda_, tag_] := MapAt[BetaSubstitute, lambda, Position[lambda, Interpretation["\[Lambda]", tag][_][_]]]


BetaReduceFixedPointList[expr_, n : _Integer | Infinity : Infinity, m : _Integer | Infinity : 1, opts : OptionsPattern[]] := 
 	FixedPointList[MapAt[BetaSubstitute, #, Sow[BetaReducePositions[#, m, opts], "Positions"]] &, expr, n]

Options[BetaReduceList] = Join[{ProgressReporting -> True}, Options[BetaReducePositions]]

BetaReduceList[expr_, n : _Integer | Infinity | UpTo[_Integer | Infinity] : Infinity, m : _Integer | Infinity : 1, opts : OptionsPattern[]] := Module[{
	subOpts = FilterRules[{opts}, Options[BetaReducePositions]],
	limit = Replace[n, _[x_] :> x],
	fixPointQ = MatchQ[n, _UpTo],
	lambda = expr,
	lambdas = {expr},
	k = 0,
	progressFunction
},
	progressFunction = If[TrueQ[OptionValue[ProgressReporting]],
		Function[code,
			Progress`EvaluateWithProgress[
				code,
				<|"Text" -> "Reducing lambda expression", "Progress" :> k / limit, "Percentage" :> k / limit, "ElapsedTime" -> Automatic, "RemainingTime" -> Automatic|>
			],
			HoldFirst
		],
		Identity
	];
	progressFunction @ While[True,
		pos = Sow[BetaReducePositions[lambda, m, subOpts], "Positions"];
		
		If[fixPointQ && pos === {} || k++ >= limit, Break[]];
		AppendTo[lambdas, lambda = MapAt[BetaSubstitute, lambda, pos]];
	];
	lambdas
]


Options[BetaReduceListPositions] = Options[BetaReduceList]

BetaReduceListPositions[args___, opts : OptionsPattern[]] := Block[{lambdas, positions},
	positions = First[Reap[lambdas = BetaReduceList[args, FilterRules[{opts}, Options[BetaReduceList]]], "Positions"][[2]], {}];
	{lambdas, positions}
]

Options[BetaReduceSizes] = Join[{"Function" -> LeafCount}, Options[BetaReduce]]

BetaReduceSizes[expr_, n : _Integer | Infinity | UpTo[_Integer | Infinity] : Infinity, m : _Integer | Infinity : 1, opts : OptionsPattern[]] := Block[{
	subOpts = Sequence @@ FilterRules[{opts}, Options[BetaReducePositions]],
	f = OptionValue["Function"],
	limit = Replace[n, _[x_] :> x],
	fixPointQ = MatchQ[n, _UpTo],
	lambda = Sow[expr, "Lambda"],
	sizes = {}, k
},
	For[k = 0, k < limit, k++,
		AppendTo[sizes, f[lambda]];
		pos = Sow[BetaReducePositions[lambda, m, subOpts], "Positions"];
		If[fixPointQ && pos === {}, Break[]];
		lambda = Sow[MapAt[BetaSubstitute, lambda, pos], "Lambda"];
	];
	{lambda, sizes}
]


LambdaLifetime[expr_, maxsteps_Integer : 50] :=
	If[# >= maxsteps, -Infinity, #] &[Length[Last[BetaReduceSizesCompiled[expr, UpTo[maxsteps]]]]]

LambdaLifetime[expr_, maxsteps_Integer : 50, opts : OptionsPattern[TreePosition]] :=
	If[# >= maxsteps, -Infinity, #] &[Length[Last[BetaReduceSizes[expr, UpTo[maxsteps], opts]]]]


(* substitute all variables *)
LambdaSubstitute[expr_, vars_Association : <||>, offset_Integer : 0] :=
	If[ Length[vars] == 0,
		expr
		,
		Replace[expr, {
			(lambda : $LambdaPattern)[body_] :> lambda[LambdaSubstitute[body, vars, offset + 1]],
			(lambda : $LambdaPattern)[body_][arg_] :> lambda[LambdaSubstitute[body, vars, offset + 1]][LambdaSubstitute[arg, vars, offset]],
			var_Integer | Interpretation[var_Integer, _] :> Lookup[vars, var - offset, var, offsetFree[#, offset] &],
			(v : Style[var_Integer, style___]) | Interpretation[v : Style[var_Integer, style___], _] :> Lookup[vars, var - offset, v, offsetFree[#, offset] &],
			f_[x_] :> LambdaSubstitute[f, vars, offset][LambdaSubstitute[x, vars, offset]]
		}]
	]

(* TODO: non-recursive version *)
(* this tries to delay substitution *)

Options[EvalLambda] = {"EvalBody" -> True}
EvalLambda[expr_, vars_Association : <||>, n : _Integer | Infinity : Infinity, k_Integer : 0, opts : OptionsPattern[]] :=
If[ k >= n,
	With[{subst = LambdaSubstitute[expr, vars]}, Sow[k]; subst]
	,
	Replace[
		expr,
		{
			(* beta reductions uses argument->head order *)
			(lambda : $LambdaPattern[body_])[arg_] :> With[{evalArg = Reap[EvalLambda[arg, vars, n, k, opts]]},
				{l = If[! FreeQ[evalArg, _TerminatedEvaluation], Return[evalArg, With], evalArg[[2, 1, 1]]]},
				If[ l >= n,
					With[{subst = LambdaSubstitute[lambda, vars][evalArg[[1]]]}, Sow[If[subst === lambda, l, l + 1]]; subst]
					,
					offsetFree[EvalLambda[body, offsetFree[#, 1] & /@ <|1 -> evalArg[[1]], KeyMap[# + 1 &, vars]|>, n, l + 1, opts], -1]
				]
			],
			If[TrueQ[OptionValue["EvalBody"]], (lambda : $LambdaPattern)[body_] :> lambda[EvalLambda[body, offsetFree[#, 1] & /@ KeyMap[# + 1 &, vars], n, k]], Nothing],
			(* standard head->argument evaluation order *)
			(head : Except[$LambdaPattern])[arg_] :> With[
				{evalHead = Reap[EvalLambda[head, vars, n, k, opts]]},
				{evalArg = If[! FreeQ[evalHead, _TerminatedEvaluation], Return[evalHead, With], Reap[EvalLambda[arg, vars, n, evalHead[[2, 1, 1]], opts]]]},
				{l = If[! FreeQ[evalArg, _TerminatedEvaluation], Return[evalArg, With], evalArg[[2, 1, 1]]]},
				If[ l >= n || evalHead[[1]][evalArg[[1]]] === head[arg],
					Sow[l]; evalHead[[1]][evalArg[[1]]]
					,
					EvalLambda[evalHead[[1]][evalArg[[1]]], n, l, opts]
				]
			]
			,
			_ :> With[{subst = LambdaSubstitute[expr, vars]}, Sow[k]; subst]
		}
	]
]


EtaReduce[expr_] := expr //. $Lambda[(f : Except[_Integer])[1]] :> offsetFree[f, -1]
EtaReduce[expr_, n_Integer] := If[ n <= 0, expr,
	With[{pos = FirstPosition[expr, $Lambda[Except[_Integer][1]]]}, If[MissingQ[pos], expr, EtaReduce[ReplaceAt[expr, $Lambda[f_[1]] :> offsetFree[f, -1], pos], n - 1]]]
]


Options[BetaReducePath] = Options[BetaReduceSizes]

BetaReducePath[args__] := Flatten[Reap[BetaReduceSizes[args], "Positions"][[2]], 2]


Options[LambdaPathEvents] = Options[BetaReducePath]

LambdaPathEvents[lambda_, args___] := With[{positions = BetaReducePath[lambda, args]},
	If[	positions === {},
		{},
		Block[{taggedlambda = TagLambda[lambda], lambdaPath},
			lambdaPath = FoldList[MapAt[BetaSubstitute, #1, {#2}] &, taggedlambda, positions];
			MapThread[Append[DirectedEdge @@ #1, #3 -> #2] &, {Partition[lambdaPath, 2, 1], positions, Range[Length[positions]]}]
		]
	]
]



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
	includeArgsQ = TrueQ[OptionValue["IncludeArguments"]],
	timeConstraint = OptionValue[TimeConstraint]
},
	Confirm @ TimeConstrained[
		term = BetaReduce[UntagLambda[lambda], n, m, lambdaOptions];
		Until[BetaNormalQ[term[\[FormalX]]],
			AppendTo[args, AlphabetString[j++]];
			term = BetaReduce[term[args[[-1]]], n, m, lambdaOptions];
		],
		timeConstraint
	];

	term = term /. l : $LambdaHead[_] :> Confirm @ FindMinimalLambdaCombinator[l, maxSize, n, m, scheme, j, opts];
	If[FreeQ[term, Alternatives @@ args], Sow[args, "Arguments"]; Return[ResourceFunction["CombinatorFixedPoint"][LambdaCombinator[lambda], scheme, combinatorOptions]]];
	
	Block[{step, combs, total, found = Missing["NotFound", term], parallelQ = TrueQ[OptionValue["Parallel"]]},
		If[ parallelQ,
			SetSharedVariable[step, Unevaluated[found], Unevaluated[args], Unevaluated[term], Unevaluated[combinatorOptions], Unevaluated[timeConstraint], Unevaluated[includeArgsQ]]
		];
		Do[
			If[! MissingQ[found], Break[]];
			step = 0;
			combs = ResourceFunction["EnumerateCombinators"][k];
			total = Length[combs];
			Progress`EvaluateWithProgress[
				If[k > 5 && parallelQ, ParallelDo, Do][
					CheckAbort[
						If[! MissingQ[found], Break[]];
						step++;
						With[{combTerm = Fold[Construct, comb, args]},
							If[
								term === TimeConstrained[
									ResourceFunction["CombinatorFixedPoint"][
										combTerm,
										scheme,
										combinatorOptions
									],
									timeConstraint
								]
								,
								found = If[includeArgsQ, combTerm, comb]
							]
						],
						found = $Aborted
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
			
		Sow[args, "Arguments"];
		found
	]
]


Options[FindMinimalCombinatorLambda] = Options[FindMinimalLambdaCombinator]

FindMinimalCombinatorLambda[comb_,
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
	includeArgsQ = TrueQ[OptionValue["IncludeArguments"]],
	timeConstraint = OptionValue[TimeConstraint]
},
	Confirm @ TimeConstrained[
		term = ResourceFunction["CombinatorFixedPoint"][comb, scheme, combinatorOptions];
		Until[! MatchQ[term, CombinatorK | CombinatorS | (CombinatorK | CombinatorS)[_] | CombinatorS[_][_]],
			With[{argCount = If[MatchQ[term, CombinatorS[_]], 2, 1]},
				Do[AppendTo[args, AlphabetString[j++]], argCount];
				term = ResourceFunction["CombinatorFixedPoint"][Fold[Construct, term, args[[- argCount ;;]]], scheme, combinatorOptions]
			];
		],
		timeConstraint
	];
	term = term /. c : CombinatorS[_][_] | (CombinatorK | CombinatorS)[_] | CombinatorK | CombinatorS :> Confirm @ FindMinimalCombinatorLambda[c, maxSize, n, m, scheme, j, opts];
	If[FreeQ[term, Alternatives @@ args], Sow[args, "Arguments"]; Return[BetaReduce[CombinatorLambda[comb], n, m, lambdaOptions]]];
	Block[{step, lambdas, total, found = Missing["NotFound", term], parallelQ = TrueQ[OptionValue["Parallel"]]},
		If[ parallelQ,
			SetSharedVariable[step, Unevaluated[found], Unevaluated[args], Unevaluated[term], Unevaluated[lambdaOptions], Unevaluated[timeConstraint], Unevaluated[includeArgsQ]]
		];
		Do[
			If[! MissingQ[found], Break[]];
			step = 0;
			lambdas = EnumerateSizeLambdas[k];
			total = Length[lambdas];
			Progress`EvaluateWithProgress[
				If[k > 5 && parallelQ, ParallelDo, Do][
					CheckAbort[
						If[! MissingQ[found], Break[]];
						step++;
						With[{lambdaTerm = Fold[Construct, lambda, args]},
							If[
								term === TimeConstrained[
									BetaReduce[
										lambdaTerm,
										n, m,
										lambdaOptions
									],
									timeConstraint
								]
								,
								found = If[includeArgsQ, lambdaTerm, lambda]
							]
						],
						found = $Aborted
					]
					,
					{lambda, lambdas}
				]
				,
				<|"Text" -> StringTemplate["Searching size-`` lambdas"][k], "Percentage" :> step / total, "ElapsedTime" -> Automatic, "RemainingTime" -> Automatic|>
			];
			,
			{k, 2, Replace[maxSize, Automatic :> LeafCount[CombinatorLambda[comb]]]}
		];
			
		Sow[args, "Arguments"];
		found
	]
]


End[]

EndPackage[]
