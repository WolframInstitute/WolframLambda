(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`Lambda`"];


(* ::Text:: *)
(*Declare your public symbols here:*)

$Lambda;
ClosedLambdaQ;
RandomLambda;
RandomSizeLambda;
EnumerateLambdas;
EnumerateAffineLambdas;
EnumerateLinearLambdas;
AffineLambdaQ;
LinearLambdaQ;
EnumerateSizeLambdas;
LambdaSize;

LambdaSubstitute;
EvalLambda;
LambdaFreeVariables;

ApplicativePosition;
BetaSubstitute;
BetaReducePositions;
BetaNormalQ;
BetaReductions;
BetaPositionReductions;
BetaReduce;
BetaReduceList;
BetaReduceSizes;
EtaReduce;

LambdaCombinator;
CombinatorLambda;

LambdaApplication;
LambdaRightApplication;
LambdaVariableForm;
LambdaBrackets;
LambdaString;

LambdaFunction;
FunctionLambda;
LambdaTree;
LambdaMinimalTree;
LambdaGraph;
BetaReduceStepPlot;

LambdaConvert;
ParseLambda;
LambdaBLC;
BLCLambda;

TagLambda;
UntagLambda;
LambdaDepths;
LambdaPositions;
ColorizeLambda;
LambdaSmiles;
LambdaDiagram;

ChurchNumeral;
FromChurchNumeral;
ChurchNumeralQ;
$LambdaBusyBeavers;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)
If[! ValueQ[$Lambda],
	$Lambda = \[FormalLambda];
]

$LambdaPattern = $Lambda | Interpretation["\[Lambda]", _]


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

AffineLambdaQ[lambda_] := AllTrue[LambdaPositions[lambda], Length[#] <= 1 &]

LinearLambdaQ[lambda_] := AllTrue[LambdaPositions[lambda], Length[#] == 1 &]


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


(* From Max Niederman *)

(* offset only the free variables in a lambda term *)
offsetFree[expr_, 0, ___] := expr
offsetFree[(lambda : $LambdaPattern)[body_], offset_, depth_ : 0] := lambda[offsetFree[body, offset, depth + 1]]
offsetFree[v : Interpretation[var_Integer, _], offset_, depth_ : 0] := ReplacePart[v, 1 -> offsetFree[var, offset, depth]]
offsetFree[fun_[x_], offset_, depth_ : 0] := offsetFree[fun, offset, depth][offsetFree[x, offset, depth]]
offsetFree[var_Integer, offset_, depth_ : 0] := If[var > depth, var + offset, var]
offsetFree[expr_, offset_, depth_ : 0] := expr


$betaSubstituteCounter

(* perform a substitution of an argument into the body of a lambda, and also decrement the free parameters by one *)
betaSubstitute[(lambda : $LambdaPattern)[body_], arg_, paramIdx_ : 1] := lambda[betaSubstitute[body, arg, paramIdx + 1]]
betaSubstitute[v : Interpretation[var_Integer, tag_], arg_, paramIdx_ : 1] := Block[{index = <||>},
	Which[
		var < paramIdx, v,
		var == paramIdx, offsetFree[arg, paramIdx - 1] /. {
			Interpretation["\[Lambda]", subTag_][body_] :> With[{i = Lookup[$betaSubstituteCounter, subTag, $betaSubstituteCounter[subTag] = 0]},
				$betaSubstituteCounter[subTag]++;
				Interpretation["\[Lambda]", tag -> Subscript[subTag, i]][body /. Interpretation[e_, subTag] :> Interpretation[e, tag -> Subscript[subTag, i]]]
			]
		},
		var > paramIdx, ReplacePart[v, 1 -> var - 1]
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


OuterPosition[expr_, patt_, n : _Integer | Infinity : Infinity, pos_List : {}] := Block[{k = n, curPos, curPositions, positions},
	If[ k < 1, Return[{}]];
	If[ MatchQ[Unevaluated[expr], patt],
		positions = {pos};
		k--
		,
		positions = {}
	];
	If[ k > 0 && ! AtomQ[Unevaluated[expr]],
		Do[
			curPos = Append[pos, i];
			curPositions = With[{subExpr = Extract[Unevaluated[expr], i, Unevaluated]}, OuterPosition[subExpr, patt, k, curPos]];
			positions = Join[positions, curPositions];
			k -= Length[curPositions];
			If[k < 1, Break[]];
			,
			{i, Range[0, Length[Unevaluated[expr]]]}
		]
	];
	positions
]

ApplicativePosition[expr_, n : _Integer | Infinity : Infinity, pos_List : {}] := Block[{k = n, curPos, curPositions, positions = {}},
	If[ k < 1, Return[{}]];
	If[ MatchQ[expr, $LambdaPattern[_][_]],
		positions = ApplicativePosition[expr[[1]], n, Append[pos, 1]];
		k -= Length[positions];
		(k -= Length[#]; positions = Join[positions, #]) & @ ApplicativePosition[expr[[0]], k, Append[pos, 0]];
		If[ k > 0,
			positions = Append[positions, pos],
			k--
		]
		,
		If[ k > 0 && ! AtomQ[expr],
			Do[
				curPos = Append[pos, i];
				curPositions = With[{subExpr = Extract[expr, i]}, ApplicativePosition[subExpr, k, curPos]];
				positions = Join[positions, curPositions];
				k -= Length[curPositions];
				If[k < 1, Break[]];
				,
				{i, Range[0, Length[Unevaluated[expr]]]}
			]
		];
	];

	positions
]

Options[BetaReducePositions] = Options[TreePosition]

BetaReducePositions[expr_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := With[{order = OptionValue[TreeTraversalOrder]},
	Switch[order,
		"Applicative",
		ApplicativePosition[expr, n],
		Automatic | "Normal" | "Outermost" | "BreadthFirst",
		OuterPosition[expr, $LambdaPattern[_][_], n],
		"Random",
		RandomSample[Position[expr, $LambdaPattern[_][_], Heads -> True], UpTo[n]],
		_,
		TreePosition[ExpressionTree[expr, "Subexpressions", Heads -> True], $LambdaPattern[_][_], All, n, TreeTraversalOrder -> order] - 1
	]
]


BetaNormalQ[expr_] := FreeQ[expr, $LambdaPattern[_][_]]


Options[BetaReductions] = Options[BetaPositionReductions] = Options[BetaReducePositions]

BetaReductions[expr_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] :=
	MapAt[BetaSubstitute, expr, {#}] & /@ BetaReducePositions[expr, n, opts]

BetaPositionReductions[expr_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := 
	AssociationMap[MapAt[BetaSubstitute, expr, {#}] &, BetaReducePositions[expr, n, opts]]


Options[BetaReduce] = Options[BetaReducePositions]

BetaReduce[expr_, n : _Integer | Infinity : Infinity, m : _Integer | Infinity : 1, opts : OptionsPattern[]] := 
 	FixedPoint[MapAt[BetaSubstitute, #, Sow[BetaReducePositions[#, m, opts], "Positions"]] &, expr, n]

Options[BetaReduceList] = Options[BetaReduce]

BetaReduceList[expr_, n : _Integer | Infinity : Infinity, m : _Integer | Infinity : 1, opts : OptionsPattern[]] :=
	FixedPointList[BetaReduce[#, 1, m, opts] &, expr, n]

Options[BetaReduceSizes] = Join[{"Function" -> LeafCount}, Options[BetaReduce]]

BetaReduceSizes[expr_, n : _Integer | Infinity | UpTo[_Integer | Infinity] : Infinity, opts : OptionsPattern[]] := Block[{
	subOpts = Sequence @@ FilterRules[{opts}, Options[BetaReducePositions]],
	f = OptionValue["Function"],
	limit = Replace[n, _[x_] :> x],
	fixPointQ = MatchQ[n, _UpTo],
	lambda = expr,
	sizes = {}, k
},
	For[k = 0, k < limit, k++,
		AppendTo[sizes, f[lambda]];
		pos = BetaReducePositions[lambda, 1, subOpts];
		If[fixPointQ && pos === {}, Break[]];
		lambda = MapAt[BetaSubstitute, lambda, pos];
	];
	{lambda, sizes}
]

(* substitute all variables *)
LambdaSubstitute[expr_, vars_Association : <||>, offset_Integer : 0] :=
	If[ Length[vars] == 0,
		expr
		,
		Replace[expr, {
			(lambda : $LambdaPattern)[body_] :> lambda[LambdaSubstitute[body, vars, offset + 1]],
			(lambda : $LambdaPattern)[body_][arg_] :> lambda[LambdaSubstitute[body, vars, offset + 1]][LambdaSubstitute[arg, vars, offset]],
			var_Integer | Interpretation[var_Integer, _] :> Lookup[vars, var - offset, var, offsetFree[#, offset] &],
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


LambdaCombinator[expr_, ruleSpec_String : "SK"] := Block[{T, rules = Characters[ruleSpec]},
	T[x_] := x;
	T[(f : Except[Interpretation["\[Lambda]", _]])[x_]] := T[f][T[x]];
	T[Interpretation["\[Lambda]", tag_][x_]] /; FreeQ[x, tag] := CombinatorK[T[x]];
	T[(l : Interpretation["\[Lambda]", tag_])[y : Interpretation["\[Lambda]", _][x_]]] /; ! FreeQ[x, tag] := T[l[T[y]]];

	T[Interpretation["\[Lambda]", tag_][Interpretation[_, tag_]]] := Evaluate[
		If[ MemberQ[rules, "I"],
			CombinatorI,
			CombinatorS[CombinatorK][CombinatorK]
		]
	];
	If[ MemberQ[rules, "\[Eta]"],
		T[Interpretation["\[Lambda]", tag_][f_[Interpretation[_, tag_]]]] /; FreeQ[f, tag] := T[f]
	];
	If[ MemberQ[rules, "C"],
		T[(l : Interpretation["\[Lambda]", tag_])[(f : Except[Interpretation["\[Lambda]", _]])[x_]]] /; ! FreeQ[f, tag] && FreeQ[x, tag] := CombinatorC[T[l[f]]][T[x]]
	];
	If[ MemberQ[rules, "B"],
		T[(l : Interpretation["\[Lambda]", tag_])[(f : Except[Interpretation["\[Lambda]", _]])[x_]]] /; FreeQ[f, tag] && ! FreeQ[x, tag] := CombinatorB[T[f]][T[l[x]]]
	];
	T[(l : Interpretation["\[Lambda]", tag_])[(f : Except[Interpretation["\[Lambda]", _]])[x_]]] /; ! FreeQ[f, tag] || ! FreeQ[x, tag] := CombinatorS[T[l[f]]][T[l[x]]];

	T[TagLambda[expr]]
]

CombinatorLambda[expr_] := expr //. {
	CombinatorI -> $Lambda[1],
	CombinatorK -> $Lambda[$Lambda[2]],
	CombinatorS -> $Lambda[$Lambda[$Lambda[3[1][2[1]]]]],
	CombinatorC -> $Lambda[$Lambda[$Lambda[3[1][2]]]],
	CombinatorB -> $Lambda[$Lambda[$Lambda[3[2[1]]]]]
}


LambdaFreeVariables[expr_, pos_List : {}, depth_Integer : 0] := Replace[expr, {
	$LambdaPattern[body_][arg_] :> Join[LambdaFreeVariables[body, Join[pos, {0, 1}], depth + 1], LambdaFreeVariables[arg, Append[pos, 1], depth]],
	$LambdaPattern[body_] :> LambdaFreeVariables[body, Append[pos, 1], depth + 1],
	f_[x_] :> Join[LambdaFreeVariables[f, Append[pos, 0], depth], LambdaFreeVariables[x, Append[pos, 1], depth]],
	var_Integer :> If[var > depth, {{depth, pos, var}}, {}],
	v : Interpretation[var_Integer, _] :> If[var > depth, {{depth, pos, v}}, {}],
	x_ :> {{depth, pos, x}}
}
]

ClosedLambdaQ[lambda_] := LambdaFreeVariables[lambda] === {}


TagLambda[expr_, lambdas_Association] := With[{
	nextLambdas = KeyMap[# + 1 &] @ lambdas
},
	expr /. {
		$Lambda[body_][y_] :> With[{newLambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]][TagLambda[y, lambdas]]],
		$Lambda[body_] :> With[{newLambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]]],
		term_Integer :> Interpretation[term, Evaluate @ If[KeyExistsQ[lambdas, term], lambdas[term][[2]], Max[Keys[lambdas]]]]
	}
]
TagLambda[$Lambda[body_], "Unique"] := With[{lambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, lambda[TagLambda[body, <|1 -> lambda|>]]]

SetAttributes[AlphabetString, Listable]
AlphabetString[0] = ""
AlphabetString[n_Integer ? NonNegative] := Block[{q, r},
	{q, r} = QuotientRemainder[n, 26];
	If[r == 0, (q -= 1; r = 26)];
	AlphabetString[q] <> FromLetterNumber[r]
]

TagLambda[expr_, symbols : _List | Automatic | "Alphabet"] := Block[{lambda = TagLambda[expr, "Unique"], vars},
	vars = Cases[lambda, Interpretation["\[Lambda]", tag_] :> tag, All, Heads -> True];
	lambda /. MapThread[
		With[{sym = Unevaluated @@ #2}, #1 :> sym] &,
		{vars, PadRight[Replace[symbols, "Alphabet" | Automatic -> {}], Length[vars], MakeExpression /@ AlphabetString[Range[Length[vars]]]]}
	]
]

TagLambda[expr_, form_String : "Alphabet"] := expr /. lambda : $Lambda[_] :> TagLambda[lambda, form]

ResourceFunction["AddCodeCompletion"]["TagLambda"][None, {"Alphabet", "Unique"}]


UntagLambda[expr_] := expr /. {Interpretation["\[Lambda]", _] :> $Lambda, Interpretation[x_, _] :> x,  l : $Lambda[_, _] :> FunctionLambda[l]}


LambdaFunction[expr_, head_ : Identity] := head @@ (Hold[Evaluate @ TagLambda[expr]] //. {Interpretation["\[Lambda]", x_][body_] :> Function[x, body], Interpretation[_Integer, x_] :> x})


FunctionLambda[expr_, vars_Association : <||>] := Replace[Unevaluated[expr], {
	($Lambda | Function)[var_, body_][x_] :> Interpretation["\[Lambda]", var][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]][FunctionLambda[Unevaluated[x], vars]],
	($Lambda | Function)[var_, body_] :> Interpretation["\[Lambda]", var][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]],
	f_[x_] :> FunctionLambda[Unevaluated[f], vars][FunctionLambda[Unevaluated[x], vars]],
	var_Symbol :> Interpretation[Evaluate[Replace[var, vars]], var]
}]


$LambdaTreeColors = <|
	"Lambda" -> Hue[0.8174603174603176, 0.20999999999999996`, 1.], 
   	"BrighterLambda" -> Hue[0.833, 0.622, 0.9570000000000001], 
   	"DebruijnIndex" -> Hue[0.576923076923077, 0.13, 1., 1.], 
   	"DebruijnIndexBorder" -> RGBColor[0.276768, 0.66747216, 0.72075, 1], 
   	"BrighterDebruijnIndex" -> Hue[0.52, 0.616, 0.961], 
   	"Application" -> GrayLevel[0.9, 1], 
   	"BrighterApplication" -> Hue[0.305, 0.795, 0.927], 
   	"BlackLambda" -> $Black,
   	"WhiteLambda" -> $White,
	"Edges" -> GrayLevel[0.8, 1], 
   	"ApplicationBorder" -> GrayLevel[0.6, 1.], 
   	"VariableArgument" -> RGBColor[1., 0.88, 0.77], 
   	"BrighterVariableArgument" -> RGBColor[1., 0.71, 0.06],
	"Variable" -> $Green,
	"Labels" -> $White
|>

$DefaultLambdaTreeColorRules = Join[
	{
		"Lambda" -> Directive[$LambdaTreeColors["Lambda"], EdgeForm[$LambdaTreeColors["BrighterLambda"]]],
		"Application" -> Directive[$LambdaTreeColors["Application"], EdgeForm[$LambdaTreeColors["ApplicationBorder"]]],
		"Index" -> Directive[$LambdaTreeColors["DebruijnIndex"], EdgeForm[$LambdaTreeColors["DebruijnIndexBorder"]]],
		"Variable" -> Directive[$LambdaTreeColors["VariableArgument"], EdgeForm[Darker[$LambdaTreeColors["BrighterVariableArgument"], .1]]]
	}
	,
	Normal[$LambdaTreeColors]
]

Options[LambdaTree] = Join[{
	"ApplicationLabel" -> None, "VariableLabels" -> False,
	ColorFunction -> $DefaultColorFunction,
	ColorRules -> $DefaultLambdaTreeColorRules,
	PlotTheme -> Automatic
},
	Options[Tree]
]

lambdaTree[(l : $LambdaPattern)[body_], opts___] := Tree[l, {lambdaTree[body]}, opts]
lambdaTree[f_[x_], opts___] := Tree[Application, {lambdaTree[f], lambdaTree[x]}, opts]
lambdaTree[expr_, opts___] := Tree[expr, None, opts]


LambdaTree[lambda_, opts : OptionsPattern[]] := With[{
	taggedLambda = TagLambda[lambda],
	theme = OptionValue[PlotTheme],
	colorRules = Join[Cases[Flatten[{OptionValue[ColorRules]}], _Rule | _RuleDelayed], $DefaultLambdaTreeColorRules],
	appLabel = OptionValue["ApplicationLabel"],
	variablesQ = TrueQ[OptionValue["VariableLabels"]]
},
	
	Block[{colors = {}, lambdaColor, appColor, leaveColor},
		lambdaColor = Replace["Lambda", colorRules];
		appColor = Replace["Application", colorRules];
		leaveColor = Replace[If[variablesQ, "Variable", "Index"], colorRules];
		lambdaTree[
			ColorizeLambda[taggedLambda, OptionValue[ColorFunction]] /.
				Style[node : Interpretation[e_, tag_], style__] :>
					(If[e === "\[Lambda]", AppendTo[colors, TreeCases[Interpretation[_, tag]] -> Directive[style]]]; node)
			,
			FilterRules[{opts}, Options[Tree]],
			ParentEdgeStyle -> {All -> Replace["Edges", colorRules]},
			TreeElementLabelStyle -> All -> Replace["BlackLambda", colorRules],
			TreeElementStyle -> Switch[theme,
				"Colored" | "MinimalColored",
					Append[colors, TreeCases[Application] -> appColor],
				_,
					{
						TreeCases[$LambdaPattern] -> Replace["Lambda", colorRules],
						"Leaves" -> Replace[If[variablesQ, "Variable", "Index"], colorRules],
						TreeCases[Application] -> appColor
					}
			],
  			TreeElementSize -> Switch[theme,
				"Minimal" | "MinimalColored",
					All -> .2,
				_,
					Automatic
			],
			TreeElementShape -> Switch[theme,
				"Minimal",
					MapThread[
						#1 -> Graphics[#2, ImageSize -> 6] &, 
						{
							{TreeCases[Application], "NonLeaves", "Leaves"},
							{{appColor, Disk[{0, 0}]}, {lambdaColor, Rectangle[{0, 0}, {0.75, 1}]}, {leaveColor, Rectangle[{0, 0}, {0.75, 1}]}}
						}
					]
				,
				"MinimalColored", {
					TreeCases[Application] -> Graphics[{appColor, Disk[{0, 0}]}, ImageSize -> 6],
					Splice @ MapAt[Graphics[{#[[2]], EdgeForm[Darker[#[[2]], .1]], Rectangle[{0, 0}, {0.75, 1}]}, ImageSize -> 6] &, colors, {All, 2}]
				}
				,
				_,
					Automatic
			],
			TreeElementLabel -> Switch[theme,
				"Minimal" | "MinimalColored",
					All -> None,
				_,
					TreeCases[Application] -> appLabel
			],
			TreeElementLabelFunction -> Switch[theme,
				"Minimal" | "MinimalColored",
					All -> None,
				_, {
					"Leaves" -> If[variablesQ, Last, Identity],
					TreeCases[Application] -> Automatic,
					"NonLeaves" -> If[variablesQ, Function[Subscript["\[Lambda]", Last[#]]], Function["\[Lambda]"]]
				}
			]
		]
]
]

LambdaMinimalTree[lambda_, opts___] := LambdaTree[lambda, opts, PlotTheme -> "Minimal", ImageSize -> {Automatic, UpTo[100]}]

LambdaGraph[lambda_, opts : OptionsPattern[]] := With[{tree = LambdaTree[TagLambda[UntagLambda[lambda], "Alphabet"], "VariableLabels" -> True]},
	VertexReplace[
		TreeGraph[tree]
		,
		{
			{Application, pos_} :> Interpretation["@", pos],
			{Interpretation["\[Lambda]", tag_], pos_} :> Interpretation[Subscript["\[Lambda]", tag], pos],
			{Interpretation[_, tag_], pos_} :> tag
		}
		,
		opts,
		GraphLayout -> "SymmetricLayeredEmbedding",
		VertexShapeFunction -> Function[
			Trees`$TreeVertexShapeFunction[
				#2,
				Directive[Trees`$TreeVertexColor, Trees`$TreeVertexFrameStyle],
				MatchQ[#2, Except[_Interpretation]]
			][##]
		],
		EdgeShapeFunction -> Trees`$TreeEdgeShapeFunction,
		EdgeStyle -> Trees`$TreeEdgeColor
	]
]


LambdaApplication[lambda_, ___] := lambda //. (f : Except[$LambdaPattern])[x_] :> Application[f, x]

LambdaVariableForm[lambda_, ___] := TagLambda[lambda] //. {(l : Interpretation["\[Lambda]", tag_])[arg_] :> $Lambda[tag, arg], Interpretation[_Integer, tag_]:> tag}

LambdaRightApplication[lambda_, sym_ : "@", ___] :=
	lambda //. (x : Except[$LambdaPattern | Row])[y_] :> Row[{x, sym, y}] //.
		Row[{prefix : Except[sym] ..., Row[{a__, sym, b__}], c__}] :> Row[{prefix, "(", a, sym, b, ")", c}]


LambdaBrackets[lambda_, ___] := RawBoxes[ToBoxes[LambdaApplication[lambda]] /. ToString[$Lambda] | "\[Application]" -> "\[InvisibleSpace]"]

LambdaString[lambda_, "Variables"] := TagLambda[lambda] //. {
   	Interpretation["\[Lambda]", var_][body_] :> StringTemplate["(\[Lambda]``.``)"][ToString[Unevaluated[var]], LambdaString[body, "Variables"]],
	Interpretation[_, var_] :> ToString[Unevaluated[var]],
	f_[x_] :> StringTemplate["(`` ``)"][LambdaString[f, "Variables"], LambdaString[x, "Variables"]]
}

LambdaString[lambda_, "Indices"] := UntagLambda[lambda] //. {
   	$Lambda[body_] :> StringTemplate["(\[Lambda] ``)"][LambdaString[body, "Indices"]],
	f_[x_] :> StringTemplate["(`` ``)"][LambdaString[f, "Indices"], LambdaString[x, "Indices"]]
}

LambdaString[lambda_, ___] := LambdaString[lambda, "Variables"]

ResourceFunction["AddCodeCompletion"]["LambdaString"][None, {"Variables", "Indices"}]


LambdaConvert[expr_, form_String : "Application", args___] := Switch[form,
	"Application",
	LambdaApplication[expr, args],
	"RightApplication",
	LambdaRightApplication[expr, args],
	"VariableForm" | "StandardForm",
	LambdaVariableForm[expr, args],
	"BracketParens",
	LambdaBrackets[expr, args],
	"Function",
	LambdaFunction[expr, args],
	"Combinator",
	LambdaCombinator[expr, args],
	"Tree",
	LambdaTree[expr, args],
	"Graph",
	LambdaGraph[expr, args],
	"String",
	LambdaString[expr, args],
	"BLC",
	LambdaBLC[expr, args],
	_,
	Missing[form]
]
ResourceFunction["AddCodeCompletion"]["LambdaConvert"][None, {"Application", "RightApplication", "VariableForm", "BracketParens", "Function", "Combinator", "Tree", "Graph", "String", "BLC"}]


BalancedParenthesesQ[str_] := FixedPoint[StringDelete["()"], StringDelete[str, Except["(" | ")"]]] === ""

ParseVariableLambda[str_String, vars_Association : <||>] := First @ StringCases[str, {
	WhitespaceCharacter ... ~~ "\[Lambda]" ~~ WhitespaceCharacter ... ~~ var : WordCharacter .. ~~ WhitespaceCharacter ... ~~ "." ~~ WhitespaceCharacter ... ~~ body__ :>
		Interpretation["\[Lambda]", var][ParseVariableLambda[body, <|vars + 1, var -> 1|>]],
	f__ ~~ WhitespaceCharacter ... ~~ x__ /; ! StringMatchQ[x, WhitespaceCharacter ..] &&
		! StringEndsQ[f, ("\[Lambda]" | ".") ~~ WhitespaceCharacter ...] && ! StringStartsQ[x, "."] && ! StringEndsQ[x, ("\[Lambda]" | ".") ~~ WhitespaceCharacter ...] &&
		BalancedParenthesesQ[f] && BalancedParenthesesQ[x] :> ParseVariableLambda[f, vars][ParseVariableLambda[x, vars]],
	"(" ~~ term__ ? BalancedParenthesesQ ~~ ")" :> ParseVariableLambda[term, vars],
	var : WordCharacter .. :> Interpretation[Evaluate[Replace[var, vars]], var]
}]

ParseIndexLambda[str_String] := First[StringCases[str, {
	WhitespaceCharacter ... ~~ "\[Lambda]" ~~ WhitespaceCharacter ... ~~ body__ ~~ WhitespaceCharacter ... :> $Lambda[ParseIndexLambda[body]],
	f__ ~~ WhitespaceCharacter .. ~~ x__ /; BalancedParenthesesQ[f] && BalancedParenthesesQ[x] :> ParseIndexLambda[f][ParseIndexLambda[x]],
	WhitespaceCharacter ... ~~ "(" ~~ term__ ? BalancedParenthesesQ ~~ ")" ~~ WhitespaceCharacter ... :> ParseIndexLambda[term],
	WhitespaceCharacter ... ~~ var : DigitCharacter .. ~~ WhitespaceCharacter ... :> Interpreter["Integer"][var]
}], StringTrim[str]]

ParseLambda[str_String, form_String : "Variables"] := Switch[form,
	"Variables",
	ParseVariableLambda[str],
	"Indices",
	ParseIndexLambda[str],
	_,
	Missing[form]
]

ResourceFunction["AddCodeCompletion"]["ParseLambda"][None, {"Variables", "Indices"}]


LambdaBLC[lambda_, ___] := lambda /. {
	$LambdaPattern[body_] :> {0, 0, Splice[LambdaBLC[body]]},
	f_[x_] :> {0, 1, Splice[LambdaBLC[f]], Splice[LambdaBLC[x]]},
	i_Integer :> Append[ConstantArray[1, i], 0]
}

blcLambda[bits : {___Integer}] :=
	Replace[bits, {
		{0, 0, body___} :> ({$Lambda[#1], #2} & @@ blcLambda[{body}]),
		{0, 1, fx___} :> (({f, xs} |-> ({f[#1], #2} & @@ blcLambda[xs])) @@ blcLambda[{fx}]),
		{var : (1 ..), 0, rest___} :> {Length[{var}], {rest}},
		{} -> {None, {}},
		_ -> {Missing["UnrecognizedBits", bits], {}}
	}]

BLCLambda[bits : {(0 | 1) ...}] := With[{lambda = blcLambda[bits]}, If[lambda[[2]] === {}, lambda[[1]], Missing @@ lambda]]

BLCLambda[ba_ByteArray] := BLCLambda[Catenate[Reverse /@ IntegerDigits[Normal[ba], 2, 8]]]

BLCLambda[n_Integer] := BLCLambda[ByteArray[{n}]]

BLCLambda[s_String] := BLCLambda[StringToByteArray[s]]

BLCLambda[ds_DataStructure] /; DataStructureQ[ds, "BitVector"] := BLCLambda[Boole[Normal[ds]]]

BLCLambda[expr_] := BLCLambda[BinarySerialize[expr]]

$DefaultColorFunction = Function[Darker[ColorData[96][#], .1]]

ColorizeTaggedLambda[lambda_, colorFunction_ : $DefaultColorFunction] := With[{lambdas = Cases[lambda, Interpretation["\[Lambda]", x_], All, Heads -> True]},
	lambda /. MapThread[x : #1 | ReplacePart[#1, 1 -> _Integer] :> Style[x, Bold, #2] &, {lambdas, colorFunction /@ Range[Length[lambdas]]}]
]


ColorizeLambda[expr_, args___] := ColorizeTaggedLambda[TagLambda[expr], args]


LambdaRow[Interpretation["\[Lambda]", tag_][body_], depth_ : 0] := {{$Lambda[HoldForm[tag]] -> depth, Splice[LambdaRow[body, depth + 1]]}}
LambdaRow[Interpretation[i_Integer, tag_], ___] := {i -> HoldForm[tag]}
LambdaRow[(f : Except[Interpretation["\[Lambda]", _]])[(g : Except[Interpretation["\[Lambda]", _]])[x_]], depth_ : 0] := Append[LambdaRow[f, depth], LambdaRow[g[x], depth]]
LambdaRow[f_[x_], depth_ : 0] := Join[LambdaRow[f, depth], LambdaRow[x, depth]]
LambdaRow[x_, ___] := {x}

Options[LambdaSmiles] = Join[
	{"Height" -> 3, "Spacing" -> 1, "StandardForm" -> False, "Arguments" -> False, "Arrow" -> False, ColorFunction -> $DefaultColorFunction},
	Options[Style], Options[Graphics]
];
LambdaSmiles[lambda_, opts : OptionsPattern[]] := Block[{
	row = LambdaRow[TagLambda[lambda]],
	lambdaPos, varPos, argPos, lambdas, maxDepth, vars, args, colors, arrows,
	height = OptionValue["Height"], spacing = OptionValue["Spacing"],
	argQ = TrueQ[OptionValue["Arguments"]],
	colorFunction = OptionValue[ColorFunction],
	styleOpts = FilterRules[{opts}, Options[Style]]
},
	row = FixedPoint[
		Replace[#, xs_List :> Splice[
				If[
					TrueQ[OptionValue["StandardForm"]],
					If[ argQ,
						If[Length[xs] == 1, {First[xs]}, {First[xs], "[", Replace[First[xs], {($Lambda[tag_] -> _) :> Splice[{"Arg"[tag] -> 0, ","}], _ -> Nothing}], Rest[xs], "]"}],
						If[Length[xs] == 1, {First[xs]}, {First[xs], "[", Rest[xs], "]"}]
					],
					If[ argQ,
						If[Length[xs] == 1, {"(", First[xs], ")"}, {First[xs], "(", Replace[First[xs], {($Lambda[tag_] -> _) :> Splice[{"Arg"[tag] -> 0, "."}], _ -> Nothing}], Splice[Rest[xs]], ")"}],
						{"(", Splice[xs], ")"}
					]
				]
			],
			1
		] &,
		row
	];
	lambdaPos = Position[row, _$Lambda -> _, {1}, Heads -> False];
	varPos = Position[row, _Integer -> _, {1}, Heads -> False];
	argPos = Position[row, "Arg"[_] -> _, {1}, Heads -> False];
	lambdas = AssociationThread[#[[All, 1, 1]], Thread[First /@ lambdaPos -> #[[All, 2]]]] & @ Extract[row, lambdaPos];
	args = AssociationThread[#[[All, 1, 1]], Thread[First /@ argPos -> #[[All, 2]]]] & @ Extract[row, argPos];
	vars = Extract[row, varPos];
	colors = Association @ MapIndexed[#1[[1, 1]] -> colorFunction[#2[[1]]] &, Extract[row, lambdaPos]];
	row = row //
		MapAt[Style["\[Lambda]", Lookup[colors, #[[1, 1]], $Black]] &, lambdaPos] //
		MapAt[Style[#[[If[argQ, 2, 1]]], Lookup[colors, #[[2]], $Black]] &, varPos] //
		MapAt[Style[#[[1, 1]], Lookup[colors, #[[1, 1]], $Black]] &, argPos];
	
	arrows = MapThread[
		With[{dh = height * Ceiling[#1[[1]] / 2], sign = (-1) ^ Boole[EvenQ[#1[[1]]]], h = lambdas[#1[[2]]], l = lambdas[#1[[2]]]},
			If[	MissingQ[l] || MissingQ[h],
				Nothing,
				{
					colors[#1[[2]]],
					Arrowheads[Replace[OptionValue["Arrow"], {False | None -> 0, True | Automatic -> Small}]],
					Arrow[Threaded[{spacing, sign}] * {{#2, 1}, {#2, 1 + dh / (l[[2]] + 1)}, {h[[1]], 1 + dh / (l[[2]] + 1)}, {h[[1]], 1}}]
				}
			]
		] &,
		{vars, First /@ varPos}
	];
	Graphics[{
		MapIndexed[Inset[Style[#1, styleOpts, FontSize -> 16], {spacing * #2[[1]], 0}] &, row],
		arrows
	},
		FilterRules[{opts}, Options[Graphics]]
	]
]

{$Black, $White, $Red, $Green, $Blue, $Yellow, $Gray} = If[$VersionNumber >= 14.3,
	{LightDarkSwitched[Black, White], LightDarkSwitched[White, Black], StandardRed, StandardGreen, StandardBlue, StandardYellow, StandardGray},
	{White, Black, Red, Green, Blue, LightYellow, Gray}
]


$LambdaDiagramColorRules = {
   	"Lambda" -> Directive[EdgeForm[Darker[$LambdaTreeColors["BrighterLambda"]]], $LambdaTreeColors["BrighterLambda"]],
   	"LambdaApplication" -> Darker[$LambdaTreeColors["Application"], .1],
   	"Application" -> Darker[$LambdaTreeColors["Application"]],
   	"Term" -> $Gray,
   	"Variable" | "FreeVariable" | "Constant" -> $LambdaTreeColors["BrighterVariableArgument"],
   	_ -> Opacity[1]
}

Options[LambdaDiagram] = Join[{
	"Dynamic" -> False, "Extend" -> True, "Pad" -> True, "Dots" -> All, "Thick" -> False,
	"Labeled" -> False, "Colored" -> False,
	"Alternative" -> True,
	ColorRules -> Automatic
},
	Options[Graphics]
];

LambdaDiagram[expr_, depths_Association, extend_ ? BooleanQ, pad_ ? BooleanQ, thick_ ? BooleanQ, alternative_ ? BooleanQ, long : _ ? BooleanQ : True, pos_List : {}] := Block[{
	w, h, lines, dh = Max[depths, -1] + If[extend, 0, 1], dw = If[thick, 2, 1]
},
	Replace[expr, {
		Interpretation["\[Lambda]", tag_][body_] :> (
			{w, lines} = LambdaDiagram[body, depths, extend, pad, thick, alternative, long, Append[pos, 1]];
			If[ long &&	! alternative,
				lines = With[{depth = Lookup[depths, tag]},
					Replace[
						lines,
						Labeled[{x_, {y1_, y2_}}, l : (_ -> "Variable")] /; y1 == - depth :> Labeled[{x, {y1, y2 - 1}}, l],
						1
					]
				]
			];
			lines = Join[{Labeled[{{0, w}, - Lookup[depths, tag]}, pos -> "Lambda"]}, lines]
		),
		f_[arg_] :> Block[{fw, fLines, argw, argLines, fPos, argPos, fVarx, fVary, argVarx, argVary},
			{fw, fLines} = LambdaDiagram[f, If[pad, depths, KeyTake[depths, Cases[f, Interpretation[_, tag_] :> tag, All, Heads -> True]]], extend, pad, thick, alternative, False, Append[pos, 0]];
			{argw, argLines} = LambdaDiagram[arg, If[pad, depths, KeyTake[depths, Cases[arg, Interpretation[_, tag_] :> tag, All, Heads -> True]]], extend, pad, thick, alternative, False, Append[pos, 1]];
			
			fPos = Position[fLines, Labeled[_, _ -> "LambdaApplication" | "Application"]];
			argPos = Position[argLines, Labeled[_, _ -> "LambdaApplication" | "Application"]];
			If[	alternative,
				If[	! extend || fPos === {},
					fPos = Append[1] @ FirstPosition[fLines, Labeled[{_, {_, _}}, _]]
					,
					fPos = Append[1] @ FirstPosition[fLines, Labeled[{SortBy[Extract[fLines, fPos], {#[[1, 2]], - #[[1, 1, 2]]} &][[1, 1, 1, 2]], {_, _}}, _]]
				];
				{fVarx, fVary} = Extract[fLines, fPos];
				fVary = fVary[[2]];
				If[	! extend || argPos === {},
					argPos = Append[1] @ FirstPosition[argLines, Labeled[{_, {_, _}}, _]]
					,
					argPos = Append[1] @ FirstPosition[argLines, Labeled[{SortBy[Extract[argLines, argPos], {#[[1, 2]], #[[1, 1, 1]]} &][[1, 1, 1, 1]], {_, _}}, _]]
				];
				{argVarx, argVary} = Extract[argLines, argPos];
				argVary = argVary[[2]]
				,
				If[ ! extend || fPos === {},
					{fVarx, fVary} = FirstCase[fLines, Labeled[{x_, {_, y_}}, _] :> {x, y}]
					,
					{fVarx, fVary} = SortBy[Extract[fLines, fPos], {#[[1, 2]], - #[[1, 1, 2]]} &][[1, 1]];
					fVarx = fVarx[[1]]
				];
				If[ ! extend || argPos === {},
					{argVarx, argVary} = FirstCase[argLines, Labeled[{x_, {_, y_}}, _] :> {x, y}]
					,
					{argVarx, argVary} = SortBy[Extract[argLines, argPos], {#[[1, 2]], #[[1, 1, 1]]} &][[1, 1]];
					argVarx = argVarx[[1]]
				]
			];
			h = If[ extend,
				Min[fVary, argVary] - 1,
				Max[fVary, argVary]
			];
			If[ alternative,
				fLines = ReplacePart[fLines, Join[fPos, {2, 2}] -> h];
				argLines = ReplacePart[argLines, Join[argPos, {2, 2}] -> h]
			];
			argLines = Replace[argLines, Labeled[line_, label_] :> Labeled[line + {fw + dw, 0}, label], 1];
			lines = Join[
				fLines,
				{
					If[ alternative,
						Nothing,
						Splice @ {
							Labeled[{fVarx, {fVary, h}}, Append[pos, 0] -> "Term"],
							Labeled[{fw + argVarx + dw, {argVary, h}}, Append[pos, 1] -> "Term"]
						}
					],
					Labeled[{{fVarx, fw + argVarx + dw}, h}, pos -> If[MatchQ[f, Interpretation["\[Lambda]", _][_]], "LambdaApplication", "Application"]]
				},
				argLines
			];
			w = fw + argw + dw;
		],
		Interpretation[var_Integer, depth_Integer] :> (
			w = 0;
			lines = {Labeled[{0, {var - depth, - dh}}, pos -> "FreeVariable"]}
		),
		Interpretation[var_Integer, tag_] :> With[{depth = Lookup[depths, tag, -1]},
			w = 0;
			lines = {Labeled[{0, {- depth, - dh}}, pos -> "Variable"]}
		],
		_ :> (
			w = 0;
			lines = {Labeled[{0, {1, - dh}}, pos -> "Constant"]}
		)
	}];
	
	{w, lines}
]


LambdaDepths[expr_, depth_Integer : 0] := Replace[expr, {
	Interpretation["\[Lambda]", tag_][body_] :> (Sow[tag -> depth]; LambdaDepths[body, depth + 1]),
	f_[arg_] :> (LambdaDepths[f, depth]; LambdaDepths[arg, depth])
}]

LambdaPositions[expr_] := Block[{lambda = TagLambda[UntagLambda[expr], "Unique"], lambdaPos, argPos, tags, argTags},
	lambdaPos = Position[lambda, Interpretation["\[Lambda]", _], Heads -> True];
	argPos = Position[lambda, Interpretation[_Integer, tag_], Heads -> True];
	tags = Extract[lambda, Append[2] /@ lambdaPos];
	argTags = Extract[lambda, Append[2] /@ argPos];
	AssociationThread[lambdaPos -> Lookup[GroupBy[Thread[argTags -> argPos], First -> Last], tags, {}]]
]


LambdaDiagram[expr_, opts : OptionsPattern[]] := Block[{
	makeTooltip = Function[{pos, type},
		type -> MapAt[Framed, {pos}] @ If[StringEndsQ[type, "Application"],
			MapAt[Style[#, $Blue] &, Append[pos, 1]] @* MapAt[Style[#, $Red] &, Append[pos, 0]],
			Identity
		] @ expr
	],
	lambda = TagLambda[UntagLambda[expr]], depths, lines, dots,
	colorRules = Replace[OptionValue[ColorRules], {Automatic -> $LambdaDiagramColorRules, rules : {(_Rule | _RuleDelayed) ...} :> Join[rules, $LambdaDiagramColorRules]}],
	lineFunction, pointFunction, labelFunction,
	alternative = TrueQ[OptionValue["Alternative"]],
	labeled = OptionValue["Labeled"]
},
	With[{typeColorFunction =
		If[ TrueQ[OptionValue["Colored"]],
			Replace[colorRules],
			Function[Nothing]
		]
	},
		lineFunction = If[TrueQ[OptionValue["Thick"]],
			Function[{
				typeColorFunction[#3],
				Rectangle @@ Replace[#1, {
					(* Horizontal *)
					{{x_, z_}, y_} :> With[{shift = If[#3 === "Lambda", 3 / 4, 1 / 4]}, {{x - shift, y - 1 / 4}, {z + shift, y + 1 / 4}}],
					(* Vertical *)
					{x_, {y_, z_}} :> {{x - 1 / 4, y - 1 / 4}, {x + 1 / 4, z - 1 / 4}}
				}]}
			],
			Function[{typeColorFunction[#3], Line[Thread[#1]]}]
		]
	];
	pointFunction = If[TrueQ[OptionValue["Thick"]],
		Function[{Replace[#2, colorRules], Disk[#1, 1 / 4]}],
		Function[{Replace[#2, colorRules], Point[#]}]
	];
	labelFunction = Switch[labeled,
		True | All | Full | Automatic, With[{
			termRule = If[labeled === Automatic, {_, "Term"} -> Nothing, {{x_, {y1_, y2}}, "Term"} :> Text[Extract[expr, {pos}][[1]], {x - 1/8, y1 - 1/2}]]
		},
			Function[{line, pos, type},
				Replace[{line, type}, {
					{{{x1_, x2_}, y_}, "Lambda"} :> {Text["\[Lambda][", {x1 - 1/8, y}], Text["]", {x2 + 1/8, y}]},
					{{{x1_, x2_}, y_}, "Application"} :> {Text["(", {x1 - 1/8, y}], Text["@", {(x1 + x2)/2, y}], Text[")", {x2 + 1/8, y}]},
					{{{x1_, x2_}, y_}, "LambdaApplication"} :> {Text["(", {x1 - 1/8, y}], Text["\[Beta]", {(x1 + x2)/2, y}], Text[")", {x2 + 1/8, y}]},
					termRule,
					{{x_, {y1_, y2_}}, _} :> If[! alternative && y1 == y2, Nothing, Text[Extract[expr, {pos}][[1]], If[alternative && y1 == y2, {x, y1 - 1/8}, {x - 1/8, y1 - 1/2}]]]
				}]
			]
		],
		False | None,
		Function[Nothing]
	];
	depths = Association @ Reap[LambdaDepths[lambda]][[2]];
	lines = SortBy[
		LambdaDiagram[lambda, depths,
			TrueQ[OptionValue["Extend"]], TrueQ[OptionValue["Pad"]],
			TrueQ[OptionValue["Thick"]],
			TrueQ[OptionValue["Alternative"]]
		][[2]],
		MatchQ[Labeled[_, _ -> "LambdaApplication" | "Term"]]
	];
	dots = Switch[OptionValue["Dots"],
		All,
		{
			PointSize[Large],
			Cases[lines, Labeled[{{x_, _}, y_}, pos_ -> type_] :> Tooltip[pointFunction[{x, y}, type], makeTooltip[pos, type]]]
		},
		True | Automatic,
		{
			PointSize[Large],
			Cases[lines, Labeled[{{x_, _}, y_}, pos_ -> "Lambda"] :> Tooltip[pointFunction[{x, y}, "Lambda"], makeTooltip[pos, "Lambda"]]]
		},
		False | None,
		Nothing
	];
	If[ TrueQ[OptionValue["Dynamic"]]
		,
		With[{boxId = Unique[Symbol["LambdaDiagram"]]},
			DynamicModule[{style = ConstantArray[Thickness[Medium], Length[lines]]},
				Graphics[{
					MapIndexed[With[{i = #2[[1]], f = lineFunction},
						Replace[#1, Labeled[line_, pos_ -> type_] :> With[{
							primitive = {
								Tooltip[Dynamic @ {If[type === "LambdaApplication", Directive[Dashed, AbsoluteThickness[3]], Nothing], style[[i]], f[line, pos, type]}, makeTooltip[pos, type]],
								labelFunction[line, pos, type]
							}
						},
							EventHandler[primitive,
								{
									"MouseEntered" :> If[ListQ[style], style[[i]] = Thickness[Large]],
									"MouseExited" :> If[ListQ[style], style[[i]] = Thickness[Medium]],
									If[	type === "LambdaApplication",
										"MouseClicked" :> MathLink`CallFrontEnd[FrontEnd`BoxReferenceReplace[FE`BoxReference[EvaluationNotebook[], boxId],
											ToBoxes[LambdaDiagram[MapAt[BetaSubstitute, expr, {pos}], opts]]]
										],
										Nothing
									]
								}
							]
						]]] &,
						lines
					],
					dots
				},
					FilterRules[{opts}, Options[Graphics]],
					PlotLabel :> ClickToCopy[expr, expr]
				],
				BoxID -> boxId
			]
		]
		,
		Graphics[{
			Replace[lines,
				Labeled[line_, pos_ -> type_] :> {Tooltip[lineFunction[line, pos, type], makeTooltip[pos, type]], labelFunction[line, pos, type]},
				1
			],
			dots
		},
			FilterRules[{opts}, Options[Graphics]]
		]
	]
]


Options[BetaReduceStepPlot] = Join[
	{
		"Width" -> .4, "ShowInput" -> True, "ShowOutput" -> False, "ClipBounds" -> True,
		ColorRules -> {"Input" -> StandardRed, "Output" -> StandardGreen}
	},
	Options[BetaReduceList],
	Options[ListStepPlot]
];

BetaReduceStepPlot[lambda_, n : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := Block[{
	positions, path
},
	positions = Flatten[Reap[path = BetaReduceList[lambda, n, FilterRules[{opts}, Options[BetaReduceList]]], "Positions"][[2]], 2];
	path = Take[path, Length[positions] + 1];
	BetaReduceStepPlot[path -> positions, opts]
]

BetaReduceStepPlot[path_List -> positions_List, opts : OptionsPattern[]] := Block[{
	width = OptionValue["Width"],
	showInputQ = TrueQ[OptionValue["ShowInput"]],
	showOutputQ = TrueQ[OptionValue["ShowOutput"]],
	clipBoundsQ = TrueQ[OptionValue["ClipBounds"]],
	inputColor = Lookup[OptionValue[ColorRules], "Input"],
	outputColor = Lookup[OptionValue[ColorRules], "Output"],
	columns
},
	columns = Append[{LeafCount[Last[path]], {}}] @ MapThread[{src, tgt, pos, i} |-> With[{
		srcTerm = Extract[src, {pos}][[1]],
		tgtTerm = Extract[tgt, {pos}][[1]]
	},
	{
		srcPos = LexicographicSort @ Position[src, _, {-1}, Heads -> True],
		srcSubPos = Join[pos, #] & /@ LexicographicSort[Position[srcTerm, _, {-1}, Heads -> True]][[{1, -1}]],
		tgtPos = LexicographicSort @ Position[tgt, _, {-1}, Heads -> True],
		tgtSubPos = Join[pos, #] & /@ LexicographicSort[Position[tgtTerm, _, {-1}, Heads -> True]][[{1, -1}]]
	},
		{
			LeafCount[src],
			{
				If[	showInputQ,
					{
						inputColor,
						Tooltip[
							Rectangle @@ Thread[{
								If[ showOutputQ,
									{i + .25 - width / 2, i + .25 + width / 2},
									{i - width / 2, i + width / 2}
								],
								Catenate[Lookup[PositionIndex[srcPos], srcSubPos]]
							}],
							srcTerm
						]
					},
					Nothing
				]
				,
				If[ showOutputQ,
					{
						outputColor,
						Tooltip[
							Rectangle @@ Thread[{
								If[	showInputQ,
									{i + .75 - width / 2, i + .75 + width / 2},
									{i + 1 - width / 2, i + 1 + width / 2}
								],
								Catenate[Lookup[PositionIndex[tgtPos], tgtSubPos]]
							}],
							srcTerm
						]
					},
					Nothing
				]
			}
		}
		],
		{
			Most[path],
			Rest[path],
			positions,
			Range[Length[positions]]
		}
	];
	ListStepPlot[
		columns[[All, 1]], Center,
		FilterRules[{opts}, Options[ListStepPlot]],
		PlotRange -> {{If[clipBoundsQ && ! showInputQ, 1.5, .5], Length[path] + If[clipBoundsQ && ! showOutputQ, -.5, .5]}, {1, All}},
		Filling -> Axis,
		Epilog -> columns[[All, 2]],
		PlotStyle -> Opacity[.4],
		Frame -> True,
		AspectRatio -> .4
	]
]


(* Special lambdas *)

SetAttributes[ChurchNumeral, Listable]
ChurchNumeral[n_Integer ? NonNegative] := $Lambda[$Lambda[Nest[2, 1, n]]]


fromChurchNumeral[expr_] := Block[{term = expr, count = 0},
	While[True,
		If[	MatchQ[term, Interpretation[1, _] | 1],
			Return[count]
		];
		
		If[ MatchQ[term, (Interpretation[2, _] | 2)[_]],
			term = term[[1]];
			count++;
			Continue[];
		];
		
		Return[
			Failure["UnrecognizedChurchNumeral",
				<|"MessageTemplate" -> "Unrecognised term: ``", "MessageParameters" -> expr|>
			]
		];
	]
]

FromChurchNumeral[$LambdaPattern[$LambdaPattern[expr_]]] := fromChurchNumeral[expr]

FromChurchNumeral[_] := Failure["UnrecognizedChurchNumeral", <|"MessageTemplate" -> "Church numeral should be of the form \[Lambda][\[Lambda][2[2[...[1]]]]]"|>]


ChurchNumeralQ[expr_] := ! FailureQ[FromChurchNumeral[expr]]


$LambdaBusyBeavers := $LambdaBusyBeavers = ParseLambda[StringReplace[#, "\\" -> "\[Lambda]"], "Indices"] & /@ 
 	FirstCase[
  		Import["https://wiki.bbchallenge.org/wiki/Busy_Beaver_for_lambda_calculus", "XMLObject"],
  		XMLElement["table", {"class" -> "wikitable"}, table_] :> Most @ Cases[table, XMLElement["code", {}, {code_}] :> code, All],
		{},
  		All
  	]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
