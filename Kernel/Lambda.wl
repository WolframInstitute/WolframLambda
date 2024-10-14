(* ::Package:: *)

(* ::Section:: *)
(*Package Header*)


BeginPackage["Wolfram`Lambda`"];


(* ::Text:: *)
(*Declare your public symbols here:*)


RandomLambda;
EnumerateLambdas;

LambdaSubstitute;
EvalLambda;
LambdaFreeVariables;

BetaReductions;
BetaReduce;
EtaReduce;

LambdaCombinator;
CombinatorLambda;

LambdaApplication;
LambdaBrackets;
LambdaString;

LambdaFunction;
FunctionLambda;
LambdaTree;
LambdaConvert;
ParseLambda;

TagLambda;
ColorizeLambda;
LambdaSmiles;
LambdaDiagram;


Begin["`Private`"];


(* ::Section:: *)
(*Definitions*)


EnumerateLambdas[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1] :=
	\[FormalLambda] /@ If[ depth == maxDepth,
		Groupings[Catenate[Tuples[Range[maxDepth], #] & /@ Range[maxLength]], {Construct -> 2}],
		Groupings[Catenate[Tuples[Join[Range[depth], EnumerateLambdas[maxDepth, maxLength, depth + 1]], #] & /@ Range[maxLength]], {Construct -> 2}]
	]


randomGrouping[xs_List] := Replace[xs, {{x_} :> x, {x_, y_} :> x[y], {x_, y_, z__} :> If[RandomReal[] < .5, x[randomGrouping[{y, z}]], x[y][randomGrouping[{z}]]]}]

randomLambda[maxDepth_Integer : 2, maxLength_Integer : 2, depth_Integer : 1] := If[ depth == maxDepth,
	With[{lambdaQ = RandomReal[] < .5}, If[lambdaQ, \[FormalLambda], Identity] @ randomGrouping @ RandomInteger[{1, If[lambdaQ, depth, depth - 1]}, RandomInteger[{1, maxLength}]]],
	\[FormalLambda] @ randomGrouping @ Table[randomLambda[maxDepth, maxLength, depth + 1], RandomInteger[{1, maxLength}]]
]

RandomLambda[maxDepth_Integer : 2, maxLength_Integer : 2, n : _Integer | Automatic : Automatic] := If[n === Automatic, randomLambda[maxDepth, maxLength], Table[randomLambda[maxDepth, maxLength], n]]


(* From Max Niederman *)

(* offset only the free variables in a lambda term *)
offsetFree[expr_, 0, ___] := expr
offsetFree[\[FormalLambda][body_], offset_, depth_ : 0] := \[FormalLambda][offsetFree[body, offset, depth + 1]]
offsetFree[fun_[x_], offset_, depth_ : 0] := offsetFree[fun, offset, depth][offsetFree[x, offset, depth]]
offsetFree[var_Integer, offset_, depth_ : 0] := If[var > depth, var + offset, var]
offsetFree[expr_, offset_, depth_ : 0] := expr

(* perform a substitution of an argument into the body of a lambda, and also decrement the free parameters by one *)
betaSubstitute[\[FormalLambda][body_], arg_, paramIdx_ : 1] := \[FormalLambda][betaSubstitute[body, arg, paramIdx + 1]]
betaSubstitute[fun_[x_], arg_, paramIdx_ : 1] := betaSubstitute[fun, arg, paramIdx][betaSubstitute[x, arg, paramIdx]]
betaSubstitute[var_Integer, arg_, paramIdx_ : 1] := Which[
	var < paramIdx, var,
	var == paramIdx,  offsetFree[arg, paramIdx - 1],
	var > paramIdx, var - 1
]
betaSubstitute[expr_, arg_, paramIdx_ : 1] := expr

(* find all possible beta-reductions by walking the expression tree applying betaSubstitute where possible *)
BetaReductions[\[FormalLambda][body_][arg_]] := Join[
	{betaSubstitute[body, arg]},
	\[FormalLambda][#][arg] & /@ BetaReductions[body],
	\[FormalLambda][body][#] & /@ BetaReductions[arg]
]
BetaReductions[\[FormalLambda][body_]] := \[FormalLambda] /@ BetaReductions[body]
BetaReductions[fun_[arg_]] := Join[#[arg] & /@ BetaReductions[fun], fun[#] & /@ BetaReductions[arg]]
BetaReductions[expr_] := {}


BetaReduce[expr_] := expr //. \[FormalLambda][body_][arg_] :> betaSubstitute[body, arg]
BetaReduce[expr_, n_Integer] := If[ n <= 0, expr,
	With[{pos = FirstPosition[expr, \[FormalLambda][_][_]]}, If[MissingQ[pos], expr, BetaReduce[ReplaceAt[expr, \[FormalLambda][body_][arg_] :> betaSubstitute[body, arg], pos], n - 1]]]
]


(* substitute all variables *)
LambdaSubstitute[expr_, vars_Association : <||>, offset_Integer : 0, depth_Integer : 0, subDepth_Integer : 0] :=
	If[ Length[vars] == 0,
	expr
	,
	Replace[expr, {
		\[FormalLambda][body_] :> \[FormalLambda][LambdaSubstitute[body, vars, offset, depth, subDepth + 1]],
		f_[x_] :> LambdaSubstitute[f, vars, offset, depth, subDepth][LambdaSubstitute[x, vars, offset, depth, subDepth]],
		var_Integer :> 
			If[	KeyExistsQ[vars, var - subDepth],
				(* argument variable substitutution *)
				offsetFree[Lookup[vars, var - subDepth], subDepth + depth]
				,
				(* free or bound variable *)
				If[	var > subDepth + depth + 1,
					(* free variable *)
					var + offset,
					(* bound variable *)
					var
				]
			]
	}]
]

(* TODO: non-recursive version *)
(* this tries to delay substitution *)
EvalLambda[expr_, vars_Association : <||>, n : _Integer | Infinity : Infinity, k_Integer : 0, offset_Integer : 0, depth_Integer : 0] := If[ k >= n,
	With[{subst = LambdaSubstitute[expr, vars, offset, depth]}, Sow[k]; subst]
	,
	Replace[
		expr,
		{
			(* beta reductions uses argument->head order *)
			(lambda : \[FormalLambda][body_])[arg_] :> With[{evalArg = Reap[EvalLambda[arg, vars, n, k, offset, depth]]},
				{l = If[MatchQ[evalArg, _TerminatedEvaluation], Return[evalArg, With], evalArg[[2, 1, 1]]]},
				If[ l >= n,
					With[{subst = LambdaSubstitute[lambda, vars, offset, depth][evalArg[[1]]]}, Sow[If[subst === lambda, l, l + 1]]; subst]
					,
					EvalLambda[body, <|1 -> evalArg[[1]], KeyMap[# + 1 &, vars]|>, n, l + 1, -1]
				]
			],
			\[FormalLambda][body_] :> \[FormalLambda][EvalLambda[body, KeyMap[# + 1 &, vars], n, k, offset, depth + 1]],
			(* standard head->argument evaluation order *)
			head_[arg_] :> With[
				{evalHead = Reap[EvalLambda[head, vars, n, k, offset, depth]]},
				{evalArg = If[MatchQ[evalHead, _TerminatedEvaluation], Return[evalHead, With], Reap[EvalLambda[arg, vars, n, evalHead[[2, 1, 1]], offset, depth]]]},
				{l = If[MatchQ[evalArg, _TerminatedEvaluation], Return[evalArg, With], evalArg[[2, 1, 1]]]},
				If[ l >= n || evalHead[[1]][evalArg[[1]]] === head[arg],
					Sow[l]; evalHead[[1]][evalArg[[1]]]
					,
					EvalLambda[evalHead[[1]][evalArg[[1]]], n, l]
				]
			]
			,
			_ :> With[{subst = LambdaSubstitute[expr, vars, offset, depth]}, Sow[k]; subst]
		}
	]
]


EtaReduce[expr_] := expr //. \[FormalLambda][(f : Except[_Integer])[1]] :> offsetFree[f, -1]
EtaReduce[expr_, n_Integer] := If[ n <= 0, expr,
	With[{pos = FirstPosition[expr, \[FormalLambda][Except[_Integer][1]]]}, If[MissingQ[pos], expr, EtaReduce[ReplaceAt[expr, \[FormalLambda][f_[1]] :> offsetFree[f, -1], pos], n - 1]]]
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
	CombinatorI -> \[FormalLambda][1],
	CombinatorK -> \[FormalLambda][\[FormalLambda][2]],
	CombinatorS -> \[FormalLambda][\[FormalLambda][\[FormalLambda][3[1][2[1]]]]],
	CombinatorC -> \[FormalLambda][\[FormalLambda][\[FormalLambda][3[1][2]]]],
	CombinatorB -> \[FormalLambda][\[FormalLambda][\[FormalLambda][3[2[1]]]]]
}


LambdaFreeVariables[expr_, pos_List : {}, depth_Integer : 0] := Replace[expr, {
	\[FormalLambda][body_][arg_] :> Join[LambdaFreeVariables[body, Join[pos, {0, 1}], depth + 1], LambdaFreeVariables[arg, Append[pos, 1], depth]],
	\[FormalLambda][body_] :> LambdaFreeVariables[body, Append[pos, 1], depth + 1],
	f_[x_] :> Join[LambdaFreeVariables[f, Append[pos, 0], depth], LambdaFreeVariables[x, Append[pos, 1], depth]],
	var_Integer :> If[var > depth, {{depth, pos, var}}, {}],
	_ :> {}
}
]


TagLambda[expr_, lambdas_Association] := With[{
	nextLambdas = KeyMap[# + 1 &] @ lambdas
},
	expr /. {
		\[FormalLambda][body_][y_] :> With[{newLambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]][TagLambda[y, lambdas]]],
		\[FormalLambda][body_] :> With[{newLambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]]],
		term_Integer :> Interpretation[term, Evaluate @ If[KeyExistsQ[lambdas, term], lambdas[term][[2]], Max[Keys[lambdas]]]]
	}
]
TagLambda[\[FormalLambda][body_], "Unique"] := With[{lambda = Interpretation["\[Lambda]", Evaluate[Unique["\[Lambda]"]]]}, lambda[TagLambda[body, <|1 -> lambda|>]]]

SetAttributes[AlphabetString, Listable]
AlphabetString[0] = ""
AlphabetString[n_Integer ? NonNegative] := Block[{q, r},
	{q, r} = QuotientRemainder[n, 26];
	If[r == 0, (q -= 1; r = 26)];
	AlphabetString[q] <> FromLetterNumber[r]
]

TagLambda[expr_, "Alphabet"] := Block[{lambda = TagLambda[expr, "Unique"], vars},
	vars = Cases[lambda, Interpretation["\[Lambda]", tag_] :> tag, All, Heads -> True];
	lambda /. MapThread[With[{sym = Unevaluated @@ #2}, #1 :> sym] &, {vars, MakeExpression /@ AlphabetString[Range[Length[vars]]]}]
]

TagLambda[expr_, form_String : "Alphabet"] := expr /. lambda_\[FormalLambda] :> TagLambda[lambda, form]

ResourceFunction["AddCodeCompletion"]["TagLambda"][None, {"Alphabet", "Unique"}]


LambdaFunction[expr_, head_ : Identity] := head @@ (Hold[Evaluate @ TagLambda[expr, "Alphabet"]] //. {Interpretation["\[Lambda]", x_][body_] :> Function[x, body], Interpretation[_Integer, x_] :> x})


FunctionLambda[expr_, vars_Association : <||>] := Replace[Unevaluated[expr], {
	Verbatim[Function][var_, body_][x_] :> \[FormalLambda][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]][FunctionLambda[x, vars]],
	Verbatim[Function][var_, body_] :> \[FormalLambda][FunctionLambda[Unevaluated[body], Prepend[vars + 1, var -> 1]]],
	f_[x_] :> FunctionLambda[Unevaluated[f], vars][FunctionLambda[Unevaluated[x], vars]],
	var_Symbol :> Replace[var, vars]
}]


LambdaTree[lambda_, opts___] := ExpressionTree[
	TagLambda[lambda] //. (f : Except[Interpretation["\[Lambda]", _]])[x_] :> Application[f, x] //. Interpretation[_, tag_] :> ToString[Unevaluated[tag]],
	"Heads", opts, Heads -> False, 
	TreeElementLabel -> TreeCases[Application] -> None, 
	TreeElementStyle -> {TreeCases[Application] -> LightGray, "Leaves" -> LightYellow, _ -> LightRed}, 
	TreeElementShapeFunction -> TreeCases[Application] -> None
]


LambdaApplication[lambda_, ___] := lambda //. (f : Except[\[FormalLambda]])[x_] :> Application[f, x]

LambdaBrackets[lambda_, ___] := RawBoxes[ToBoxes[LambdaApplication[lambda]] /. "\[FormalLambda]" | "\[Application]" -> "\[InvisibleSpace]"]

LambdaString[lambda_, ___] := TagLambda[lambda] //. {
   	Interpretation["\[Lambda]", var_][body_] :> StringTemplate["(\[Lambda]``.``)"][ToString[Unevaluated[var]], LambdaString[body]],
	Interpretation[_, var_] :> ToString[Unevaluated[var]],
	f_[x_] :> StringTemplate["(`` ``)"][LambdaString[f], LambdaString[x]]
}


LambdaConvert[expr_, form_String : "Application", args___] := Switch[form,
	"Application",
	LambdaApplication[expr],
	"BracketParens",
	LmabdaBrackets[expr],
	"Function",
	LambdaFunction[expr, args],
	"Combinator",
	LambdaCombinator[expr, args],
	"Tree",
	LambdaTree[expr, args],
	"String",
	LambdaString[expr, args],
	_,
	Missing[form]
]
ResourceFunction["AddCodeCompletion"]["LambdaConvert"][None, {"Application", "BracketParens", "Function", "Combinator", "Tree", "String"}]


BalancedParenthesesQ[str_] := FixedPoint[StringDelete["()"], StringDelete[str, Except["(" | ")"]]] === ""

ParseVariableLambda[str_String, vars_Association : <||>] := First @ StringCases[str, {
	WhitespaceCharacter ... ~~ "\[Lambda]" ~~ WhitespaceCharacter ... ~~ var : WordCharacter .. ~~ WhitespaceCharacter ... ~~ "." ~~ WhitespaceCharacter ... ~~ body__ :>
		\[FormalLambda][ParseVariableLambda[body, <|vars + 1, var -> 1|>]],
	f__ ~~ WhitespaceCharacter ... ~~ x__ /; ! StringMatchQ[x, WhitespaceCharacter ..] && BalancedParenthesesQ[f] && BalancedParenthesesQ[x] :>
		ParseVariableLambda[f, vars][ParseVariableLambda[x, vars]],
	"(" ~~ term__ ? BalancedParenthesesQ ~~ ")" :> ParseVariableLambda[term, vars],
	var : WordCharacter .. :> Replace[var, vars]
}]

ParseIndexLambda[str_String] := First @ StringCases[str, {
	WhitespaceCharacter ... ~~ "\[Lambda]" ~~ WhitespaceCharacter ... ~~ body__ ~~ WhitespaceCharacter ... :> \[FormalLambda][ParseIndexLambda[body]],
	f__ ~~ WhitespaceCharacter .. ~~ x__ /; BalancedParenthesesQ[f] && BalancedParenthesesQ[x] :> ParseIndexLambda[f][ParseIndexLambda[x]],
	WhitespaceCharacter ... ~~ "(" ~~ term__ ? BalancedParenthesesQ ~~ ")" ~~ WhitespaceCharacter ... :> ParseIndexLambda[term],
	WhitespaceCharacter ... ~~ var : DigitCharacter .. ~~ WhitespaceCharacter ... :> Interpreter["Integer"][var]
}]

ParseLambda[str_String, form_String : "Variables"] := Switch[form,
	"Variables",
	ParseVariableLambda[str],
	"Indices",
	ParseIndexLambda[str],
	_,
	Missing[form]
]

ResourceFunction["AddCodeCompletion"]["ParseLambda"][None, {"Variables", "Indices"}]


ColorizeTaggedLambda[lambda_] := With[{lambdas = Cases[lambda, Interpretation["\[Lambda]", x_], All, Heads -> True]},
	lambda /. MapThread[x : #1 | Interpretation[_Integer, Evaluate @ #1[[2]]] :> Style[x, Bold, #2] &, {lambdas, ColorData[109] /@ Range[Length[lambdas]]}]
]


ColorizeLambda[expr_] := ColorizeTaggedLambda[TagLambda[expr]]


LambdaRow[Interpretation["\[Lambda]", tag_][body_], depth_ : 0] := {{\[FormalLambda][tag] -> depth, Splice[LambdaRow[body, depth + 1]]}}
LambdaRow[Interpretation[i_Integer, tag_], depth_ : 0] := {i -> tag}
LambdaRow[(f : Except[Interpretation["\[Lambda]", _]])[(g : Except[Interpretation["\[Lambda]", _]])[x_]], depth_ : 0] := Append[LambdaRow[f, depth], LambdaRow[g[x], depth]]
LambdaRow[f_[x_], depth_ : 0] := Join[LambdaRow[f, depth], LambdaRow[x, depth]]
LambdaRow[x_, depth_ : 0] := {x}

Options[LambdaSmiles] = Join[{"Height" -> 3}, Options[Style], Options[Graphics]];
LambdaSmiles[lambda_, opts : OptionsPattern[]] := Block[{row = LambdaRow[TagLambda[lambda]], lambdaPos, varPos, lambdas, vars, colors, arrows, height = OptionValue["Height"], styleOpts = FilterRules[{opts}, Options[Style]]},
	row = FixedPoint[Replace[#, xs_List :> Splice[{"(", Splice[xs], ")"}], 1] &, row];
	lambdaPos = Position[row, _\[FormalLambda] -> _, {1}, Heads -> False];
	varPos = Position[row, _Integer -> _, {1}, Heads -> False];
	lambdas = AssociationThread[#[[All, 1, 1]], Thread[First /@ lambdaPos -> #[[All, 2]]]] & @ Extract[row, lambdaPos];
	vars = Extract[row, varPos];
	colors = Association @ MapIndexed[#1[[1, 1]] -> ColorData[109][#2[[1]]] &, Extract[row, lambdaPos]];
	row = MapAt[Style["\[Lambda]", Lookup[colors, #[[1, 1]], Black]] &, lambdaPos] @ MapAt[Style[#[[1]], Lookup[colors, #[[2]], Black]] &, varPos] @ row;
	
	arrows = MapThread[With[{dh = Ceiling[#1[[1]] / 2], sign = (-1) ^ Boole[EvenQ[#1[[1]]]], l = lambdas[#1[[2]]]},
		If[MissingQ[l], Nothing, {colors[#1[[2]]], Line[Threaded[{1, sign}] * {{#2, 1}, {#2, 1 + dh / (l[[2]] + 1)}, {l[[1]], 1 + dh / (l[[2]] + 1)}, {l[[1]], 1}}]}]] &,
		{vars, First /@ varPos}
	];
	Graphics[{
		MapIndexed[Inset[Style[#1, styleOpts, FontSize -> 16], {#2[[1]], 0}] &, row],
		arrows
	},
		FilterRules[{opts}, Options[Graphics]],
		AspectRatio -> height / Length[row]
	]
]


Options[LambdaDiagram] = Join[{"Dynamic" -> False, "Extend" -> False, "Pad" -> True, "Dots" -> True}, Options[Graphics]];

LambdaDiagram[expr_, depths_Association, extend_ ? BooleanQ, pad_ ? BooleanQ, pos_List : {}] := Block[{
	w, h, lines
},
	h = If[extend, 0, -1];
	Replace[expr, {
		Interpretation["\[Lambda]", tag_][body_] :> (
			{w, lines} = LambdaDiagram[body, depths, extend, pad, Append[pos, 1]];
			lines = Join[{Labeled[{{0, w}, - Lookup[depths, tag]}, pos -> "Lambda"]}, lines]
		),
		f_[arg_] :> Block[{fw, fLines, argw, argLines, fPos, argPos, fVarx, fVary, argVarx, argVary},
			{fw, fLines} = LambdaDiagram[f, If[pad, depths, KeyTake[depths, Cases[f, Interpretation[_, tag_] :> tag, All, Heads -> True]]], extend, pad, Append[pos, 0]];
			{argw, argLines} = LambdaDiagram[arg, If[pad, depths, KeyTake[depths, Cases[arg, Interpretation[_, tag_] :> tag, All, Heads -> True]]], extend, pad, Append[pos, 1]];
			fPos = Position[fLines, Labeled[_, _ -> "Application"]];
			If[	fPos === {},
				fPos = Append[1] @ FirstPosition[fLines, Labeled[{_, {_, _}}, _]]
				,
				fPos = Append[1] @ FirstPosition[fLines, Labeled[{TakeSmallestBy[Extract[fLines, fPos], #[[1, 2]] &, 1][[1, 1, 1, 2]], {_, _}}, _]]
			];
			{fVarx, fVary} = Extract[fLines, fPos];
			fVary = fVary[[2]];
			argPos = Append[1] @ FirstPosition[argLines, Labeled[{_, {_, _}}, _]];
			{argVarx, argVary} = Extract[argLines, argPos];
			h += If[ extend,
				Min[fVary, argVary[[2]]] - 1,
				Max[fVary, argVary[[2]]] + 1
			];
			fLines = ReplacePart[fLines, Join[fPos, {2, 2}] -> h];
			argLines = ReplacePart[argLines, Join[argPos, {2, 2}] -> h];
			argLines = Replace[argLines, Labeled[line_, label_] :> Labeled[line + {fw + 1, 0}, label], 1];
			lines = Join[
				fLines,
				{Labeled[{{fVarx, fw + 1}, h}, pos -> If[MatchQ[f, Interpretation["\[Lambda]", _][_]], "LambdaApplication", "Application"]]},
				argLines
			];
			w = fw + argw + 1;
		],
		Interpretation[var_Integer, depth_Integer] :> (
			w = 0; h -= Max[depths, -1];
			lines = {Labeled[{0, {var - depth, h}}, pos -> "FreeVariable"]}
		),
		Interpretation[_Integer, tag_Symbol] :> (
			w = 0; h -= Max[depths, -1];
			lines = {Labeled[{0, {- Lookup[depths, tag, -1], h}}, pos -> "Variable"]}
		),
		_ :> (
			w = 0; h -= Max[depths, -1];
			lines = {Labeled[{0, {1, h}}, pos -> "Constant"]}
		)
	}];
	
	{w, lines}
]

LambdaDepths[expr_, depth_Integer : 0] := Replace[expr, {
	Interpretation["\[Lambda]", tag_][body_] :> (Sow[tag -> depth]; LambdaDepths[body, depth + 1]),
	f_[arg_] :> (LambdaDepths[f, depth]; LambdaDepths[arg, depth])
}]

LambdaDiagram[expr_, opts : OptionsPattern[]] := Block[{
	makeTooltip = Function[{pos, type},
		type -> MapAt[Framed, {pos}] @ If[StringEndsQ[type, "Application"],
			MapAt[Style[#, Blue] &, Append[pos, 1]] @* MapAt[Style[#, Red] &, Append[pos, 0]],
			Identity
		] @ expr
	],
	lambda = TagLambda[expr], depths, dots
},
	depths = Association @ Reap[LambdaDepths[lambda]][[2]];
	lines = LambdaDiagram[lambda, depths, TrueQ[OptionValue["Extend"]], TrueQ[OptionValue["Pad"]]][[2]];
	dots = If[TrueQ[OptionValue["Dots"]],
		{
			PointSize[Large],
			Cases[lines, Labeled[{{x_, _}, y_}, pos_ -> type_] :> Tooltip[Point[{x, y}], makeTooltip[pos, type]]]
		},
		Nothing
	];
	If[ TrueQ[OptionValue["Dynamic"]]
		,
		With[{boxId = Unique[Symbol["LambdaDiagram"]]},
			DynamicModule[{style},
				lines = SortBy[lines, MatchQ[Labeled[{{_, _}, _}, _ -> "LambdaApplication"]]];
				style = ConstantArray[Thickness[Medium], Length[lines]];
				Graphics[{
					MapIndexed[With[{i = #2[[1]]},
						Replace[#1, Labeled[line_, pos_ -> type_] :> With[{
							primitive = Tooltip[Dynamic @ {style[[i]], Line[Thread[line]]}, makeTooltip[pos, type]]
						},
							EventHandler[primitive,
								{
									"MouseEntered" :> (style[[i]] = If[type === "LambdaApplication", Directive[Dashed, AbsoluteThickness[3]], Thickness[Large]]),
									"MouseExited" :> (style[[i]] = Thickness[Medium]),
									If[	type === "LambdaApplication",
										"MouseClicked" :> MathLink`CallFrontEnd[FrontEnd`BoxReferenceReplace[FE`BoxReference[EvaluationNotebook[], boxId],
											ToBoxes[LambdaDiagram[MapAt[BetaReduce[#, 1] &, expr, {pos}], opts]]]
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
				Labeled[line_, pos_ -> type_] :> Tooltip[Line[Thread[line]], makeTooltip[pos, type]],
				1
			],
			dots
		},
			FilterRules[{opts}, Options[Graphics]]
		]
	]
]


(* ::Section::Closed:: *)
(*Package Footer*)


End[];
EndPackage[];
