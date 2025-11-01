BeginPackage["Wolfram`Lambda`"];

ClearAll[
	$Lambda,
	ClosedLambdaQ,
	BetaNormalQ,
	LambdaFreeVariables,
	
	LambdaCombinator,
	CombinatorLambda,
	LambdaTag,
	LambdaTags,

	LambdaApplication,
	LambdaRightApplication,
	LambdaForm,
	LambdaVariableForm,
	LambdaBrackets,
	LambdaDepthForm,
	LambdaString,
	LambdaToHaskell,

	LambdaFunction,
	FunctionLambda,

	LambdaConvert,
	ParseLambda,
	LambdaBLC,
	BLCLambda,

	TagLambda,
	UntagLambda,
	LambdaUntag,
	LambdaDepths,
	LambdaPositions,
	ColorizeLambda,
	UncolorizeLambda,

	ChurchNumeral,
	FromChurchNumeral,
	ChurchNumeralQ,
	$LambdaBusyBeavers,

	$LambdaStyles,
	$LambdaGridStyleRules,
	$LambdaResults
]

If[ ! ValueQ[$Lambda],
	$Lambda = Global`\[Lambda]
]

Begin["`Private`"];


$LambdaHead = $Lambda | \[FormalLambda] | (sym_Symbol /; Developer`SymbolQ[Unevaluated[sym]] && SymbolName[Unevaluated[sym]] == "\[Lambda]") | "\[Lambda]" | Style["\[Lambda]", ___]

$LambdaPattern = $LambdaHead | Interpretation["\[Lambda]" | Style["\[Lambda]", ___], _]

BetaNormalQ[expr_] := FreeQ[expr, $LambdaPattern[_][_]]


$LambdaStyles = <|
	"Lambda" -> Hue[0.8174603174603176, 0.20999999999999996`, 1.], 
   	"DebruijnIndex" -> Hue[0.576923076923077, 0.13, 1., 1.], 
	"MinimalLambda" -> Hue[0.82, 0.5, 1.], 
   	"MinimalDebruijnIndex" -> Hue[0.58, 0.5, 1.], 
   	"BrighterLambda" -> Hue[0.833, 0.622, 0.957], 
   	"DebruijnIndexBorder" -> RGBColor[0.276768, 0.66747216, 0.72075, 1], 
   	"BrighterDebruijnIndex" -> Hue[0.52, 0.616, 0.961], 
   	"Application" -> GrayLevel[0.9, 1], 
   	"BrighterApplication" -> Hue[0.305, 0.795, 0.927], 
   	"BlackLambda" -> Black,
   	"WhiteLambda" -> White,
	"Edges" -> RGBColor[0.6, 0.6, 0.6],
	"LoopbackEdges" -> Directive[$Black, Thickness[0.01], Dotted],
   	"ApplicationBorder" -> GrayLevel[0.6, 1.], 
   	"VariableArgument" -> RGBColor[1., 0.88, 0.77], 
   	"BrighterVariableArgument" -> RGBColor[1., 0.71, 0.06],
	"Variable" -> $Green,
	"Labels" -> Black
|>

$LambdaTreeColorRules := Join[
	{
		"Lambda" -> Directive[$LambdaStyles["Lambda"], EdgeForm[$LambdaStyles["BrighterLambda"]]],
		"MinimalLambda" -> Directive[$LambdaStyles["MinimalLambda"], EdgeForm[$LambdaStyles["BrighterLambda"]]],
		"Application" -> Directive[$LambdaStyles["Application"], EdgeForm[$LambdaStyles["ApplicationBorder"]]],
		"Index" -> Directive[$LambdaStyles["DebruijnIndex"], EdgeForm[$LambdaStyles["DebruijnIndexBorder"]]],
		"MinimalIndex" -> Directive[$LambdaStyles["MinimalDebruijnIndex"], EdgeForm[$LambdaStyles["DebruijnIndexBorder"]]],
		"Variable" -> Directive[$LambdaStyles["VariableArgument"], EdgeForm[Darker[$LambdaStyles["BrighterVariableArgument"], .1]]]
	}
	,
	Normal[$LambdaStyles]
]

$LambdaGridStyleRules = {Background -> {{GrayLevel[0.93]}, {GrayLevel[0.968]}, {{1, 1} -> GrayLevel[0.93]}}, ItemStyle -> {{Italic}, Automatic}, Frame -> All, FrameStyle -> GrayLevel[0.75], Spacings -> {.75, .6}}

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

LambdaHaskellTerm[Interpretation["\[Lambda]", tag_][body_]] := "(L(\\" <> ToString[Unevaluated[tag]] <> "->" <> LambdaHaskellTerm[body] <> "))"
LambdaHaskellTerm[f_[x_]] := "(app " <> LambdaHaskellTerm[f] <> " " <> LambdaHaskellTerm[x] <> ")"
LambdaHaskellTerm[Interpretation[_, var_]] := ToString[Unevaluated[var]]

LambdaToHaskell[lambda_] := StringTemplate["
{-# htermination term #-}


data Term = L (Term -> Term)

app :: Term -> Term -> Term
app (L f) x = f x

term = ``
"][LambdaHaskellTerm[TagLambda[lambda]]]

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


tagLambda[tag_] := Interpretation["\[Lambda]", tag]
tagLambda[e_, tag_] := If[MatchQ[e, $LambdaHead], Interpretation["\[Lambda]", tag], Interpretation[e, tag]]

unchainTags[tag_] := tag //. {(x_ -> subTag_ -> y_) :> With[{z = unchainTags[x][unchainTags[y]]}, Interpretation[z, subTag]], (subTag_ -> y_) :> Interpretation[y, subTag]}

simpleTags[expr_] := expr /. Interpretation[x_, tag_] :> Interpretation[x, Evaluate[unchainTags[tag] //. Interpretation[_[y_, ___], subTag_] :> Interpretation[y, subTag]]]

TagLambda[expr_, lambdas_Association] := With[{
	nextLambdas = KeyMap[# + 1 &] @ lambdas
},
	simpleTags[expr] /. {
		(l : $LambdaHead)[body_][y_] :> With[{newLambda = tagLambda[l, Unique["\[Lambda]"]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]][TagLambda[y, lambdas]]],
		(l : $LambdaHead)[body_] :> With[{newLambda = tagLambda[l, Unique["\[Lambda]"]]}, newLambda[TagLambda[body, Prepend[1 -> newLambda] @ nextLambdas]]],
		term_Integer :> Interpretation[term, Evaluate @ If[KeyExistsQ[lambdas, term], lambdas[term][[2]], Max[Keys[lambdas]]]]
	}
]
TagLambda[(l : $LambdaHead)[body_], "Unique"] := With[{lambda = tagLambda[l, Unique["\[Lambda]"]]}, lambda[TagLambda[body, <|1 -> lambda|>]]]

SetAttributes[AlphabetString, Listable]
AlphabetString[0] = ""
AlphabetString[n_Integer ? NonNegative] := Block[{q, r},
	{q, r} = QuotientRemainder[n, 26];
	If[r == 0, (q -= 1; r = 26)];
	AlphabetString[q] <> FromLetterNumber[r]
]

TagLambda[expr_, symbols : _List | Automatic | "Alphabet"] := Block[{lambda = TagLambda[simpleTags[expr], "Unique"], vars},
	If[lambda === expr, Return[expr]];
	vars = Cases[lambda, Interpretation["\[Lambda]" | Style["\[Lambda]", ___], tag_] :> tag, All, Heads -> True];
	lambda /. MapThread[
		With[{sym = Unevaluated @@ #2}, #1 :> sym] &,
		{vars, PadRight[Replace[symbols, "Alphabet" | Automatic -> {}], Length[vars], MakeExpression /@ AlphabetString[Range[Length[vars]]]]}
	]
]

TagLambda[expr_, "Minimal", symbols_] := simpleTags[expr] /. lambda : $LambdaHead[_] :> TagLambda[lambda, symbols]

TagLambda[expr_, "Simple"] := TagLambda[expr] //. Interpretation[x_, Interpretation[y_, _]] :> Interpretation[x, y]

TagLambda[expr_, form_String] := TagLambda[simpleTags[expr], "Minimal", Replace[form, "Minimal" -> "Alphabet"]]

TagLambda[expr_] := TagLambda[simpleTags[expr], "Alphabet"]

ResourceFunction["AddCodeCompletion"]["TagLambda"][None, {"Alphabet", "Unique", "Minimal", "Simple"}]


UntagLambda[expr_] := expr /. {Interpretation["\[Lambda]", _] :> $Lambda, Interpretation[x_, _] :> x,  l : $Lambda[_, _] :> FunctionLambda[l]}


LambdaFunction[expr_, head_ : Identity] := head @@ (Hold[Evaluate @ TagLambda[expr]] //. {Interpretation["\[Lambda]", x_][body_] :> Function[x, body], Interpretation[_Integer, x_] :> x})


FunctionLambda[expr_, vars_Association : <||>] := Replace[Unevaluated[expr], {
	_Interpretation | _Integer -> expr,
	Style[($LambdaHead | Function), style___][Style[HoldForm[var_] | var_, ___], body_][x_] :> Interpretation[Style["\[Lambda]", style], var][FunctionLambda[Unevaluated[body], Prepend[vars + 1, HoldForm[var] -> 1]]][FunctionLambda[Unevaluated[x], vars]],
	Style[($LambdaHead | Function), style___][Style[HoldForm[var_] | var_, ___], body_] :> Interpretation[Style["\[Lambda]", style], var][FunctionLambda[Unevaluated[body], Prepend[vars + 1, HoldForm[var] -> 1]]],
	($LambdaHead | Function)[HoldForm[var_] | var_, body_][x_] :> Interpretation["\[Lambda]", var][FunctionLambda[Unevaluated[body], Prepend[vars + 1, HoldForm[var] -> 1]]][FunctionLambda[Unevaluated[x], vars]],
	($LambdaHead | Function)[HoldForm[var_] | var_, body_] :> Interpretation["\[Lambda]", var][FunctionLambda[Unevaluated[body], Prepend[vars + 1, HoldForm[var] -> 1]]],
	(f : Except[HoldForm])[x_] :> FunctionLambda[Unevaluated[f], vars][FunctionLambda[Unevaluated[x], vars]],
	HoldForm[var : Except[$LambdaHead]] | (var : Except[$LambdaHead]) :> Interpretation[Evaluate[Replace[HoldForm[var], vars]], var]
}]


LambdaDepths[expr_, depth_Integer : 0] := Replace[expr, {
	Interpretation["\[Lambda]", tag_][body_] :> (Sow[tag -> depth]; LambdaDepths[body, depth + 1]),
	f_[arg_] :> (LambdaDepths[f, depth]; LambdaDepths[arg, depth])
}]

LambdaPositions[expr_] := Block[{lambda = TagLambda[UntagLambda[expr]], lambdaPos, argPos, tags, argTags},
	lambdaPos = Position[lambda, Interpretation["\[Lambda]", _], Heads -> True];
	argPos = Position[lambda, Interpretation[_Integer, tag_], Heads -> True];
	tags = Extract[lambda, Append[2] /@ lambdaPos];
	argTags = Extract[lambda, Append[2] /@ argPos];
	AssociationThread[lambdaPos -> Lookup[GroupBy[Thread[argTags -> argPos], First -> Last], tags, {}]]
]

LambdaApplication[lambda_, ___] := lambda //. (f : Except[$LambdaPattern])[x_] :> Application[f, x]

LambdaForm[lambda_] := UntagLambda[lambda] /. $LambdaHead -> "\[Lambda]"

LambdaVariableForm[lambda_, ___] := TagLambda[lambda] //. {
	Interpretation[Style[l : $LambdaHead, style___], tag_][arg_] :> Style[l, style][Style[HoldForm[tag], style], arg],
	Interpretation[Style[_Integer, style___], tag_] :> Style[HoldForm[tag], style],
	Interpretation[l : $LambdaHead, tag_][arg_] :> l[HoldForm[tag], arg],
	Interpretation[_Integer, tag_] :> HoldForm[tag]
}

LambdaRightApplication[lambda_, sym_ : " @ ", ___] :=
	lambda //. (x : Except[$LambdaPattern | Row])[y_] :> Row[{x, sym, y}] //.
		Row[{prefix : Except[sym] ..., Row[{a__, sym, b__}], c__}] :> Row[{prefix, "(", a, sym, b, ")", c}]


LambdaBrackets[lambda_, ___] := RawBoxes[ToBoxes[LambdaApplication[lambda] /. $LambdaHead -> "\[InvisibleSpace]"] /. "\[Application]" -> "\[InvisibleSpace]"]

LambdaDepthForm[expr_] := With[{lambda = TagLambda[expr]}, {lambdas = Cases[lambda, Interpretation["\[Lambda]", _], All, Heads -> True]},
	lambda /. MapThread[x : #1 | ReplacePart[#1, 1 -> _Integer] :> Nest[UnderBar,x,  #2] &, {lambdas, Range[Length[lambdas]]}]
]

lambdaStringVariables[lambda_] := lambda //. {
   	Interpretation[$LambdaHead, var_][body_] :> StringTemplate["(\[Lambda]``.``)"][ToString[Unevaluated[var]], lambdaStringVariables[body]],
	Interpretation[_, var_] :> ToString[Unevaluated[var]],
	f_[x_] :> Function[StringTemplate[If[StringEndsQ[#1, ")"] || StringStartsQ[#2, "("], "(````)", "(``\[InvisibleSpace]``)"]][##]][lambdaStringVariables[f], lambdaStringVariables[x]]
}

lambdaStringIndices[lambda_] := lambda //. {
   	$LambdaHead[body_] :> StringTemplate["(\[Lambda]\[InvisibleSpace]``)"][lambdaStringIndices[body]],
	f_[x_] :> StringTemplate["(``\[InvisibleSpace]``)"][lambdaStringIndices[f], lambdaStringIndices[x]]
}

LambdaString[lambda_, "Indices"] := lambdaStringIndices[UntagLambda[lambda]]
LambdaString[lambda_, _ : "Variables"] := lambdaStringVariables[TagLambda[lambda]]
LambdaString[lambda_, "Brackets"] := StringReplace[ToString[DisplayForm[ToBoxes[LambdaBrackets[lambda]]]], WhitespaceCharacter .. -> "\[InvisibleSpace]"]

ResourceFunction["AddCodeCompletion"]["LambdaString"][None, {"Variables", "Indices", "Brackets"}]


BalancedParenthesesQ[str_] := FixedPoint[StringDelete["()"], StringDelete[str, Except["(" | ")"]]] === ""

ParseVariableLambda[str_String, vars_Association : <||>] := First @ StringCases[str, {
	WhitespaceCharacter ... ~~ "\[Lambda]" ~~ WhitespaceCharacter ... ~~ args : Repeated[WordCharacter .. ~~ WhitespaceCharacter ...] ~~ "." ~~ WhitespaceCharacter ... ~~ body__ :>
		With[{argVars = Reverse @ StringCases[args, WordCharacter ..]}, {len = Length[argVars]},
			Fold[
				ReverseApplied[Construct],
				ParseVariableLambda[body, <|vars + len, Thread[argVars -> Range[len]]|>],
				Interpretation["\[Lambda]", #] & /@ argVars
			]
		],
	f__ ~~ WhitespaceCharacter ... ~~ x__ /; ! StringMatchQ[x, WhitespaceCharacter ..] &&
		! StringEndsQ[f, ("\[Lambda]" | ".") ~~ WhitespaceCharacter ...] && ! StringStartsQ[x, "."] && ! StringEndsQ[x, ("\[Lambda]" | ".") ~~ WhitespaceCharacter ...] &&
		BalancedParenthesesQ[f] && BalancedParenthesesQ[x] :> ParseVariableLambda[f, vars][ParseVariableLambda[x, vars]],
	"(" ~~ term__ ? BalancedParenthesesQ ~~ ")" :> ParseVariableLambda[term, vars],
	var : WordCharacter .. :> Interpretation[Evaluate[Replace[var, vars]], var]
}]

ParseIndexLambda[str_String, depth_Integer : 0] := First[StringCases[str, {
	WhitespaceCharacter ... ~~ "\[Lambda]" ~~ WhitespaceCharacter ... ~~ body__ ~~ WhitespaceCharacter ... :> $Lambda[ParseIndexLambda[body, depth + 1]],
	WhitespaceCharacter ... ~~ "(" ~~ term__ ? BalancedParenthesesQ ~~ ")" ~~ WhitespaceCharacter ... :> ParseIndexLambda[term, depth],
	f__ ~~ (WhitespaceCharacter | "(") ..  ~~ x__ /; BalancedParenthesesQ[f] && BalancedParenthesesQ[x] :> ParseIndexLambda[f, depth][ParseIndexLambda[x, depth]],
	WhitespaceCharacter ... ~~ var : DigitCharacter .. ~~ WhitespaceCharacter ... :> With[{x = Interpreter["Integer"][var]},
		If[StringLength[var] > 1 && x > depth, Fold[Construct, IntegerDigits[x]], x]
	]
}], StringTrim[str]]

ParseLambda[str_String, form_String : "Variables"] := Switch[form,
	"Variables",
	ParseVariableLambda[str],
	"Indices",
	ParseIndexLambda[str],
	"Brackets" | "BracketParens",
	ParseIndexLambda[StringReplace[str, {"[" -> "(\[Lambda]", "]" -> ")"}]],
	_,
	Missing[form]
]

ResourceFunction["AddCodeCompletion"]["ParseLambda"][None, {"Variables", "Indices", "Brackets"}]


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

Options[ColorizeLambda] = Options[ColorizeTaggedLambda] = {ColorFunction -> $DefaultColorFunction}

ColorizeTaggedLambda[lambda_, OptionsPattern[]] := With[{
	tags = Cases[lambda, Interpretation["\[Lambda]", tag_] :> HoldPattern[tag], All, Heads -> True],
	colorFunction = OptionValue[ColorFunction]
},
	lambda /. MapThread[Interpretation[e_, tag : #1] :> Interpretation[Style[e, Bold, #2], tag] &, {tags, colorFunction /@ Range[Length[tags]]}]
]

ColorizeLambda[expr_, args___] := ColorizeTaggedLambda[TagLambda[expr], args]

UncolorizeLambda[expr_] := expr /. Style[e_, ___] :> e


LambdaTag[Interpretation["\[Lambda]" | Style["\[Lambda]", ___], tag_]] := HoldForm[tag]
LambdaTag[head_[_]] := LambdaTag[head]
LambdaTag[_] := None

LambdaTags[expr_] := Union @ Cases[expr, Interpretation["\[Lambda]" | Style["\[Lambda]", ___], tag_] :> tag, All, Heads -> True]

untagTerms[Interpretation[e_, _ -> x_]] := untagTerms[Interpretation[e, x]]
untagTerms[f_[x_]] := untagTerms[f][untagTerms[x]]
untagTerms[e_] := e

LambdaUntag[e_] := untagTerms[e]


LambdaRow[Interpretation["\[Lambda]", tag_][body_], depth_ : 0] := {{$Lambda[HoldForm[tag]] -> depth, Splice[LambdaRow[body, depth + 1]]}}
LambdaRow[Interpretation[i_Integer, tag_], ___] := {i -> HoldForm[tag]}
LambdaRow[(f : Except[Interpretation["\[Lambda]", _]])[(g : Except[Interpretation["\[Lambda]", _]])[x_]], depth_ : 0] := Append[LambdaRow[f, depth], LambdaRow[g[x], depth]]
LambdaRow[f_[x_], depth_ : 0] := Join[LambdaRow[f, depth], LambdaRow[x, depth]]
LambdaRow[x_, ___] := {x}


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

$LambdaResults = CloudExpression["https://www.wolframcloud.com/obj/nikm/CloudExpression/LambdaResults"]


End[]

EndPackage[]
