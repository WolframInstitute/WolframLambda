BeginPackage["Wolfram`Lambda`"]

ClearAll[
    LambdaSmiles,
    LambdaDiagram,
    LambdaTreeDiagram,

    BetaReduceStepPlot,
    BetaReduceChain,

    LambdaArrayPlot,
    LambdaDepthArrayPlot,
    LambdaDepthArrayPlot3D
]

Begin["`Private`"]


Options[LambdaSmiles] = Join[
	{"Height" -> 3, "Spacing" -> 1, "StandardForm" -> True, "Arguments" -> True, "Arrow" -> False, "Tick" -> True, "Colored" -> All, ColorFunction -> $DefaultColorFunction},
	Options[Style], Options[Graphics]
];
LambdaSmiles[lambda_, opts : OptionsPattern[]] := Block[{
	row = LambdaRow[TagLambda[lambda]],
	lambdaPos, varPos, argPos, lambdas, maxDepth, vars, args, colors, varColors, termColors, arrows,
	height = OptionValue["Height"], spacing = OptionValue["Spacing"],
	argQ = TrueQ[OptionValue["Arguments"]],
	tickQ = TrueQ[OptionValue["Tick"]],
	colored = OptionValue["Colored"],
	colorFunction = OptionValue[ColorFunction],
	styleOpts = FilterRules[{opts, FontSize -> 12.5}, Options[Style]]
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
	lambdaPos = Position[row, $LambdaHead[_] -> _, {1}, Heads -> False];
	varPos = Position[row, _Integer -> _, {1}, Heads -> False];
	argPos = Position[row, "Arg"[_] -> _, {1}, Heads -> False];
	lambdas = AssociationThread[#[[All, 1, 1]], Thread[First /@ lambdaPos -> #[[All, 2]]]] & @ Extract[row, lambdaPos];
	args = AssociationThread[#[[All, 1, 1]], Thread[First /@ argPos -> #[[All, 2]]]] & @ Extract[row, argPos];
	vars = Extract[row, varPos];
	colors = Association @ MapIndexed[#1[[1, 1]] -> colorFunction[#2[[1]]] &, Extract[row, lambdaPos]];
	varColors = termColors = $Black & /@ colors;
	Switch[colored,
		True, colors = Function[colorFunction[1]] /@ colors,
		All, termColors = varColors = colors,
		Automatic, termColors = colors,
		False | None, colors = varColors
	];
	row = row //
		MapAt[Style["\[Lambda]", Lookup[termColors, #[[1, 1]], $Gray]] &, lambdaPos] //
		MapAt[Style[#[[If[argQ, 2, 1]]], Lookup[termColors, #[[2]], $Gray]] &, varPos] //
		MapAt[Style[#[[1, 1]], Lookup[varColors, #[[1, 1]], $Gray]] &, argPos];
	
	arrows = MapThread[
		With[{dh = height * Ceiling[#1[[1]] / 2], sign = (-1) ^ Boole[EvenQ[#1[[1]]]], h = lambdas[#1[[2]]], l = lambdas[#1[[2]]]},
			If[	MissingQ[l] || MissingQ[h],
				Nothing,
				{
					colors[#1[[2]]],
					Arrowheads[Replace[OptionValue["Arrow"], {False | None -> 0, True | Automatic -> Small}]],
					Arrow[Threaded[{spacing, sign}] * {{#2, height}, {#2, height + dh / (l[[2]] + 1)}, {h[[1]], height + dh / (l[[2]] + 1)}, {h[[1]], height}}],
					If[argQ && tickQ, Line[Threaded[{spacing, sign}] * {{h[[1]] + 2, height + dh / (l[[2]] + 1)}, {h[[1]] + 2, height + 1 / 2 dh / (l[[2]] + 1)}}], Nothing]
				}
			]
		] &,
		{vars, First /@ varPos}
	];
	Graphics[{
		MapIndexed[Inset[Text @ Style[#1, styleOpts], {spacing * #2[[1]], 0}] &, row],
		arrows
	},
		FilterRules[{opts}, Options[Graphics]],
		AspectRatio -> height / (Length[row] * spacing)
	]
]

{$Black, $White, $Red, $Green, $Blue, $Yellow, $Gray} = If[$VersionNumber >= 14.3,
	{
		LightDarkSwitched[Black, White], LightDarkSwitched[White, Black],
		StandardRed, StandardGreen, StandardBlue, StandardYellow,
		LightDarkSwitched[Darker[StandardGray], Lighter[StandardGray]]
	},
	{White, Black, Red, Green, Blue, LightYellow, Gray}
]


Options[BetaReduceStepPlot] = Join[
	{
		"Width" -> .4, "ShowInput" -> True, "ShowOutput" -> False, "ClipBounds" -> True, "TerminationLine" -> False,
		"Tooltips" -> False,
		ColorRules -> {"Input" -> StandardRed, "Output" -> StandardGreen}
	},
	Options[BetaReduceList],
	Options[ListStepPlot]
];


BetaReduceStepPlot[path_List -> positions_List, step : Right | Left | Center : Center, opts : OptionsPattern[]] /; Length[path] >= Length[positions] := Block[{
	width = OptionValue["Width"],
	showInputQ = TrueQ[OptionValue["ShowInput"]],
	showOutputQ = TrueQ[OptionValue["ShowOutput"]],
	clipBoundsQ = TrueQ[OptionValue["ClipBounds"]],
	terminationQ = TrueQ[OptionValue["TerminationLine"]],
	inputColor = Lookup[OptionValue[ColorRules], "Input"],
	outputColor = Lookup[OptionValue[ColorRules], "Output"],
	tooltip = Replace[OptionValue["Tooltips"], {False | None -> (#1 &), _ -> Tooltip}],
	len = Length[positions] + 1,
	xfn, yfn,
	columns
},
	{xfn, yfn} = Visualization`Utilities`ParseScalingFunctions[OptionValue["ScalingFunctions"], 2, ListStepPlot][[All, 1]];
	truncatedPath = Take[path, len];
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
						tooltip[
							Rectangle @@ Thread[{
								xfn @ If[ showOutputQ,
									{i + .25 - width / 2, i + .25 + width / 2},
									{i - width / 2, i + width / 2}
								],
								yfn @ Catenate[Lookup[PositionIndex[srcPos], srcSubPos]]
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
						tooltip[
							Rectangle @@ Thread[{
								xfn @ If[	showInputQ,
									{i + .75 - width / 2, i + .75 + width / 2},
									{i + 1 - width / 2, i + 1 + width / 2}
								],
								yfn @ Catenate[Lookup[PositionIndex[tgtPos], tgtSubPos]]
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
			Most[truncatedPath],
			Rest[truncatedPath],
			positions,
			Range[Length[positions]]
		}
	];
	ListStepPlot[
		If[ terminationQ && Length[path] > len,
			{MapIndexed[Append[#2, #1] &, columns[[All, 1]]], MapIndexed[Append[#2 + len, #1] &, LeafCount /@ Drop[path, len]]},
			columns[[All, 1]]
		],
		step,
		FilterRules[{opts}, Options[ListStepPlot]],
		PlotRange -> {{If[clipBoundsQ && ! showInputQ, 1.5, .5], Length[path] + If[clipBoundsQ && ! showOutputQ, -.66, .5]}, {1, All}},
		PlotRangePadding -> {{0, If[clipBoundsQ || Length[path] > len, 0, 1]}, {0, Scaled[.1]}},
		Epilog -> columns[[All, 2]],
		Filling -> {1 -> Axis},
		PlotStyle -> RGBColor[0.24, 0.6, 0.8],
		Frame -> True,
		AspectRatio -> .4
	]
]

BetaReduceStepPlot[lambda_, n : _Integer | _UpTo | Infinity : Infinity, step : Right | Left | Center : Center, opts : OptionsPattern[]] := Block[{
	positions, path
},
	positions = Catenate @ Reap[path = BetaReduceList[lambda, n, FilterRules[{opts}, Options[BetaReduceList]]], "Positions"][[2]];
	
	BetaReduceStepPlot[path -> Catenate[Most[positions]], step, opts, "ClipBounds" -> Last[positions, {}] =!= {}]
]


Options[BetaReduceChain] = Join[Options[BetaReduceListPositions], Options[Framed], Options[Style], Options[Column]]

BetaReduceChain[args___, opts : OptionsPattern[]] := With[{
	reduceOpts = FilterRules[{opts}, Options[BetaReduceListPositions]],
	frameOpts = FilterRules[{opts, BaseStyle -> FontColor -> Black, Background -> LightRed, FrameStyle -> None, FrameMargins -> 0}, Options[Framed]],
	styleOpts = FilterRules[{opts, FontSize -> 10}, FilterRules[Options[Style], Except[Options[Framed]]]],
	columnOpts = FilterRules[{opts, Spacings -> 0.2}, FilterRules[Options[Column], Except[Join[Options[Framed], Options[Style]]]]]
},
	Column[
		MapThread[Style[MapAt[Framed[#, frameOpts] &, #1, #2], styleOpts] &, BetaReduceListPositions[args, reduceOpts]],
		columnOpts
	] /. $Lambda -> "\[Lambda]"
]


ClearAll[lambdaArrayRow]
lambdaArrayRow[lambda_, depth_ : 0] :=
	Replace[lambda, {
		$LambdaHead :> {Sow[depth]; 0},
		{x_, xs__} :> Join[lambdaArrayRow[x, depth], Catenate[Join[Sow[depth + 1]; {-1}, lambdaArrayRow[#, depth + 1], Sow[depth + 1]; {-2}] & /@ {xs}]],
		x_ :> {Sow[depth]; x}
	}]
LambdaArrayRow[lambda_] := lambdaArrayRow @ LambdaRow[UntagLambda[lambda]]

LambdaArrayRowDepths[lambda_] := MapAt[First, Reap[LambdaArrayRow[lambda]], 2]

$ColorArrayColors = {0 -> Hue[0.87, 1, 1], -1 -> GrayLevel[.8], -2 -> GrayLevel[.5], -3 -> None, "MinVar" -> Hue[0.66, 1, 1.], "MaxVar" -> Hue[0.51, 1, 1]}

Options[LambdaArrayPlot] = Join[{
	"Labeled" -> False,
	ColorRules -> $ColorArrayColors
},
	Options[ArrayPlot]
]

LambdaArrayPlot[lambdas : {__}, max : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := Block[{rows, colorRules, plot},
	rows = Take[LambdaArrayRow /@ lambdas, All, UpTo[max]];
	colorRules = Flatten[{OptionValue[ColorRules], $ColorArrayColors}];
	plot = ArrayPlot[
		rows,
		ColorRules -> Append[
			colorRules,
			x_ :> Blend[Lookup[colorRules, {"MinVar", "MaxVar"}], Rescale[x, {1, Max[rows, 1]}]]
		],
		FilterRules[{opts}, Options[ArrayPlot]]
	];
	If[ TrueQ[OptionValue["Labeled"]],
		Show[
			plot,
			Graphics[
				MapIndexed[
					Style[Text[Replace[#1, {0 -> "\[Lambda]", -1 -> "[", -2 -> "]"}], {#2[[2]], #2[[1]]} - {0.5, 0.5}], Directive[White, 14]] &, 
					Reverse[rows],
					{2}
				]
			]
		],
		plot
	]
]

Options[LambdaDepthArrayPlot] = Join[{
	ColorRules -> $ColorArrayColors
},
	Options[ArrayPlot]
]

LambdaDepthArrayPlot[lambda_, max : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := Module[{row, heights, colorRules}, 
    {row, heights} = LambdaArrayRowDepths[lambda];
	{row, heights} = Take[#, UpTo[max]] & /@ {row, heights};
	colorRules = Flatten[{OptionValue[ColorRules], $ColorArrayColors}];
    ArrayPlot[
		Prepend[Table[MapThread[If[#2 >= i, #1, -3] &, {row, heights}], {i, 1, Max[heights]}], row],
      	FilterRules[{opts}, Options[ArrayPlot]],
		ColorRules -> Append[
			colorRules,
			x_ :> Blend[Lookup[colorRules, {"MinVar", "MaxVar"}], Rescale[x, {1, Max[row, 1]}]]
		],
	  	Mesh -> Automatic
	]
]

Options[LambdaDepthArrayPlot3D] = Join[{
	ColorRules -> $ColorArrayColors
},
	Options[ArrayPlot3D]
]

LambdaDepthArrayPlot3D[lambdas : {__}, max : _Integer | Automatic : Automatic, opts : OptionsPattern[]] := Block[{rows, heights, colorRules}, 
    {rows, heights} = Thread[LambdaArrayRowDepths /@ lambdas];
	colorRules = Flatten[{OptionValue[ColorRules], $ColorArrayColors}];
    ArrayPlot3D[
		Take[
			MapThread[
				Prepend[Table[MapThread[If[#2 >= i, #1, -3] &, {##}], {i, 1, Max[#2]}], #1] &,
				{rows, heights}
			],
			All, All, UpTo[Replace[max, Automatic :> Max[Length /@ rows]]]
		],
		FilterRules[{opts}, Options[ArrayPlot3D]], 
		ColorRules -> Append[
			colorRules,
			x_ :> Blend[Lookup[colorRules, {"MinVar", "MaxVar"}], Rescale[x, {1, Max[rows, 1]}]]
		],
		AspectRatio -> 1 / 4
	]
]



$LambdaDiagramColorRules = {
   	"Lambda" -> Replace["Lambda", $LambdaTreeColorRules],
   	"Application" | "LambdaApplication" -> Replace["Application", $LambdaTreeColorRules],
   	"Term" -> $Gray,
   	"Variable" | "FreeVariable" | "Constant" -> Replace["Variable", $LambdaTreeColorRules],
   	_ -> Opacity[1]
}

Options[LambdaDiagram] = Join[{
	"Extend" -> True, "Pad" -> True, "Dots" -> All, "Thick" -> False,
	"Labeled" -> False, "Colored" -> False,
	"Alternative" -> False,
	ColorRules -> Automatic,
	PlotInteractivity -> False
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


LambdaDiagram[expr_, opts : OptionsPattern[]] := Block[{
	interactiveQ = TrueQ[OptionValue[PlotInteractivity]],
	tooltip,
	makeTooltip = Function[{pos, type},
		type -> MapAt[Framed, {pos}] @ If[StringEndsQ[type, "Application"],
			MapAt[Style[#, $Blue] &, Append[pos, 1]] @* MapAt[Style[#, $Red] &, Append[pos, 0]],
			Identity
		] @ expr
	],
	lambda = TagLambda[UntagLambda[expr]], depths, lines, dots,
	colorRules = Replace[OptionValue[ColorRules], {Automatic -> $LambdaDiagramColorRules, rules_  :> Join[Cases[Flatten[{rules}], _Rule | _RuleDelayed], $LambdaDiagramColorRules]}],
	lineFunction, pointFunction, labelFunction,
	alternative = TrueQ[OptionValue["Alternative"]],
	labeled = OptionValue["Labeled"]
},
	tooltip = If[TrueQ[OptionValue[PlotInteractivity]], Tooltip, #1 &];
	With[{typeColorFunction =
		If[ TrueQ[OptionValue["Colored"]],
			Replace[colorRules],
			Function[$Gray]
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
		Function[{Replace[#2, colorRules], Disk[#1, 1 / 8]}]
	];
	labelFunction = Switch[labeled,
		True, 
			Function[{line, pos, type},
				Replace[{line, type}, {
					{{{x1_, x2_}, y_}, "Lambda"} :> {Text["\[Lambda]", {x1 - 1/8, y}]},
					{_, "Term" | "Application" | "LambdaApplication"} :> Nothing,
					{{x_, {y1_, y2_}}, _} :> If[! alternative && y1 == y2, Nothing, Text[Extract[expr, {pos}][[1]], If[alternative && y1 == y2, {x, y1 - 1/8}, {x - 1/8, y1 - 1/2}]]]
				}]
			],
		All | Full | Automatic, With[{
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
			Cases[lines, Labeled[{{x_, _}, y_}, pos_ -> type_] :> tooltip[pointFunction[{x, y}, type], makeTooltip[pos, type]]]
		},
		True | Automatic,
		{
			Cases[lines, Labeled[{{x_, _}, y_}, pos_ -> "Lambda"] :> tooltip[pointFunction[{x, y}, "Lambda"], makeTooltip[pos, "Lambda"]]]
		},
		False | None,
		Nothing
	];
	If[ interactiveQ
		,
		With[{boxId = Unique[Symbol["LambdaDiagram"]]},
			DynamicModule[{style = ConstantArray[AbsoluteThickness[1.5], Length[lines]]},
				Graphics[{
					MapIndexed[With[{i = #2[[1]], f = lineFunction},
						Replace[#1, Labeled[line_, pos_ -> type_] :> With[{
							primitive = {
								tooltip[Dynamic @ {If[type === "LambdaApplication", Dashed, Nothing], style[[i]], f[line, pos, type]}, makeTooltip[pos, type]],
								labelFunction[line, pos, type]
							}
						},
							EventHandler[primitive,
								{
									"MouseEntered" :> If[ListQ[style], style[[i]] = AbsoluteThickness[3]],
									"MouseExited" :> If[ListQ[style], style[[i]] = AbsoluteThickness[1.5]],
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
				Labeled[line_, pos_ -> type_] :> tooltip[{AbsoluteThickness[1.5], lineFunction[line, pos, type]}, makeTooltip[pos, type]],
				1
			],
			dots,
			Replace[lines,
				Labeled[line_, pos_ -> type_] :> labelFunction[line, pos, type],
				1
			]
		},
			FilterRules[{opts}, Options[Graphics]]
		]
	]
]


Options[LambdaTreeDiagram] = Join[Options[LambdaDiagram], Options[LambdaTree]]

LambdaTreeDiagram[lambda_, opts : OptionsPattern[]] := Block[{diagram = 
    LambdaDiagram[lambda, FilterRules[{opts}, Options[LambdaDiagram]], "Dots" -> False],
	alternativeQ = TrueQ[OptionValue["Alternative"]],
	tree, graph, vertices,
	treePositionMap, pos1, pos2, permutation, coords
},
	tree = LambdaTree[lambda, FilterRules[{opts}, Options[LambdaTree]]];
	graph = Trees`TreeVisualizationGraph[tree];
	pos1 = TreePosition[tree, _];
	pos2 = TreePosition[tree, _, TreeTraversalOrder -> "TopDown"];
	permutation = FindPermutation[pos1, pos2];
	treePositionMap = AssociationThread[TreePosition[ExpressionTree[lambda, "Subexpressions", "Heads" -> True], _Integer | _[_]] - 1, pos1];
	vertices = VertexList[tree][[All, 2]];
	coords = Lookup[
		Cases[diagram, 
			Tooltip[{___, l_Line} | l_Line, (type_ -> expr_)] :> 
				With[{pos = FirstPosition[expr, _Framed]}, 
					Lookup[treePositionMap, Key[pos]] -> 
						With[{len = RegionMeasure[l, 1]}, 
							Switch[type,
								"Variable", 
									If[len == 0 && alternativeQ, RegionCentroid[l] + {0, .1}, l[[1, 1]] - {0, 1/2}],
								"Lambda",
									If[len == 0, {0, 0}, RegionCentroid[l] + {-len/2, 0}],
								_,
									RegionCentroid[l]
							]
						]
				],
			All
		],
		Permute[vertices, permutation]
	];
	Show[
		diagram, 
		Graph[graph, VertexCoordinates -> Thread[VertexList[graph] -> coords]]
	]
]


End[]

EndPackage[]