BeginPackage["Wolfram`Lambda`"]

ClearAll[
    LambdaTree,
    LambdaMinimalTree,
    HighlightLambdaTree,
    BetaReduceTreeList,
    LambdaGraph,
    LambdaLoopbackGraph,
    LambdaSingleWayCausalGraph,
    LambdaCausalGraph,
    LambdaCausalEvolutionGraph
]

Begin["`Private`"]

Options[LambdaTree] = Join[{
	"ApplicationLabel" -> None, "VariableLabels" -> False, "HighlightRedex" -> False,
	ColorFunction -> $DefaultColorFunction,
	ColorRules -> $LambdaTreeColorRules,
	PlotTheme -> Automatic
},
	Options[Tree]
]

lambdaTree[(l : $LambdaPattern)[body_], opts___] := Tree[l, {lambdaTree[body]}, opts]
lambdaTree[f_[x_], opts___] := Tree[Application, {lambdaTree[f], lambdaTree[x]}, opts]
lambdaTree[expr_, opts___] := Tree[expr, None, opts]


LambdaTree[lambda_, opts : OptionsPattern[]] := Block[{
	taggedLambda,
	theme = OptionValue[PlotTheme],
	colorRules = Join[Cases[Flatten[{OptionValue[ColorRules]}], _Rule | _RuleDelayed], $LambdaTreeColorRules],
	appLabel = OptionValue["ApplicationLabel"],
	variablesQ = TrueQ[OptionValue["VariableLabels"]],
	highlightRedex = Replace[OptionValue["HighlightRedex"], Automatic | True -> StandardRed]
},
	taggedLambda = FunctionLambda[lambda];
	If[taggedLambda =!= lambda, variablesQ = True, taggedLambda = TagLambda[taggedLambda]];
	Block[{tree, colors = {}, lambdaColor, appColor, leaveColor, applicationPositions, redexPositions},
		lambdaColor = Replace["Lambda", colorRules];
		appColor = Replace["Application", colorRules];
		leaveColor = Replace[If[variablesQ, "Variable", "Index"], colorRules];
		tree = lambdaTree[
			ColorizeLambda[taggedLambda, FilterRules[{opts}, Options[ColorizeLambda]]] /.
				Interpretation[Style[e_, style__], tag_] :>
					(If[e === "\[Lambda]", AppendTo[colors, TreeCases[Interpretation[_, tag]] -> Directive[style]]]; Interpretation[e, tag])
			,
			FilterRules[{opts}, Options[Tree]],
			ParentEdgeStyle -> {All -> Replace["Edges", colorRules]},
			TreeElementLabelStyle -> All -> Replace["BlackLambda", colorRules],
			
  			TreeElementSize -> Switch[theme,
				"Minimal" | "MinimalColored",
					All -> {"Scaled", .015},
				_,
					All -> Medium
			],
			TreeElementShape -> Switch[theme,
				"Minimal",
					MapThread[
						#1 -> Graphics[{#2, Rectangle[{0, 0}, {0.75, 1}]}] &, 
						{
							{TreeCases[$LambdaPattern], "Leaves"},
							{lambdaColor, leaveColor}
						}
					]
				,
				"MinimalColored", {
					Splice @ MapAt[Graphics[{#[[2]], EdgeForm[Darker[#[[2]], .1]], Rectangle[{0, 0}, {0.75, 1}]}] &, colors, {All, 2}]
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
					TreeCases[$LambdaPattern] -> If[variablesQ, Function[Subscript["\[Lambda]", Replace[#, Interpretation[_, tag_] :> HoldForm[tag]]]], Function["\[Lambda]"]],
					"Leaves" -> If[variablesQ, Replace[Interpretation[_, tag_] :> HoldForm[tag]], Identity],
					TreeCases[Application] -> Automatic
				}
			]
		];
		applicationPositions = TreePosition[tree, Application, All];
		redexPositions = If[ ! MatchQ[highlightRedex, None | False],
			Catenate @ Reap[
				TreeScan[
					Replace[{#1, #2}, {Application, {$LambdaPattern, _}} :> Sow[#3]] &,
					tree,
					All -> {"Data", "OriginalChildrenData", "Position"}
				]
			][[2]],
			{}
		];
		applicationPositions = Complement[applicationPositions, redexPositions];
		Tree[
			tree,
			TreeElementStyle ->
				Join[
					Thread[applicationPositions -> appColor],
					Thread[redexPositions -> highlightRedex],
					Switch[theme,
						"Colored" | "MinimalColored",
							colors,
						_,
							{
								TreeCases[$LambdaPattern] -> Replace["Lambda", colorRules],
								"Leaves" -> leaveColor
							}
					]
				]
				,
			Switch[theme, "Minimal" | "MinimalColored",
				TreeElementShape -> Join[
					Thread[redexPositions -> Graphics[{highlightRedex, Disk[]}]],
					Thread[applicationPositions -> Graphics[{appColor, Disk[]}]]
				],
				_,
				TreeElementShapeFunction -> Join[
					Thread[redexPositions -> Trees`$TreeVertexShapeFunction[Null, highlightRedex, False]],
					Thread[applicationPositions -> Trees`$TreeVertexShapeFunction[Null, appColor, False]]
				]
			]
		]
	]
]

LambdaMinimalTree[lambda_, opts___] := LambdaTree[lambda, opts, PlotTheme -> "Minimal", ImageSize -> {Automatic, UpTo[100]}]


LambdaTreePosition[expr_, pos : {___Integer}] := If[pos === {}, pos, 
  	With[{apos = FoldList[Append, {}, pos]}, 
		Table[
			If[ MatchQ[Extract[expr, {apos[[i]]}][[1]], $LambdaPattern[_]], 
				pos[[i]],
				pos[[i]] + 1
			],
			{i, Length[pos]}
		]
	]
]

LambdaTreePosition[lambda_, pos_List] := With[{expr = UntagLambda[FunctionLambda[lambda]]}, LambdaTreePosition[expr, #] & /@ pos]

Options[HighlightLambdaTree] = Join[{"HighlightStyle" -> StandardRed, Method -> "Edges"}, Options[LambdaTree]]

HighlightLambdaTree[lambda_, pos : (Automatic | {{___Integer} ...}) : Automatic, opts : OptionsPattern[]] := With[{
	positions = Replace[pos, Automatic :> BetaReducePositions[FunctionLambda[lambda], FilterRules[{opts}, Options[BetaReducePositions]]]],
	tree = LambdaTree[lambda, FilterRules[{opts}, Options[LambdaTree]]]
}, 
  	Tree[tree,
		Switch[
			OptionValue[Method],
			"Edges",
				ParentEdgeStyle -> Thread[Append[__] /@ LambdaTreePosition[lambda, positions] -> Directive[AbsoluteThickness[2], OptionValue["HighlightStyle"]]]
			,
			"Frames" | "Boxes", {
				Epilog -> With[{
					coords = TreeNodeCoordinates[tree]
				}, {
					coords = Cases[coords, ({_, Append[#, ___]} -> coord_) :> coord] & /@ LambdaTreePosition[lambda, positions]
				},
					{EdgeForm[OptionValue["HighlightStyle"]], FaceForm[None], Rectangle @@ ({{-.25, -.25}, {.25, .25}} + CoordinateBoundingBox[#]) & /@ coords}
				],
				PlotRangePadding -> Scaled[.1]
			}
			,
			"Stripes",
				Prolog -> Block[{g},
					g = LambdaGraph[tree, "Merge" -> False, GraphLayout -> "LayeredDigraphEmbedding"];
					MapIndexed[
						With[{vars = VertexList[g, {ReplacePart[#, 1 -> _Integer], _}], shift = #2[[1]]},
							If[ Length[vars] == 0, Nothing,
                                Subgraph[g, Union[FindShortestPath[g, #, All] /@ vars]] //
                                    First @ GraphPlot[#,
                                        EdgeStyle -> $LambdaStyles["LoopbackEdges"],
                                        VertexShapeFunction -> None,
                                        VertexCoordinates -> Thread[VertexList[#] -> GraphEmbedding[#] + Threaded[{- .1 * shift, 0}]]
                                    ] &
                            ]
								
						] &,
						TreeData /@ TreeCases[tree, Interpretation["\[Lambda]", _]]
					]
				]
			,
			_,
				Unevaluated[]
		]
	]
]


Options[BetaReduceTreeList] = Join[Options[BetaReduceList], Options[HighlightLambdaTree]]

BetaReduceTreeList[lambda_, args___, opts : OptionsPattern[]] := With[{treeOpts = FilterRules[{opts}, Options[HighlightLambdaTree]]},
	MapThread[HighlightLambdaTree[##, treeOpts, Method -> None] &, BetaReduceListPositions[lambda, args, FilterRules[{opts}, Options[BetaReduceListPositions]]]]
]


Options[LambdaGraph] = Join[{"Merge" -> True}, Options[LambdaTree], Options[Graph]]

LambdaGraph[lambda_, opts : OptionsPattern[]] :=
	LambdaGraph[LambdaTree[TagLambda[lambda], "VariableLabels" -> True, FilterRules[{opts}, Options[LambdaTree]]], opts]

LambdaGraph[tree_Tree, opts : OptionsPattern[]] := Block[{
	g, coords, rules
},
	g = Trees`TreeVisualizationGraph[tree];
	coords = TreeNodeCoordinates[tree];
	g = VertexReplace[g, Thread[VertexList[g] -> coords[[All, 1]]]];
	rules = {
		{l : Interpretation["\[Lambda]", _], _} :> l,
		If[TrueQ[OptionValue["Merge"]], {Interpretation[_, tag_], _} :> HoldForm[tag], Nothing]
	};
	VertexReplace[
		g,
		rules
		,
		FilterRules[{opts}, Options[Graph]],
		VertexCoordinates -> MapAt[Replace[rules], coords, {All, 1}],
		FormatType -> StandardForm,
		PerformanceGoal -> "Quality"
		GraphLayout -> "SymmetricLayeredEmbedding"
	]
]


TreeNodes[tree_] := With[{pos = TreePosition[tree, _, TreeTraversalOrder -> "TopDown"]},
	Thread[{TreeExtract[tree, pos, TreeData], pos}]
]

TreeNodeCoordinates[tree_] := Thread[
	TreeNodes[tree] ->
	GraphEmbedding[Trees`TreeVisualizationGraph[tree]]
]

Options[LambdaLoopbackGraph] = Join[Options[LambdaTree], Options[Graph]]

LambdaLoopbackGraph[lambda_, opts : OptionsPattern[]] :=
	LambdaLoopbackGraph[LambdaTree[TagLambda[lambda], FilterRules[{opts}, Options[LambdaTree]], TreeElementLabelStyle -> "Leaves" -> Transparent], opts]

LambdaLoopbackGraph[tree_Tree, opts : OptionsPattern[]] := Block[{
	g, coords, rules
},
	g = Trees`TreeVisualizationGraph[tree];
	coords = MapAt[Replace[{l : Interpretation["\[Lambda]", _], _} :> l], TreeNodeCoordinates[tree], {All, 1}];
	EdgeAdd[
		VertexReplace[g, Thread[VertexList[g] -> coords[[All, 1]]]],
		DirectedEdge[#, ReplacePart[#[[1]], 1 -> "\[Lambda]"]] & /@ Thread[{TreeExtract[tree, #, TreeData], #}] & @ TreePosition[tree, _, "Leaves"],
		FilterRules[{opts}, Options[Graph]],
		EdgeShapeFunction -> {
			_ -> Trees`$TreeEdgeShapeFunction,
			DirectedEdge[{_Interpretation, _}, _] ->
				( BSplineCurve[Insert[{First[#1], Last[#1]}, (Total @ {First[#1], Last[#1]}) / 2 + {If[#1[[1, 1]] > #1[[-1, 1]], 1, -1], 0}, 2]] &)
		},
		EdgeStyle -> {
			DirectedEdge[{_Interpretation, _}, _] -> $LambdaStyles["LoopbackEdges"]
		},
		VertexCoordinates -> coords,
		FormatType -> StandardForm,
		PerformanceGoal -> "Quality"
		GraphLayout -> "SymmetricLayeredEmbedding"
	]
]



EventDestroyedCreatedTags[DirectedEdge[lam1_, lam2_, t_ -> pos_]] := With[{
	tags1 = LambdaTags[Extract[lam1, {pos}][[1]]],
	tags2 = LambdaTags[Extract[lam2, {pos}][[1]]]
},
	{Complement[tags1, tags2], Complement[tags2, tags1]}
]

LaterEventActiveQ[DirectedEdge[lam1_, _, _], DirectedEdge[lam2_, _, _ -> pos_]] := ! FreeQ[lam1, Extract[lam2, {pos}][[1, 0, 0]][_][_]]


Options[LambdaSingleWayCausalGraph] = Join[{Method -> Automatic}, Options[Graph]]

LambdaSingleWayCausalGraph[events_List, opts : OptionsPattern[]] :=
If[ events === {},
	Graph[{}, opts]
	,
	With[{dependencyOnlyQ = MatchQ[OptionValue[Method], "DependencyOnly"]},
		TransitiveReductionGraph[
			EdgeDelete[
				TransitiveClosureGraph @ Graph[events, DirectedEdge @@@ Partition[events, 2, 1]],
				DirectedEdge[event1_, event2_] /; With[{
					created = EventDestroyedCreatedTags[event1][[2]],
					destroyed = EventDestroyedCreatedTags[event2][[1]]
				}, (dependencyOnlyQ || LaterEventActiveQ[event1, event2]) && AllTrue[destroyed, x |-> AllTrue[created, FreeQ[x, #] &]]]
			]
			,
			FilterRules[{opts}, Options[Graph]],
			VertexStyle -> ResourceFunction["WolframPhysicsProjectStyleData"]["CausalGraph", "VertexStyle"],
			VertexLabels -> DirectedEdge[lam1_, lam2_, t_ -> pos_]:> Row[{t, ":", Row[pos], ":", LambdaTag @ LambdaUntag[Extract[lam1, {pos}][[1]]]}],
			EdgeStyle -> LightDarkSwitched[ResourceFunction["WolframPhysicsProjectStyleData"]["CausalGraph", "EdgeStyle"], StandardRed],
			VertexLabels -> Placed[Automatic, Tooltip],
			GraphLayout -> "LayeredDigraphEmbedding"
		]
	]
]


Options[eventVertexShapeFunction] = {
	"ShowIndices" -> False,  "ShowPositions" -> False, "ShowExpressions" -> True,
	"EventColumnOptions" -> {Alignment -> Center, Background -> {Opacity[0.8, Hue[0.14, 0.34, 1]], RGBColor[0.9997869066419748, 0.8347064306285127, 0.26312831039590046`]}, BaseStyle -> Directive[Opacity[1], Black]},
	"EventStyleOptions" -> {FontColor -> Directive[Opacity[1], Black]},
	"EventFrameOptions" -> {Background -> Directive[Opacity[0.2], Hue[0.14, 0.34, 1]], FrameMargins -> {{2, 2}, {0, 0}}, FrameStyle -> Hue[0.09, 1, 0.91, .3], RoundingRadius -> 2},
	"Variables" -> False
};

eventVertexShapeFunction[opts : OptionsPattern[]] := With[{
	colOpts = {OptionValue["EventColumnOptions"], OptionValue[Options[eventVertexShapeFunction], "EventColumnOptions"]},
	eventOpts = {OptionValue["EventStyleOptions"], OptionValue[Options[eventVertexShapeFunction], "EventStyleOptions"]},
	frameOpts = {OptionValue["EventFrameOptions"], OptionValue[Options[eventVertexShapeFunction], "EventFrameOptions"]},
	showIndex = If[TrueQ[OptionValue["ShowIndices"]], Identity, Nothing &],
	showPosition = If[TrueQ[OptionValue["ShowPositions"]], Identity, Nothing &],
	formFunction = If[TrueQ[OptionValue["Variables"]], LambdaVariableForm, Identity],
	getIndex = Replace[{(index_ -> _) :> index, _ -> Missing[]}],
	getPos = Replace[(_ -> pos_) | pos_ :> pos]
},
{
	showExpression = If[TrueQ[OptionValue["ShowExpressions"]],
		Function[Text @ formFunction @ ReplacePart[#1, {#2} -> Column[formFunction /@ #3, colOpts]]],
		(Column[Text @ formFunction[#3], colOpts] &)
	]
},
	Function[
		Replace[#2, DirectedEdge[from_, to_, tag_] :> With[{index = getIndex[tag], pos = getPos[tag]},
			Inset[
				Framed[
					Row[{
						If[# === {}, Nothing, Column[{Splice[#], SpanFromAbove}, Alignment -> Top]] & @ {showIndex[index], showPosition[pos]},
						Style[
							showExpression[from, pos, {Extract[from, {pos}][[1]], Extract[to, {pos}][[1]]}]
							,
							200 * #3,
							eventOpts
						]},
						Spacer[1]
					],
					frameOpts
				]
				, #1
			]
		]
		]
	]
]


Options[LambdaCausalGraph] = Join[{"Variables" -> False}, Options[eventVertexShapeFunction], Options[LambdaPathEvents], Options[LambdaSingleWayCausalGraph]]

LambdaCausalGraph[lambda : Except[_List], args : Except[OptionsPattern[]] ..., opts : OptionsPattern[]] :=
	LambdaCausalGraph[LambdaPathEvents[lambda, args, FilterRules[{opts}, Options[LambdaPathEvents]]], opts]

LambdaCausalGraph[{}, ___] := Graph[{}, VertexLabels -> None]

LambdaCausalGraph[pathEvents : {__}, opts : OptionsPattern[]] :=
	VertexReplace[
		LambdaSingleWayCausalGraph[pathEvents, FilterRules[{opts}, FilterRules[Options[LambdaSingleWayCausalGraph], Except[Options[Graph]]]]],
		DirectedEdge[from_, to_, tag_] :> (DirectedEdge[untagTerms[from], untagTerms[to], tag]),
		FilterRules[{opts}, Options[Graph]],
		VertexLabels -> None,
		VertexShapeFunction -> _DirectedEdge -> eventVertexShapeFunction[FilterRules[{opts}, Options[eventVertexShapeFunction]]],
		GraphLayout -> "LayeredDigraphEmbedding",
		FormatType -> StandardForm,
		PerformanceGoal -> "Quality"
	]

Options[LambdaCausalEvolutionGraph] = Options[LambdaCausalGraph]

LambdaCausalEvolutionGraph[cg_Graph ? GraphQ, opts : OptionsPattern[]] := With[{
	variablesQ = TrueQ[OptionValue[LambdaCausalEvolutionGraph, {opts}, "Variables"]]
},
	Graph[
		EdgeAdd[
			cg,
			Replace[VertexList[cg], event : DirectedEdge[from_, to_, tag_] :> Splice[{DirectedEdge[from, event], DirectedEdge[event, to]}], 1],
			EdgeStyle -> {Except[_DirectedEdge, _DirectedEdge] -> ResourceFunction["WolframPhysicsProjectStyleData"]["StatesGraph"]["EdgeStyle"], _ -> Inherited},
			VertexStyle -> {
				_ -> ResourceFunction["WolframPhysicsProjectStyleData"]["CausalGraph"]["VertexStyle"],
				Except[_DirectedEdge] -> Automatic
			},
			VertexShapeFunction -> {
				Except[_DirectedEdge] -> Function[
					ResourceFunction["WolframPhysicsProjectStyleData"]["StatesGraph"]["VertexShapeFunction"][#1,
						Style[Text[If[variablesQ, LambdaVariableForm[#2], #2] /. $Lambda -> "\[Lambda]"], $Black, 200 * #3], None]
				],
				_ -> Inherited
			},
			GraphLayout -> "LayeredDigraphEmbedding",
			FormatType -> StandardForm,
			PerformanceGoal -> "Quality"
		],
		FilterRules[{opts}, Options[Graph]]
	]
]

LambdaCausalEvolutionGraph[args : Except[OptionsPattern[]] .., opts : OptionsPattern[]] :=
	LambdaCausalEvolutionGraph[LambdaCausalGraph[args, FilterRules[{opts}, FilterRules[Options[LambdaCausalGraph], Except[Options[Graph]]]]], opts]


End[]

EndPackage[]