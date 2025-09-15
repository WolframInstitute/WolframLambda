BeginPackage["Wolfram`Lambda`"]

ClearAll[
    LambdaMultiwayGraph,
	LambdaAllPathEvents,
    LambdaMultiwayCausalGraph,
    LambdaMultiwayCausalEvolutionGraph
]

Begin["`Private`"]

Options[LambdaMultiwayGraph] = Join[{
	"Simple" -> True,
    "HighlightPath" -> None,
	"Highlight" -> True,
	"Variables" -> False,
	"VertexShape" -> Automatic
},
	Options[BetaPositionReductions],
	Options[Graph]
]

LambdaMultiwayGraph[lambda_, t_Integer : 1 , m : _Integer | Infinity : Infinity, opts : OptionsPattern[]] := With[{
	simpleQ = TrueQ[OptionValue["Simple"]],
	variablesQ = TrueQ[OptionValue["Variables"]],
	highlight = Replace[OptionValue["HighlightPath"], {True | Automatic -> 1, Except[_Integer] -> None}],
	reduceOptions = FilterRules[{opts}, Options[BetaPositionReductions]],
	highlightStyle = OptionValue["Highlight"]
}, {
	highlightStyle1 = Replace[highlightStyle, True | Automatic :> $LambdaStyles["Lambda"]],
	highlightStyle2 = Replace[highlightStyle, True | Automatic :> $LambdaStyles["BrighterLambda"]]
}, Block[{g, highlightNodes},	
	g = ResourceFunction["NestGraphTagged"][
		KeySort[Block[{i = 1}, KeyMap[{#, i++} &] @ If[simpleQ, DeleteDuplicates, Identity] @ BetaPositionReductions[#, m, reduceOptions]], LexicographicOrder] &,
		lambda,
		t,
		FilterRules[{opts}, Options[ResourceFunction["NestGraphTagged"]]]
	];
	g = Graph[VertexList[g], MapAt[First, EdgeList[g], {All, 3}]];
	If[	! MatchQ[highlightStyle, False | None],
		highlightNodes = Select[Pick[VertexList[g], VertexOutDegree[g], 0], BetaReducePositions[#] =!= {} &]
	];
	g = Graph[g,
		FilterRules[{opts}, Options[Graph]],
		VertexShapeFunction -> Map[With[{highlightedQ = ! MatchQ[highlightStyle, False | None] && MemberQ[highlightNodes, #]},
			# -> Replace[OptionValue["VertexShape"], {
				"Expression" | {"Expression", typeOpts : OptionsPattern[]} :> With[{background = If[highlightedQ, highlightStyle1, None]},
					If[	highlightedQ,
						Function[Inset[Text @ Framed[Style[If[variablesQ, LambdaVariableForm[LambdaUntag[#2]], LambdaForm[#2]], 200 * #3, typeOpts, FontColor -> $Black], BaseStyle -> Background -> highlightStyle1, FrameMargins -> 0], #1]],
						Function[ResourceFunction["WolframPhysicsProjectStyleData"]["StatesGraph", "VertexShapeFunction"][
							#1, Text @ Style[If[variablesQ, LambdaVariableForm[LambdaUntag[#2]], LambdaForm[#2]], 200 * #3, typeOpts, FontColor -> $Black], None
						]]
					]
				],
				"Tree" | {"Tree", subOpts___} :> With[{background = If[highlightedQ, highlightStyle1, None], frame = If[highlightedQ, highlightStyle2, Automatic]},
					Function[Inset[Framed[
						HighlightLambdaTree[#2, subOpts,
							"VariableLabels" -> variablesQ, Method -> "Boxes", PlotTheme -> "Minimal",
							TreeElementSize -> All -> .5,
							ImageSize -> #3 * 25 * LeafCount[#2] ^ .2
						],
						Background -> background,
						FrameStyle -> frame
					], #1]]
				],
				"Diagram" | {"Diagram", subOpts___} :> With[{background = If[highlightedQ, highlightStyle1, None], frame = If[highlightedQ, highlightStyle2, Automatic]},
					Function[Inset[
						Framed[
							LambdaDiagram[#2, subOpts, "Colored" -> True, ColorRules -> {"LambdaApplication" -> StandardRed}, ImageSize -> #3 * 30 * LeafCount[#2] ^ .2],
							Background -> background,
							FrameStyle -> frame
						],
						#1
					]]
				],
				type_String | {type_String, args___, typeOpts : OptionsPattern[]} :>
					If[	highlightedQ,
						Function[Inset[Text @ Framed[Style[LambdaConvert[#2, type, args], 200 * #3, typeOpts, FontColor -> $Black], BaseStyle -> Background -> highlightStyle1, FrameMargins -> 0], #1]],
						Function[ResourceFunction["WolframPhysicsProjectStyleData"]["StatesGraph", "VertexShapeFunction"][
							#1, Text @ Style[LambdaConvert[#2, type, args], 200 * #3, typeOpts, FontColor -> $Black], None
						]]
					]
				,
				_ -> Automatic
			}]] &,
			VertexList[g]
		],
		VertexSize -> Switch[OptionValue["VertexShape"], Automatic, x_ :> .1 Sqrt[LeafCount[x]], "Tree" | "Diagram" | {"Tree" | "Diagram", _}, 2.5, "Expression", Automatic],
		VertexStyle -> Thread[highlightNodes -> highlightStyle2],
		EdgeStyle -> _ -> Hue[0.6, 0.7, 0.7],
		GraphLayout -> "LayeredDigraphEmbedding",
		FormatType -> StandardForm,
		PerformanceGoal -> "Quality"
	];
  	If[	highlight === None,
		g,
		HighlightGraph[g,
			Style[
				With[{edges = EdgeList[g]},
					Join[#, VertexList[#]] & @
						NestWhilePairList[FirstCase[edges, edge : DirectedEdge[#, next_, {_, highlight}] :> {edge, If[next === #, Missing[], next]}] &, lambda, Not @* MissingQ, 1, t]
				],
				Directive[Thick, StandardRed]
			]
		]
	]
]
]


LambdaAllPathEvents[lambda_, args___] := Block[{mwg = LambdaMultiwayGraph[lambda, args], taggedlambda = TagLambda[lambda], paths},
	paths = Catenate[ResourceFunction["FindPathEdges"][mwg, lambda, #, Infinity, All] & /@ Pick[VertexList[mwg], VertexOutDegree[mwg], 0]];
	MapThread[
		Append[DirectedEdge @@ #1, #3 -> #2] &,
		{Partition[FoldList[MapAt[BetaSubstitute, #1, {#2}] &, taggedlambda, #], 2, 1], #, Range[Length[#]]}
	] & /@ paths[[All, All, 3, 1]]
]

Options[LambdaMultiwayCausalGraph] = Join[Options[LambdaCausalGraph], Options[Graph]];

LambdaMultiwayCausalGraph[args__, opts : OptionsPattern[]] := With[{
	cgs = VertexReplace[
		LambdaCausalGraph[#, FilterRules[{opts}, FilterRules[Options[LambdaCausalGraph], Except[Options[Graph]]]]],
		DirectedEdge[from_, to_, _ -> pos_] :> DirectedEdge[from, to, pos]
	] & /@ LambdaAllPathEvents[args]
},
	Graph[
		GraphUnion[##,
			Normal @ Merge[Options[#, {VertexStyle, VertexShapeFunction, EdgeStyle}] & /@ cgs, Apply[Join]],
			GraphLayout -> "SymmetricLayeredEmbedding",
			FormatType -> StandardForm,
			PerformanceGoal -> "Quality"
		] & @@ cgs,
		FilterRules[{opts}, Options[Graph]]
	]
]


LambdaMultiwayCausalEvolutionGraph[args : Except[OptionsPattern[]] .., opts : OptionsPattern[]] :=
	LambdaCausalEvolutionGraph[LambdaMultiwayCausalGraph[args, FilterRules[{opts}, FilterRules[Options[LambdaMultiwayCausalGraph], Except[Options[Graph]]]]], opts]



End[]

EndPackage[]