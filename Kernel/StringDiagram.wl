BeginPackage["Wolfram`Lambda`"]

Get["Wolfram`DiagrammaticComputation`"]

ClearAll[
    LambdaStringDiagram,
    LambdaInteractionNet,
    SmoothLambdaStringDiagram
]

Begin["`Private`"]

ConnectCurves[curves_, eps_ : 1*^-4] := Block[{g},
    g = RelationGraph[EuclideanDistance[#1[[-1]], #2[[1]]] < eps &, curves];
  
    Catenate[
        With[{sg = #, in = Pick[VertexList[#], VertexInDegree[#], 0], out = Pick[VertexList[#], VertexOutDegree[#], 0]}, 
            Apply[Join] @* MapAt[Rest, {2 ;;}] @* Map[Split /* Map[First]] /@ 
                Catenate @ Outer[First[FindPath[sg, ##], VertexList[sg]] &, in, out, 1]
        ] & /@ WeaklyConnectedGraphComponents[g]
    ]
]

SmoothPoints[points_, n : _ ? NumericQ : .5, m : _Integer?Positive : 5] /; 0 <= n <= 1 := With[
    {len = Length[points]}, {k = Round[n * (len - 2) + 1]},
    {if = Interpolation[Thread[{Subdivide[len - k], Prepend[First[points]] @ Append[Last[points]] @ MovingAverage[points, k][[2 ;; -2]]}], InterpolationOrder -> 2]},
    BSplineCurve[if /@ Subdivide[m]]
]

Options[SmoothGraphicsCurves] = Join[{
    "WireStyle" -> Directive[RGBColor[0.6, 0.6, 0.6], CapForm["Round"], AbsoluteThickness[1.5], Arrowheads[{{Medium, .6, Graphics[Polygon[{{-1/2, 1/4}, {1/2, 0}, {-1/2, -1/4}}]]}}]]},
    Options[Graphics]
]

SmoothGraphicsCurves[g_, n : _ ? NumericQ : .5, m : _Integer ? Positive : 5, opts : OptionsPattern[]] /; 0 <= n <= 1 := Block[{h, curves},
    curves = First[Reap[h = g /. BSplineCurve[ps_] :> (Sow[ps]; {})][[2]], {}];
    Show[Graphics[{OptionValue["WireStyle"], Haloing[], Arrow @ SmoothPoints[#, n, m]} & /@ ConnectCurves[curves]], h, FilterRules[{opts}, Options[Graphics]]]
]

Options[LambdaStringDiagram] = Join[
    {
        "LambdaSize" -> .15, "LambdaOptions" -> {FontSize -> 10}, "ApplicationOptions" -> {},
        "Grid" -> True, "MultiCopy" -> True, "FlipApplication" -> False
    },
    Options[Wolfram`DiagrammaticComputation`Diagram`ToDiagram`Private`LambdaDiagram],
    Options[DiagramArrange],
    Options[SmoothGraphicsCurves]
]

LambdaStringDiagram[lambda_, opts : OptionsPattern[]] := With[{
    lambdaSize = OptionValue["LambdaSize"],
    lambdaOpts = OptionValue["LambdaOptions"],
    appOpts = OptionValue["ApplicationOptions"],
    arrange = If[TrueQ[OptionValue["Grid"]], DiagramArrange, Identity[#1] &]
},
    arrange[
        ToDiagram[TagLambda[lambda], FilterRules[{opts}, Options[Wolfram`DiagrammaticComputation`Diagram`ToDiagram`Private`LambdaDiagram]]] //
            If[ TrueQ[OptionValue["MultiCopy"]], Identity, DiagramCopySplit] //
            If[ TrueQ[OptionValue["FlipApplication"]],
                DiagramMap[
                    If[ #["HoldExpression"] === HoldForm["\[Application]"],
                        Diagram[#, PortDual @ Last[#["InputPorts"]], Join[Most[#["InputPorts"]], #["OutputPorts"]],
                            appOpts,
                            "PortLabels" -> TakeDrop[Permute[Catenate[#["PortLabels"]], {2, 1}], 1]
                        ],
                        #
                    ] &,
                    #
                ] &,
                Identity
            ]
        ,
        FilterRules[{opts}, Options[DiagramArrange]],
        "WireLabels" -> False, "Rotate" -> Top,
        Alignment -> Center, Direction -> Up
    ] // (d |-> DiagramMap[
        Diagram[#, 
            Replace[#["HoldExpression"], {
                HoldForm["Copy"] :>
                    {
                        "Shape" -> Switch[#["Arities"], {1, _}, "RoundedTriangle", {_, 1}, "RoundedUpsideDownTriangle", _, Automatic],
                        "Style" -> Hue[0.709, 0.445, 1],
                        "FloatingPorts" -> Switch[#["Arities"], {1, _}, {False, True}, {_, 1}, {True, False}, _, False],
                        "Width" -> 1, "Height" -> 1
                    },
                HoldForm[Subscript["\[Lambda]", _]] :>
                    With[{size = lambdaSize * DiagramGridHeight[d]}, {
                        lambdaOpts,
                        "Width" -> size / GoldenRatio, "Height" -> size
                    }],
                _ -> Unevaluated[]
            }],
            "PortLabels" -> None, "PortArrows" -> OptionValue["WireStyle"]
        ] &,
        d
    ]) 
]

LambdaInteractionNet[l_, opts : OptionsPattern[]] :=
	SimplifyDiagram @ LambdaStringDiagram[l, opts,
		"LambdaOptions" -> {
            "Shape" -> "RoundedUpsideDownTriangle", "Width" -> 1, "Height" -> 1,
            "Style" -> Lookup[$LambdaTreeColorRules, "Lambda"],
            "FloatingPorts" -> {True, False}},
        "ApplicationOptions" -> {"Shape" -> "RoundedTriangle", "Width" -> 1, "Height" -> 1, "Style" -> Lookup[$LambdaTreeColorRules, "Lambda"], "FloatingPorts" -> {False, True}},
		"AddErasers" -> True, "MultiCopy" -> False, "FlipApplication" -> True,
        "WireStyle" -> Automatic,
        "UnarySpiders" -> False,
        "Grid" -> False
	]

Options[SmoothLambdaStringDiagram] = Options[SmoothGraphicsCurves]

SmoothLambdaStringDiagram[lambda_, n : _ ? NumericQ : 0, m : _Integer ? Positive : 5, opts : OptionsPattern[]] /; 0 <= n <= 1 := 
    SmoothGraphicsCurves[
        DiagramGrid[LambdaStringDiagram[lambda, FilterRules[{opts}, Options[LambdaStringDiagram]]], PlotInteractivity -> False, "PortLabels" -> False], n, m,
        FilterRules[{opts}, Options[SmoothGraphicsCurves]]
    ] /. {Arrow[{p1_, p2_}] :> Arrow[{p1, p2 + Normalize[p2 - p1]}]}

End[]

EndPackage[]

