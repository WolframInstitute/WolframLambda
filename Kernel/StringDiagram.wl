BeginPackage["Wolfram`Lambda`"]

Get["Wolfram`DiagrammaticComputation`"]

ClearAll[
    LambdaStringDiagram,
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
    {"LambdaSize" -> .33, "LambdaLabelStyle" -> FontSize -> 10, "LambdaStyle" -> Automatic},
    Options[Wolfram`DiagrammaticComputation`Diagram`ToDiagram`Private`LambdaDiagram],
    Options[DiagramArrange],
    Options[SmoothGraphicsCurves]
]

LambdaStringDiagram[lambda_, opts : OptionsPattern[]] := With[{
    lambdaSize = OptionValue["LambdaSize"],
    lambdaStyle = OptionValue["LambdaStyle"],
    lambdaLabelStyle = OptionValue["LambdaLabelStyle"]
},
    DiagramArrange[
        ToDiagram[TagLambda[lambda], FilterRules[{opts}, Options[Wolfram`DiagrammaticComputation`Diagram`ToDiagram`Private`LambdaDiagram]]],
        FilterRules[{opts}, Options[DiagramArrange]],
        "LoopDiagrams" -> False, "WireLabels" -> False, "Rotate" -> Top, 
        Alignment -> Center, Dividers -> False,
        "RowSort" -> True, Direction -> Up
    ] // (d |-> DiagramMap[Diagram[#, "PortLabels" -> None, "PortArrows" -> OptionValue["WireStyle"]] &] @ DiagramArrange @ DiagramMap[
        Diagram[#, 
            Switch[#["Name"],
                HoldForm[""],
                {"Shape" -> "Triangle", "Style" -> Hue[0.709, 0.445, 1], "FloatingPorts" -> True, "Width" -> 1, "Height" -> 1},
                HoldForm[Style[Subscript["\[Lambda]", _], ___]],
                With[{size = lambdaSize * DiagramGridHeight[d]}, {
                    "Expression" -> Style[#["Name"], lambdaLabelStyle],
                    If[lambdaStyle === Automatic, {}, "Style" -> lambdaStyle],
                    "Width" -> size / GoldenRatio, "Height" -> size
                }],
                _,
                Unevaluated[]
            ]
        ] &,
        d
    ])
]

Options[SmoothLambdaStringDiagram] = Options[SmoothGraphicsCurves]

SmoothLambdaStringDiagram[lambda_, n : _ ? NumericQ : 0, m : _Integer ? Positive : 5, opts : OptionsPattern[]] /; 0 <= n <= 1 := 
    SmoothGraphicsCurves[
        DiagramGrid[LambdaStringDiagram[lambda, FilterRules[{opts}, Options[LambdaStringDiagram]]], PlotInteractivity -> False], n, m,
        FilterRules[{opts}, Options[SmoothGraphicsCurves]]
    ] /. {Arrow[{p1_, p2_}] :> Arrow[{p1, p2 + Normalize[p2 - p1]}]}

End[]

EndPackage[]

