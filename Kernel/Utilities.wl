BeginPackage["Wolfram`Lambda`"]

Begin["`Private`"]

NestWhilePairList[f_, expr_, test_, m_Integer : 1, max : _Integer | Infinity : Infinity, g_ : First] := 
	Enclose @ Block[{list = {}, args = {expr}, i = 0},
		While[True,
			If[i >= max || Length[args] == m && ! ConfirmBy[test @@ args, BooleanQ], Break[]];
			Replace[f @@ args,
			{
				pair : {_, next_} :> (AppendTo[list, g[pair]]; If[i++ >= m, args = Rest[args]]; args = Append[args, next];),
				_ :> Break[]
			}];
		];
		list
	]


NormalPosition[expr_, patt_, n : _Integer | Infinity : Infinity, pos_List : {}] := Block[{
	k = n, curPos, curExpr, positions = {}, stack = CreateDataStructure["Stack", {{{}, Hold[expr]}}]
},
	While[k > 0 && ! stack["EmptyQ"],
		{curPos, curExpr} = stack["Pop"];
		With[{e = Unevaluated @@ curExpr},
			If[ MatchQ[curExpr, Hold[patt]],
				AppendTo[positions, curPos];
				k--
			];
			If[ AtomQ[e], Continue[]];
			Do[
				stack["Push", {Append[curPos, i], Extract[e, i, Hold]}]
				,
				{i, Range[Length[e], 0, -1]}
			]
		]
	];
	positions
]

OuterPosition[expr_, patt_, n : _Integer | Infinity : Infinity, pos_List : {}] := Block[{
	k = n, curPos, curExpr, positions = {}, queue = CreateDataStructure["Queue", {{{}, Hold[expr]}}]
},
	While[k > 0 && ! queue["EmptyQ"],
		{curPos, curExpr} = queue["Pop"];
		With[{e = Unevaluated @@ curExpr},
			If[ MatchQ[curExpr, Hold[patt]],
				AppendTo[positions, curPos];
				k--
			];
			If[ AtomQ[e], Continue[]];
			Do[
				queue["Push", {Append[curPos, i], Extract[e, i, Hold]}]
				,
				{i, Range[0, Length[e]]}
			]
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


End[]

EndPackage[]
