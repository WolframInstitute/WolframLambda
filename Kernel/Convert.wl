BeginPackage["Wolfram`Lambda`"]

ClearAll[
    LambdaConvert
]

Begin["`Private`"]


LambdaConvert[expr_, form_String : "Application", args___] := Switch[form,
	"Colors",
	ColorizeLambda[expr, args],
	"Application",
	LambdaApplication[expr, args],
	"RightApplication",
	LambdaRightApplication[expr, args],
	"VariableForm" | "StandardForm",
	LambdaVariableForm[expr, args],
	"BracketParens" | "Brackets",
	LambdaBrackets[expr, args],
	"DepthForm",
	LambdaDepthForm[expr, args],
	"Function",
	LambdaFunction[expr, args],
	"Combinator",
	LambdaCombinator[expr, args],
	"Smiles",
	LambdaSmiles[expr, args],
	"Tree",
	LambdaTree[expr, args],
	"Graph",
	LambdaGraph[expr, args],
	"Diagram",
	LambdaDiagram[expr, args],
	"String",
	LambdaString[expr, args],
	"BLC",
	LambdaBLC[expr, args],
	"Haskell",
	LambdaToHaskell[expr, args],
	_,
	Missing[form]
]
ResourceFunction["AddCodeCompletion"]["LambdaConvert"][None,
	{
		"Colors", "Application", "RightApplication", "VariableForm", "BracketParens", "DepthForm",
		"Function", "Combinator",
		"Tree", "Graph", "Diagram",
		"String", "BLC", "Haskell"
	}
]


End[]

EndPackage[]
