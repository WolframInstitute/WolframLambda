
(* ============================= *)
(* Lambda Combinator EntityStore *)
(* ============================= *)


BeginPackage["Wolfram`Lambda`EntityStore`", "Wolfram`Lambda`"]


Begin["`Private`"]

(* Core definitions (De Bruijn form as given earlier).
   Note: We keep exactly the structures already discussed to avoid silent drift.
*)
namedCore = {
  <|
    "ID" -> "I",
    "Name" -> "Identity",
    "Aliases" -> {"I","Idiot","Identity"},
    "LambdaPretty" -> "\[Lambda]x. x",
    "DeBruijn" -> $Lambda[1],
    "Arity" -> 1,
    "Family" -> "Basic",
    "Category" -> "Identity",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Returns its argument.",
    "Notes" -> "I = S K K.",
    "BasisSK" -> CombinatorI,
    "Schema" -> None,
    "ReferenceKeys" -> {"Curry","Church"}
  |>,
  <|
    "ID" -> "K",
    "Name" -> "Kestrel",
    "Aliases" -> {"K","Kestrel"},
    "LambdaPretty" -> "\[Lambda]x y. x",
    "DeBruijn" -> $Lambda[$Lambda[2]],
    "Arity" -> 2,
    "Family" -> "Basic",
    "Category" -> "Constant",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Constant selector.",
    "Notes" -> "Second argument discarded.",
    "BasisSK" -> CombinatorK,
    "Schema" -> None,
    "ReferenceKeys" -> {"Curry","Church"}
  |>,
  <|
    "ID" -> "KI",
    "Name" -> "Kite",
    "Aliases" -> {"KI","Kite"},
    "LambdaPretty" -> "\[Lambda]x y. y",
    "DeBruijn" -> $Lambda[$Lambda[1]],
    "Arity" -> 2,
    "Family" -> "Basic",
    "Category" -> "Projection",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Returns its second argument.",
    "Notes" -> "KI = (K I) applied style; also = C K.",
    "Schema" -> None,
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "S",
    "Name" -> "Starling",
    "Aliases" -> {"S","Starling"},
    "LambdaPretty" -> "\[Lambda]a b c. a c (b c)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[3[1][2[1]]]]],
    "Arity" -> 3,
    "Family" -> "Basic",
    "Category" -> "ApplicativeDistribution",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Distributes application: S f g x = f x (g x).",
    "Notes" -> "With K forms a basis (SK).",
    "Schema" -> None,
    "ReferenceKeys" -> {"Curry"}
  |>,
  <|
    "ID" -> "B",
    "Name" -> "Bluebird",
    "Aliases" -> {"B","Bluebird","Composer"},
    "LambdaPretty" -> "\[Lambda]a b c. a (b c)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[3[2[1]]]]],
    "Arity" -> 3,
    "Family" -> "Composition",
    "Category" -> "Composition",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Function composition: B f g x = f (g x).",
    "Notes" -> "B = S (K S) K.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Turner","Bird"}
  |>,
  <|
    "ID" -> "Blackbird",
    "Name" -> "Blackbird",
    "Aliases" -> {"Blackbird","B1"},
    "LambdaPretty" -> "\[Lambda]a b c d. a (b c d)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[4[3[2[1]]]]]]],
    "Arity" -> 4,
    "Family" -> "Composition",
    "Category" -> "HigherComposition",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Binary lifted composition: f (g x y).",
    "Notes" -> "Extends B to two arguments for g.",
    "Schema" -> "B_1",
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "Bunting",
    "Name" -> "Bunting",
    "Aliases" -> {"Bunting","B2"},
    "LambdaPretty" -> "\[Lambda]a b c d e. a (b c d e)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[$Lambda[5[4[3[2[1]]]]]]]]],
    "Arity" -> 5,
    "Family" -> "Composition",
    "Category" -> "HigherComposition",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Composition where inner takes 3 args.",
    "Notes" -> "General pattern B_n.",
    "Schema" -> "B_2",
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "Becard",
    "Name" -> "Becard",
    "Aliases" -> {"Becard","B3"},
    "LambdaPretty" -> "\[Lambda]a b c d e f. a (b c d e f)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[$Lambda[$Lambda[6[5[4[3[2[1]]]]]]]]]]],
    "Arity" -> 6,
    "Family" -> "Composition",
    "Category" -> "HigherComposition",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Composition where inner takes 4 args.",
    "Notes" -> "Continuation of B_n ladder.",
    "Schema" -> "B_3",
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "C",
    "Name" -> "Cardinal",
    "Aliases" -> {"C","Cardinal","Flip"},
    "LambdaPretty" -> "\[Lambda]f x y. f y x",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[3[1][2]]]],
    "Arity" -> 3,
    "Family" -> "Permutation",
    "Category" -> "ArgumentSwap",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Flips last two args.",
    "Notes" -> "C f x y = f y x.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "Thrush",
    "Name" -> "Thrush",
    "Aliases" -> {"Thrush","T"},
    "LambdaPretty" -> "\[Lambda]x f. f x",
    "DeBruijn" -> $Lambda[$Lambda[1[2]]],
    "Arity" -> 2,
    "Family" -> "Permutation",
    "Category" -> "Reordering",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Argument reorder: T x f = f x (aka flip I).",
    "Notes" -> "C I.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "Jay",
    "Name" -> "Jay",
    "Aliases" -> {"Jay","J"},
    "LambdaPretty" -> "\[Lambda]a b c d. a b (c d)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[4[3][2[1]]]]]],
    "Arity" -> 4,
    "Family" -> "Composition",
    "Category" -> "ApplicationWeaving",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Weaves application: J f g h x = f g (h x).",
    "Notes" -> "Related to Bluebird variation.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "BluebirdPrime",
    "Name" -> "BluebirdPrime",
    "Aliases" -> {"BluebirdPrime","B'"},
    "LambdaPretty" -> "\[Lambda]a b c d. a (b (c d))",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[4[2[1[3]]]]]]],
    "Arity" -> 4,
    "Family" -> "Composition",
    "Category" -> "NestedComposition",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Nested compose variant.",
    "Notes" -> "Conventions vary across sources.",
    "Schema" -> "Variant",
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "CardinalOnceRemoved",
    "Name" -> "CardinalOnceRemoved",
    "Aliases" -> {"CardinalOnceRemoved","C*"},
    "LambdaPretty" -> "\[Lambda]f g x y. f x y g   (provisional)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[4[1][3][2]]]]],
    "Arity" -> 4,
    "Family" -> "Permutation",
    "Category" -> "ReorderingHigher",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Higher permutation (pattern tentative).",
    "Notes" -> "Verify against source; naming not universal.",
    "Schema" -> "PermutationVariant",
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "M",
    "Name" -> "Mockingbird",
    "Aliases" -> {"M","Mockingbird","SelfApply"},
    "LambdaPretty" -> "\[Lambda]f. f f",
    "DeBruijn" -> $Lambda[1[1]],
    "Arity" -> 1,
    "Family" -> "FixedPointAux",
    "Category" -> "SelfApplication",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Self-application; diverges on itself.",
    "Notes" -> "M M diverges.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "ApplyTwice",
    "Name" -> "ApplyTwice",
    "Aliases" -> {"ApplyTwice"},
    "LambdaPretty" -> "\[Lambda]f x. f (f x)",
    "DeBruijn" -> $Lambda[$Lambda[2[2[1]]]],
    "Arity" -> 2,
    "Family" -> "Iteration",
    "Category" -> "UnaryIteration",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Applies function twice.",
    "Notes" -> "Also (B W I) etc.",
    "Schema" -> None,
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "Delta",
    "Name" -> "Delta",
    "Aliases" -> {"Delta","\[CapitalDelta]"},
    "LambdaPretty" -> "\[Lambda]f x. f (x x)",
    "DeBruijn" -> $Lambda[$Lambda[2[1[1]]]],
    "Arity" -> 2,
    "Family" -> "FixedPointAux",
    "Category" -> "Expansion",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Core of Y: duplicates x self-application.",
    "Notes" -> "Helps build fixed-point operators.",
    "Schema" -> None,
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "W",
    "Name" -> "Warbler",
    "Aliases" -> {"W","Warbler","Duplicator"},
    "LambdaPretty" -> "\[Lambda]f x. f x x",
    "DeBruijn" -> $Lambda[$Lambda[2[1][1]]],
    "Arity" -> 2,
    "Family" -> "Duplication",
    "Category" -> "ArgumentDuplication",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Duplicates argument: W f x = f x x.",
    "Notes" -> "Non-linear usage.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "W1",
    "Name" -> "WarblerOnceRemoved",
    "Aliases" -> {"W1","WarblerOnceRemoved"},
    "LambdaPretty" -> "\[Lambda]f g x. f g x x",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[3[2[1][1]]]]],
    "Arity" -> 3,
    "Family" -> "Duplication",
    "Category" -> "ArgumentDuplication",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Two params before duplicated x.",
    "Notes" -> "Pattern W_n.",
    "Schema" -> "W_1",
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "W2",
    "Name" -> "WarblerTwiceRemoved",
    "Aliases" -> {"W2","WarblerTwiceRemoved"},
    "LambdaPretty" -> "\[Lambda]f g h x. f g h x x",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[$Lambda[4[3[1][1]][2]]]]],
    "Arity" -> 4,
    "Family" -> "Duplication",
    "Category" -> "ArgumentDuplication",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Three params before duplicated x.",
    "Notes" -> "Pattern W_n.",
    "Schema" -> "W_2",
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "Omega",
    "Name" -> "Omega",
    "Aliases" -> {"Omega","\[CapitalOmega]"},
    "LambdaPretty" -> "(\[Lambda]x. x x)(\[Lambda]x. x x)",
    "DeBruijn" -> ($Lambda[1[1]])[$Lambda[1[1]]],
    "Arity" -> 0,
    "Family" -> "Divergent",
    "Category" -> "SelfApplication",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Canonical diverging term.",
    "Notes" -> "No normal form.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Curry"}
  |>,
  <|
    "ID" -> "Y",
    "Name" -> "YCombinator",
    "Aliases" -> {"Y","CurryY"},
    "LambdaPretty" -> "\[Lambda]f. (\[Lambda]x. f (x x)) (\[Lambda]x. f (x x))",
    "DeBruijn" -> $Lambda[ ($Lambda[2[1[1]]])[$Lambda[2[1[1]]]] ],
    "Arity" -> 1,
    "Family" -> "FixedPoint",
    "Category" -> "FixedPoint",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Produces fixed point of f under \[Beta] (normal order).",
    "Notes" -> "Non-strict fixed-point operator.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Curry","Turing"}
  |>,
  <|
    "ID" -> "Z",
    "Name" -> "ZCombinator",
    "Aliases" -> {"Z"},
    "LambdaPretty" -> "Strict Y variant (applicative-friendly)",
    "DeBruijn" -> $Lambda[ ($Lambda[2[$Lambda[1[1[2]]]][1[1]]])[$Lambda[2[$Lambda[1[1[2]]]][1[1]]]] ],
    "Arity" -> 1,
    "Family" -> "FixedPoint",
    "Category" -> "FixedPoint",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Fixed point under applicative order.",
    "Notes" -> "For strict evaluation contexts.",
    "Schema" -> None,
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "Owl",
    "Name" -> "Owl",
    "Aliases" -> {"Owl"},
    "LambdaPretty" -> "\[Lambda]f. (\[Lambda]g. f (g g)) (\[Lambda]g. f (g g))",
    "DeBruijn" -> $Lambda[$Lambda[1[$Lambda[2[2[1]]]]]],
    "Arity" -> 1,
    "Family" -> "FixedPointAux",
    "Category" -> "FixedPoint",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Another fixed-point style (factoring).",
    "Notes" -> "Equivalent behavior to Y.",
    "Schema" -> None,
    "ReferenceKeys" -> {}
  |>,
  <|
    "ID" -> "Iota",
    "Name" -> "Iota",
    "Aliases" -> {"Iota","\[Iota]"},
    "LambdaPretty" -> "\[Lambda]f. f (\[Lambda]x. x x)",
    "DeBruijn" -> $Lambda[1[$Lambda[2[2]]]],
    "Arity" -> 1,
    "Family" -> "Basis",
    "Category" -> "BasisConstructor",
    "StronglyNormalizing" -> False,
    "FixedPointRelated" -> True,
    "Definition" -> "Single-combinator basis seed (varies by encoding).",
    "Notes" -> "Different published definitions exist.",
    "Schema" -> None,
    "ReferenceKeys" -> {"ChrisBarker","IotaJot"}
  |>,
  (* Logical / Church encodings *)
  <|
    "ID" -> "True",
    "Name" -> "ChurchTrue",
    "Aliases" -> {"True"},
    "LambdaPretty" -> "\[Lambda]x y. x",
    "DeBruijn" -> $Lambda[$Lambda[2]],
    "Arity" -> 2,
    "Family" -> "Logic",
    "Category" -> "Boolean",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Boolean True.",
    "Notes" -> "Alias of K under naming.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "False",
    "Name" -> "ChurchFalse",
    "Aliases" -> {"False"},
    "LambdaPretty" -> "\[Lambda]x y. y",
    "DeBruijn" -> $Lambda[$Lambda[1]],
    "Arity" -> 2,
    "Family" -> "Logic",
    "Category" -> "Boolean",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Boolean False.",
    "Notes" -> "Alias of KI.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "IfThenElse",
    "Name" -> "IfThenElse",
    "Aliases" -> {"IfThenElse"},
    "LambdaPretty" -> "\[Lambda]p a b. p a b",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[3[2][1]]]],
    "Arity" -> 3,
    "Family" -> "Logic",
    "Category" -> "Control",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Boolean eliminator.",
    "Notes" -> "Applies predicate function-style.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "Not",
    "Name" -> "Not",
    "Aliases" -> {"Not"},
    "LambdaPretty" -> "\[Lambda]p. p FALSE TRUE",
    "DeBruijn" -> $Lambda[1[$Lambda[$Lambda[1]]][$Lambda[$Lambda[2]]]],
    "Arity" -> 1,
    "Family" -> "Logic",
    "Category" -> "BooleanOperator",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Boolean negation.",
    "Notes" -> "Uses Church booleans.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "And",
    "Name" -> "And",
    "Aliases" -> {"And"},
    "LambdaPretty" -> "\[Lambda]p q. p q p",
    "DeBruijn" -> $Lambda[$Lambda[2[1[2]]]],
    "Arity" -> 2,
    "Family" -> "Logic",
    "Category" -> "BooleanOperator",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Boolean conjunction.",
    "Notes" -> "Short-circuit style via Church encoding.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "Or",
    "Name" -> "Or",
    "Aliases" -> {"Or"},
    "LambdaPretty" -> "\[Lambda]p q. p p q",
    "DeBruijn" -> $Lambda[$Lambda[1[1[2]]]],
    "Arity" -> 2,
    "Family" -> "Logic",
    "Category" -> "BooleanOperator",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Boolean disjunction.",
    "Notes" -> "Short-circuit variant.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  (* Church numerals minimal *)
  <|
    "ID" -> "Zero",
    "Name" -> "Zero",
    "Aliases" -> {"Zero","0"},
    "LambdaPretty" -> "\[Lambda]f x. x",
    "DeBruijn" -> $Lambda[$Lambda[1]],
    "Arity" -> 2,
    "Family" -> "Numeral",
    "Category" -> "ChurchNumeral",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Zero numeral.",
    "Notes" -> "Applies f zero times.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "One",
    "Name" -> "One",
    "Aliases" -> {"One","1"},
    "LambdaPretty" -> "\[Lambda]f x. f x",
    "DeBruijn" -> $Lambda[$Lambda[2[1]]],
    "Arity" -> 2,
    "Family" -> "Numeral",
    "Category" -> "ChurchNumeral",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "One numeral.",
    "Notes" -> "Applies f once.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  <|
    "ID" -> "Succ",
    "Name" -> "Successor",
    "Aliases" -> {"Succ"},
    "LambdaPretty" -> "\[Lambda]n f x. f (n f x)",
    "DeBruijn" -> $Lambda[$Lambda[$Lambda[2[3[2[1]]]]]],
    "Arity" -> 3,
    "Family" -> "Numeral",
    "Category" -> "Arithmetic",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Numeral successor.",
    "Notes" -> "Adds one application.",
    "Schema" -> None,
    "ReferenceKeys" -> {"Church"}
  |>,
  (* Schemas (meta-entities) *)
  <|
    "ID" -> "Schema_Bn",
    "Name" -> "B_n Schema",
    "Aliases" -> {"Schema_Bn"},
    "LambdaPretty" -> "\[Lambda] a b x1..xn. a (b x1..xn)",
    "DeBruijn" -> Missing["Schema"],
    "Arity" -> "n+2",
    "Family" -> "Composition",
    "Category" -> "Schema",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "General composition ladder.",
    "Notes" -> "Instantiate for each n \[GreaterEqual] 0.",
    "Schema" -> "B_n",
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "Schema_Wn",
    "Name" -> "W_n Schema",
    "Aliases" -> {"Schema_Wn"},
    "LambdaPretty" -> "\[Lambda] f a1..an x. f a1..an x x",
    "DeBruijn" -> Missing["Schema"],
    "Arity" -> "n+2",
    "Family" -> "Duplication",
    "Category" -> "Schema",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Duplication ladder.",
    "Notes" -> "Instantiate each n \[GreaterEqual] 0.",
    "Schema" -> "W_n",
    "ReferenceKeys" -> {"Bird"}
  |>,
  <|
    "ID" -> "Schema_Permutation",
    "Name" -> "Permutation Schema",
    "Aliases" -> {"Schema_Permutation"},
    "LambdaPretty" -> "\[Lambda] f x1..xn. f x_{\[Pi](1)} .. x_{\[Pi](n)}",
    "DeBruijn" -> Missing["Schema"],
    "Arity" -> "n+1",
    "Family" -> "Permutation",
    "Category" -> "Schema",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Encodes arbitrary argument permutations.",
    "Notes" -> "\[Pi] \[Element] S_n.",
    "Schema" -> "Permutation(\[Pi])",
    "ReferenceKeys" -> {}
  |>
};

(* Programmatic generators (return De Bruijn form with $Lambda nesting).
   For consistency with earlier definitions.
*)

BluebirdChainExplicit[n_Integer?NonNegative] := Module[{body},
  (* \[Lambda] a b x1..xn. a (b x1..xn)
     Indices: innermost = x_n = 1, x_{n-1}=2,..., x1 = n, b = n+1, a = n+2
  *)
  body = (n + 2)[ Fold[Apply, n + 1, Range[n, 1, -1]] ];
  Nest[$Lambda, body, n + 2]
];

WarblerChain[n_Integer?NonNegative] := Module[{body},
  (* \[Lambda] f a1..an x. f a1..an x x
     Indices: x=1, a_n=2,..., a1 = n+1, f = n+2
  *)
  body = (n + 2)[ Fold[Apply, n + 2, Join[Range[n + 1, 2, -1], {1, 1}]] /. (n + 2) -> (n + 2) ];
  Nest[$Lambda, body, n + 2]
];

PermutationCombinator[p_List] := Module[{n = Length[p], f, body, toIndex},
  (* Binders: f, x1..xn
     Indices: x_n=1,...,x1=n, f = n+1
     Need x_{p(1)},..., x_{p(n)} -> indices: x_k at position k = (n - k + 1)
  *)
  f = n + 1;
  toIndex[k_] := n - k + 1;
  body = Fold[Apply, f, toIndex /@ p];
  Nest[$Lambda, body, n + 1]
];

(* AddBChain / AddWChain build and return a list of entity associations *)
AddBChain[max_Integer?NonNegative] := Table[
  With[{n = k},
    <|
      "ID" -> If[n == 0, "B", "B" <> ToString[n]],
      "Name" -> If[n == 0, "Bluebird", "B_" <> ToString[n]],
      "Aliases" -> If[n == 0, {"B","Bluebird","Composer"}, { "B"<>ToString[n]}],
      "LambdaPretty" -> "\[Lambda] a b x1..x"<>ToString[n]<>". a (b x1..x"<>ToString[n]<>")",
      "DeBruijn" -> BluebirdChainExplicit[n],
      "Arity" -> n + 3 (* a b x1..xn *),
      "Family" -> "Composition",
      "Category" -> "HigherComposition",
      "StronglyNormalizing" -> True,
      "FixedPointRelated" -> False,
      "Definition" -> "Generalized composition B_"<>ToString[n],
      "Notes" -> "B_n ladder.",
      "Schema" -> "B_"<>ToString[n],
      "ReferenceKeys" -> {"Bird"}
    |>
  ],
  {k, 0, max}
];

AddWChain[max_Integer?NonNegative] := Table[
  With[{n = k},
    <|
      "ID" -> If[n == 0, "W", "W" <> ToString[n]],
      "Name" -> If[n == 0, "Warbler", "W_" <> ToString[n]],
      "Aliases" -> If[n == 0, {"W","Warbler","Duplicator"}, {"W"<>ToString[n]}],
      "LambdaPretty" -> "\[Lambda] f a1..a"<>ToString[n]<>" x. f a1..a"<>ToString[n]<>" x x",
      "DeBruijn" -> WarblerChain[n],
      "Arity" -> n + 2,
      "Family" -> "Duplication",
      "Category" -> "ArgumentDuplication",
      "StronglyNormalizing" -> True,
      "FixedPointRelated" -> False,
      "Definition" -> "Duplication combinator W_"<>ToString[n],
      "Notes" -> "W_n ladder.",
      "Schema" -> "W_"<>ToString[n],
      "ReferenceKeys" -> {"Bird"}
    |>
  ],
  {k, 0, max}
];

AddPermutationCombinator[name_String, p_List] := Module[{n = Length[p]},
  <|
    "ID" -> name,
    "Name" -> name,
    "Aliases" -> {name},
    "LambdaPretty" -> "\[Lambda] f x1..x"<>ToString[n]<>". f x_{\[Pi](1)}..x_{\[Pi]("<>ToString[n]<>")} with \[Pi]="<>ToString[p],
    "DeBruijn" -> PermutationCombinator[p],
    "Arity" -> n + 1,
    "Family" -> "Permutation",
    "Category" -> "Reordering",
    "StronglyNormalizing" -> True,
    "FixedPointRelated" -> False,
    "Definition" -> "Permutation combinator applying permutation " <> ToString[p],
    "Notes" -> "Generated from schema.",
    "Schema" -> "Permutation"<>ToString[p],
    "ReferenceKeys" -> {}
  |>
];

(* Build entity index: choose how many extra B_n / W_n to pre-populate *)
extraB = AddBChain[3];    (* already had up to B3 / Becard, kept for completeness *)
extraW = AddWChain[2];    (* W, W1, W2 *)

(* Optional example permutations *)
permExamples = {
  AddPermutationCombinator["PermSwap12", {2,1}],
  AddPermutationCombinator["PermRotate123", {2,3,1}]
};

(* Merge while avoiding duplicate IDs (simple precedence to namedCore order) *)
allEntitiesRaw = Join[namedCore, extraB, extraW, permExamples];

allEntitiesRaw = Append[#, "BasisSK" -> LambdaCombinator[#DeBruijn]] & /@ allEntitiesRaw;

(* Deduplicate by ID *)
allEntities = Values @ GroupBy[allEntitiesRaw, #ID &, First];

(* Property definitions *)
propertyDefs = <|
  "Name" -> <|"Label"->"Name","Type"->"String"|>,
  "Aliases" -> <|"Label"->"Aliases","Type"->"List"|>,
  "LambdaPretty" -> <|"Label"->"Pretty Lambda","Type"->"String"|>,
  "DeBruijn" -> <|"Label"->"De Bruijn Form","Type"->"Expression"|>,
  "Arity" -> <|"Label"->"Arity","Type"->"Expression"|>,
  "Family" -> <|"Label"->"Family","Type"->"String"|>,
  "Category" -> <|"Label"->"Category","Type"->"String"|>,
  "StronglyNormalizing" -> <|"Label"->"Strongly Normalizing","Type"->"Boolean"|>,
  "FixedPointRelated" -> <|"Label"->"Fixed Point Related","Type"->"Boolean"|>,
  "Definition" -> <|"Label"->"Definition","Type"->"String"|>,
  "Notes" -> <|"Label"->"Notes","Type"->"String"|>,
  "BasisSK" -> <|"Label"->"SK Basis Expansion","Type"->"Expression"|>,
  "Schema" -> <|"Label"->"Schema Identifier","Type"->"Expression"|>,
  "ReferenceKeys" -> <|"Label"->"Reference Keys","Type"->"List"|>
|>;

entitiesAssoc = Association @ Map[
   #ID -> KeyDrop[#, {"ID"}] &,
   allEntities
];

lambdaCombinatorStore = EntityStore[
    "LambdaCombinator" -> <|
      "Label" -> "Lambda Combinator",
      "Entities" -> entitiesAssoc,
      "Properties" -> propertyDefs
    |>
];

EntityUnregister["LambdaCombinator"]

EntityRegister[lambdaCombinatorStore];

End[];

EndPackage[];
