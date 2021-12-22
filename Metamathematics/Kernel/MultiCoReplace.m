Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["MultiSubsetUnify"]
PackageExport["MultiCoReplace"]
PackageExport["unifyAt"]
PackageExport["CoMatchAt"]
PackageExport["CoReplaceAt"]



Options[iMultiSubsetUnify] = Options[unify];

iMultiSubsetUnify[posSubExpr_, subset_, head_Symbol, opts : OptionsPattern[]] := Module[{
	positions, values,
	subsets = Replace[subset, {x : Except[_head] :> head[x]}]
},
	positions = Keys[posSubExpr];
	values = Values[posSubExpr];
	DeleteCases[_ ? FailureQ] @ Association @ Map[pos |->
		Extract[positions, pos] ->
			With[{term = Extract[values, pos]}, unify[head @@ term, subsets, opts](* & /@ orderByPattern[term, head] @ subsets*)],
		List @@@ Tuples[Position[values, patt_ /; MatchQ[#, patt], {1}, Heads -> False] & /@ subsets]
	]

]


Options[MultiSubsetUnify] = Join[Options[SubexpressionPositions], Options[iMultiSubsetUnify]];

MultiSubsetUnify[expr_, subset_, head_Symbol : List, opts : OptionsPattern[]] := With[{
	posSubExpr = SubexpressionPositions[expr,
		FilterRules[{
			opts,
			"OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
			"OuterMode" -> All
		}, Options[SubexpressionPositions]]
	]},

	iMultiSubsetUnify[posSubExpr, subset, head, FilterRules[{opts}, Options[iMultiSubsetUnify]]]
]


Options[MultiCoReplace] = Join[Options[MultiSubsetUnify]];

iMultiCoReplace // ClearAll

iMultiCoReplace[expr_, rule_ ? RuleQ, multiUnification_Association, head_Symbol] :=
	DeleteCases[{}] @ Association @ KeyValueMap[{pos, unifications} |-> pos -> DeleteDuplicates @ Catenate @ Map[unification |->
		With[{
			newExpr = expr /. Normal @ KeyMap[Verbatim, unification]
		},
			Map[
				With[{res = Replace[#, {x : Except[_head] :> head[x]}]},
					ReplacePart[newExpr, List @@ Thread[head @@ Take[Replace[{} -> {{}}] /@ pos, UpTo[Length[res]]] -> Take[res, UpTo[Length[pos]]], head]]
				] &,
				ReplaceList[
					Replace[First[rule], x : Except[_head] :> head[x]],
					ReplacePart[rule, 1 -> head[OrderlessPatternSequence @@ Extract[newExpr, pos]]]
				]
			]
		],
		unifications
	],
	multiUnification
]

MultiCoReplace[expr_, rule_ ? RuleQ, head_Symbol : List, opts : OptionsPattern[]] :=
	iMultiCoReplace[expr, rule, MultiSubsetUnify[expr, First[rule], FilterRules[{opts}, Options[MultiSubsetUnify]]], head]

MultiCoReplace[expr_, rules : {_ ? RuleQ ...}, head_Symbol : List, opts : OptionsPattern[]] := With[{
	posSubExpr = SubexpressionPositions[expr,
		FilterRules[{
			opts,
			"OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
			"OuterMode" -> All
		}, Options[SubexpressionPositions]]
	]},
	Association @ MapIndexed[
		KeyMap[
			List /* Prepend[First @ #2],
			iMultiCoReplace[expr, #1, iMultiSubsetUnify[posSubExpr, First[#1], head, FilterRules[{opts}, Options[iMultiSubsetUnify]]], head]
		] &,
		rules
	]
]


unifyAt[expr_, patt_, pos_] := Enclose @ Normal @ KeyMap[Verbatim] @ Confirm @ unifier[extract[expr, pos], patt]


CoMatchAt[expr_, patt_, pos_] := Enclose @ With[{newPatt = Block[{$ModuleNumber = 1}, uniquifyPatterns[patt, expr]]},
	expr /. Confirm @ unifyAt[expr, newPatt, pos]
]


CoReplaceAt[expr_, rule_ ? RuleQ, pos_] := Enclose @ With[{newRule = Block[{$ModuleNumber = 1}, uniquifyPatterns[makePatternRule @@ rule, expr]]},
	With[{
		substitution = Normal @ KeyMap[Verbatim] @ Confirm @ unifier[extract[expr, pos], First[newRule]]
	},
		mapAt[Replace[makeReplaceRule @@ newRule], expr /. substitution, pos]
	]
]

