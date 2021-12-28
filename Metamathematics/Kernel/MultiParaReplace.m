Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["MultiParaUnify"]
PackageExport["MultiParaReplace"]

PackageExport["unifyAt"]
PackageExport["matchAt"]
PackageExport["replaceAt"]



Options[iMultiParaUnify] := Options[unifier];

iMultiParaUnify[posSubExpr_, subset_, head_Symbol, opts : OptionsPattern[]] := Module[{
	positions, values,
	subsets = wrap[subset, head]
},
	positions = Keys[posSubExpr];
	values = Values[posSubExpr];
	DeleteCases[_ ? FailureQ] @ Association @ Map[pos |->
		Extract[positions, pos] ->
			With[{term = Extract[values, pos]}, unifier[head @@ term, subsets]],
		Tuples[List /@ Range[Length[values]], {Length[subsets]}]
	]

]


Options[MultiParaUnify] := Join[Options[SubexpressionPositions], Options[iMultiParaUnify]];

MultiParaUnify[expr_, subset_, head_Symbol : List, opts : OptionsPattern[]] := With[{
	posSubExpr = SubexpressionPositions[expr,
		FilterRules[{
			opts,
			"OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
			"OuterMode" -> All
		}, Options[SubexpressionPositions]]
	]},

	iMultiParaUnify[posSubExpr, subset, head, FilterRules[{opts}, Options[iMultiParaUnify]]]
]


Options[MultiParaReplace] := Join[Options[MultiParaUnify]];

iMultiParaReplace[expr_, rule_ ? RuleQ, multiUnification_Association, head_Symbol] :=
	DeleteCases[{}] @ Association @ KeyValueMap[{pos, unifications} |-> pos -> DeleteDuplicates @ Catenate @ Map[unification |->
		With[{
			newExpr = expr /. unification,
            newRule = makeReplaceRule @@ (makePatternRule @@ rule /. unification)
		},
			Map[
				With[{res = wrap[#, head]},
					ReplacePart[newExpr, List @@ Thread[head @@ Take[Replace[{} -> {{}}] /@ pos, UpTo[Length[res]]] -> Take[res, UpTo[Length[pos]]], head]]
				] &,
				ReplaceList[
					wrap[First[newRule], head],
					ReplacePart[newRule, 1 -> head[OrderlessPatternSequence @@ Extract[newExpr, pos]]]
				]
			]
		],
		wrap[unifications]
	],
	multiUnification
]

MultiParaReplace[expr_, rule_ ? RuleQ, head_Symbol : List, opts : OptionsPattern[]] := With[{
    newRule = makeReplaceRule @@ uniquifyPatterns[makePatternRule @@ rule]
},
	iMultiParaReplace[expr, newRule, MultiParaUnify[expr, First[newRule], FilterRules[{opts}, Options[MultiParaUnify]]], head]
]

MultiParaReplace[expr_, rules : {_ ? RuleQ ...}, head_Symbol : List, opts : OptionsPattern[]] := With[{
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
            With[{rule = uniquifyPatterns[#1]},
			    iMultiParaReplace[expr, rule, iMultiParaUnify[posSubExpr, First[rule], head, FilterRules[{opts}, Options[iMultiParaUnify]]], head]
            ]
		] &,
		rules
	]
]


unifyAt[expr_, patt_, pos_] := unifier[extract[expr, pos], patt]


matchAt[expr_, patt_, pos_] := Enclose @ With[{newPatt = Block[{$ModuleNumber = 1}, uniquifyPatterns[patt, expr]]},
	expr /. Confirm @ unifyAt[expr, newPatt, pos]
]


replaceAt[expr_, rule_ ? RuleQ, pos_] := Enclose @ With[{newRule = Block[{$ModuleNumber = 1}, uniquifyPatterns[makePatternRule @@ rule, expr]]},
	With[{
		substitution = Confirm @ unifier[extract[expr, pos], First[newRule]]
	},
		mapAt[Replace[makeReplaceRule @@ newRule], expr /. substitution, pos]
	]
]

