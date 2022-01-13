Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["MultiCoUnify"]
PackageExport["MultiCoReplace"]
PackageExport["unifyAt"]
PackageExport["CoMatchAt"]
PackageExport["CoReplaceAt"]



Options[iMultiCoUnify] := Options[unify];

iMultiCoUnify[posSubExpr_, subset_, head_Symbol, opts : OptionsPattern[]] := Module[{
	positions, values,
	subsets = wrap[subset, head]
},
	positions = Keys[posSubExpr];
	values = Values[posSubExpr];
	DeleteCases[_ ? FailureQ] @ Association @ Map[pos |->
		Extract[positions, pos] ->
			With[{term = Extract[values, pos]}, unify[head @@ term, subsets, opts](* & /@ orderByPattern[term, head] @ subsets*)],
		Tuples[Position[values, patt_ /; MatchQ[#, patt], {1}, Heads -> False] & /@ subsets]
	]

]


Options[MultiCoUnify] := Join[Options[SubexpressionPositions], Options[iMultiCoUnify]];

MultiCoUnify[expr_, subset_, head_Symbol : List, opts : OptionsPattern[]] := With[{
	posSubExpr = SubexpressionPositions[expr,
		FilterRules[{
			opts,
			"OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
			"OuterMode" -> All
		}, Options[SubexpressionPositions]]
	]},

	iMultiCoUnify[posSubExpr, subset, head, FilterRules[{opts}, Options[iMultiCoUnify]]]
]


iMultiCoReplace[expr_, rule_ ? RuleQ, multiUnification_Association, head_Symbol] :=
	DeleteCases[{}] @ Association @ KeyValueMap[{pos, unifications} |-> pos -> DeleteDuplicates @ Catenate @ Map[unification |->
		With[{
			newExpr = expr /. unification
		},
			Map[
				With[{res = wrap[#, head]},
					ReplacePart[newExpr, List @@ Thread[head @@ Take[Replace[{} -> {{}}] /@ pos, UpTo[Length[res]]] -> Take[res, UpTo[Length[pos]]], head]]
				] &,
				ReplaceList[
					wrap[First[rule], head],
					ReplacePart[rule, 1 -> head[OrderlessPatternSequence @@ Extract[newExpr, pos]]]
				]
			]
		],
		unifications
	],
	multiUnification
]


Options[MultiCoReplace] := Join[Options[MultiCoUnify]];

MultiCoReplace[expr_, rule_ ? RuleQ, head_Symbol : List, opts : OptionsPattern[]] :=
	iMultiCoReplace[expr, rule, MultiCoUnify[expr, First[rule], FilterRules[{opts}, Options[MultiCoUnify]]], head]

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
			iMultiCoReplace[expr, #1, iMultiCoUnify[posSubExpr, First[#1], head, FilterRules[{opts}, Options[iMultiCoUnify]]], head]
		] &,
		rules
	]
]


CoUnifyAt[expr_, patt_, pos_] := Enclose @ First @ Confirm @ unify[extract[expr, pos], patt]


CoMatchAt[expr_, patt_, pos_] := Enclose @ With[{newPatt = Block[{$ModuleNumber = 1}, uniquifyPatterns[patt, expr]]},
	expr /. Confirm @ CoUnifyAt[expr, newPatt, pos]
]


CoReplaceAt[expr_, rule_ ? RuleQ, pos_] := Enclose @ With[{newRule = Block[{$ModuleNumber = 1}, uniquifyPatterns[makePatternRule @@ rule, expr]]},
	With[{
		substitution = First @ Confirm @ unify[extract[expr, pos], First[newRule]]
	},
		mapAt[Replace[makeReplaceRule @@ newRule], expr /. substitution, pos]
	]
]

