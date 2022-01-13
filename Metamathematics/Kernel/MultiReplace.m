Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]

PackageExport["MultiReplace"]
PackageExport["MultiStringReplace"]



Options[MultiReplace] := Options[SubexpressionPositions];

iMultiReplace[expr_, rule_ ? RuleQ, subExprPos_Association, head_Symbol] := Module[{
	lhs = First[rule],
	listLhs,
	positions, values,
	subsetRule
},
	positions = Keys[subExprPos];
	values = Values[subExprPos];
	lhs = wrap[lhs, head];
	listLhs = List @@ lhs;
	subsetRule = ReplacePart[rule, 1 -> listLhs];
	Association @ Map[pos |->
		With[{subExpr = Lookup[subExprPos, pos]},
			pos -> Map[
				With[{res = wrap[#, head]},
					(*Delete[Drop[pos, UpTo[Length[res]]]] @ *)
					ReplacePart[expr, List @@ Thread[head @@ Take[Replace[{} -> {{}}] /@ pos, UpTo[Length[res]]] -> Take[res, UpTo[Length[pos]]], head]]
				] &,
				DeleteDuplicates @ ReplaceList[head @@ subExpr, ReplacePart[rule, 1 -> lhs]]
			]
		],
		positions[[#]] & /@ SubsetPosition[values, listLhs]
	]
]

MultiReplace[expr_, rule_ ? RuleQ, head_Symbol : List, opts : OptionsPattern[]] :=
	iMultiReplace[expr, rule, SubexpressionPositions[expr, opts], head]

MultiReplace[expr_, rules : {(_ ? RuleQ)..}, head_Symbol : List, opts : OptionsPattern[]] := With[{subExprPos = SubexpressionPositions[expr, opts]},
	Association @ MapIndexed[KeyMap[List /* Prepend[First @ #2], iMultiReplace[expr, #1, subExprPos, head]] &, rules]
]


MultiStringReplace[s_String, rule_Rule] := Module[{
	lhs = wrap[First[rule]],
	rhs = wrap[Last[rule]],
	pos
},
	pos = StringPosition[s, #] & /@ lhs;
	AssociationMap[
		StringReplacePart[s, Take[rhs, UpTo[Length[#]]], Take[#, UpTo[Length[rhs]]]] &,
		ResourceFunction["SelectTuples"][pos, IntervalIntersection @@ (Interval /@ #) === Interval[] &]
	]
]

MultiStringReplace[s_String, rules : {_Rule...}] :=
	Association @ MapIndexed[KeyMap[List /* Prepend[First[#2]]] @ MultiStringReplace[s, #1] &, rules]

