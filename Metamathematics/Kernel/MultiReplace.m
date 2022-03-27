Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]

PackageExport["MultiReplace"]
PackageExport["MultiStringReplace"]



Options[iMultiReplace] = {"Mode" -> "Tuples", "ReturnTokens" -> False};

iMultiReplace[expr_, rule_ ? RuleQ, subExprPos_Association, head_, OptionsPattern[]] := Module[{
	lhs = First[rule],
	listLhs,
	positions, values,
	subsetRule,
	returnTokens = OptionValue["ReturnTokens"]
},
	positions = Keys[subExprPos];
	values = Values[subExprPos];
	lhs = wrap[lhs, head];
	listLhs = List @@ lhs;
	subsetRule = ReplacePart[rule, 1 -> listLhs];
	DeleteCases[{}] @ Association @ Map[pos |->
		With[{subExpr = Lookup[subExprPos, pos]},
			pos -> Map[
				With[{ppos = Replace[{} -> {{}}] /@ pos, res = wrap[#, head]},
				If[ returnTokens,
					res,
					Activate[#, Splice] & @ ReplacePart[
						expr,
						List @@ Thread[
							If[ Length[res] > Length[pos],
								head @@ ppos -> Append[#1, If[head === List, Inactive[Splice], Apply[head]] @ #2] & @@
									TakeDrop[res, Length[pos] - 1],
								head @@ Take[ppos, Length[res]] -> res
							],
							head
						]
					]
				]
				] &,
				DeleteDuplicates @ ReplaceList[head @@ subExpr, ReplacePart[rule, 1 -> lhs]]
			]
		],
		Extract[positions, #] & /@ Switch[
			OptionValue["Mode"],
			"Tuples",
			TuplePosition[values, listLhs],
			"OrderedTuples",
			OrderedTuplePosition[values, listLhs],
			"Subsets",
			subsetPosition[values, listLhs],
			_,
			{}
		]
	]
]

Options[multiReplace] := Options[ResourceFunction["SubexpressionPositions"]] ~Join~ Options[iMultiReplace];

multiReplace[expr_, rule_ ? RuleQ, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] :=
	iMultiReplace[expr, rule,
		ResourceFunction["SubexpressionPositions"][
			expr,
			level,
			Sequence @@ FilterRules[
				{opts},
				Options[ResourceFunction["SubexpressionPositions"]]
			]
		],
		head,
		FilterRules[
			{opts},
			Options[iMultiReplace]
		]
	]

multiReplace[expr_, rules : {(_ ? RuleQ)..}, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] :=
With[{subExprPos = ResourceFunction["SubexpressionPositions"][expr, level, Sequence @@ FilterRules[
		{opts},
		Options[ResourceFunction["SubexpressionPositions"]]
	]]},
	Association @ MapIndexed[
		KeyMap[List /* Prepend[First @ #2]] @ iMultiReplace[expr, #1, subExprPos, head, FilterRules[{opts}, Options[iMultiReplace]]] &,
		rules
	]
]


Options[MultiReplace] := Options[multiReplace] ~Join~ {Method -> "Substitution"}

MultiReplace[expr_, rule_, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] :=
Switch[OptionValue[MultiReplace, {opts}, Method],
	"Cosubstitution",
	MultiCoReplace[expr, rule, level, head, FilterRules[{opts}, Options[MultiCoReplace]]],
	"Bisubstitution",
	MultiBiReplace[expr, rule, level, head, FilterRules[{opts}, Options[MultiBiReplace]]],
	_,
	multiReplace[expr, rule, level, head, FilterRules[{opts}, Options[multiReplace]]]
]


MultiStringReplace[s_String, rule_Rule] := Module[{
	lhs = wrap[First[rule]],
	rhs = wrap[Last[rule]],
	pos
},
	pos = StringPosition[s, #] & /@ lhs;
	AssociationMap[
		StringReplacePart[s, Take[rhs, UpTo[Length[#]]], Take[#, UpTo[Length[rhs]]]] &,
		ResourceFunction["SelectTuples"][pos, Length[#] == 1 || IntervalIntersection @@ (Interval /@ #) === Interval[] &]
	]
]

MultiStringReplace[s_String, rules : {_Rule...}] :=
	Association @ MapIndexed[KeyMap[List /* Prepend[First[#2]]] @ MultiStringReplace[s, #1] &, rules]

