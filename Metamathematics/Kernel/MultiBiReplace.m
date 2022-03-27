Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["MultiBiUnify"]
PackageExport["MultiBiReplace"]

PackageExport["unifyAt"]
PackageExport["matchAt"]
PackageExport["replaceAt"]



Options[iMultiBiUnify] := Options[unifier] ~Join~ {"Mode" -> "Tuples"};

iMultiBiUnify[posSubExpr_, subset_, head_Symbol, opts : OptionsPattern[]] := Module[{
    positions, values,
    subsets = wrap[subset, head]
},
    positions = Keys[posSubExpr];
    values = Values[posSubExpr];
    DeleteCases[_ ? FailureQ] @ Association @ Map[pos |->
        Extract[positions, pos] ->
            With[{term = Extract[values, pos]}, unifier[head @@ term, subsets]],
        Switch[
            OptionValue["Mode"],
            "Tuples",
            Tuples[List /@ Range[Length[values]], Length[subsets]],
            "OrderedTuples",
            OrderedTuples[List /@ Range[Length[values]], Length[subsets]],
            "Subsets",
            Subsets[List /@ Range[Length[values]], {Length[subsets]}],
            _,
            {}
        ]
    ]

]


Options[MultiBiUnify] := Join[Options[SubexpressionPositions], Options[iMultiBiUnify]];

MultiBiUnify[expr_, subset_, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] := With[{
    posSubExpr = SubexpressionPositions[expr, level,
        FilterRules[{
            opts,
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All
        }, Options[SubexpressionPositions]]
    ]},

    iMultiBiUnify[posSubExpr, subset, head, FilterRules[{opts}, Options[iMultiBiUnify]]]
]


iMultiBiReplace[expr_, rule_ ? RuleQ, multiUnification_Association, head_Symbol, returnTokens_ : False] :=
    DeleteCases[{}] @ Association @ KeyValueMap[{pos, unifications} |-> pos -> DeleteDuplicates @ Catenate @ Map[unification |->
        With[{
            newExpr = expr /. unification,
            newRule = makeReplaceRule @@ (makePatternRule @@ rule /. unification)
        },
            Map[
                With[{ppos = Replace[{} -> {{}}] /@ pos, res = wrap[#, head]},
                If[ returnTokens,
                    res,
                    Activate[#, Splice] & @ ReplacePart[
                        newExpr,
                        List @@ Thread[
                            If[ Length[res] > Length[pos],
                                head @@ ppos -> Append[#1, Hold @ If[head === List, Inactive[Splice], Apply[head]] @ #2] & @@
                                    TakeDrop[res, Length[pos] - 1],
                                head @@ Take[ppos, Length[res]] -> res
                            ],
                            head
                        ]
                    ]
                ]
                ] &,
                ReplaceList[
                    wrap[First[newRule], head],
                    ReplacePart[newRule, 1 -> head @@ Extract[newExpr, pos]]
                ]
            ]
        ],
        wrap[unifications]
    ],
    multiUnification
]


Options[MultiBiReplace] := Join[Options[MultiBiUnify], {"ReturnTokens" -> False}];

MultiBiReplace[expr_, rule_ ? RuleQ, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] := With[{
    newRule = makeReplaceRule @@ Block[{$ModuleNumber = 1}, uniquifyPatterns[makePatternRule @@ rule]]
},
    iMultiBiReplace[expr, newRule, MultiBiUnify[expr, First[newRule], level, FilterRules[{opts}, Options[MultiBiUnify]]], head, TrueQ @ OptionValue[MultiBiReplace, {opts}, "ReturnTokens"]]
]

MultiBiReplace[expr_, rules : {_ ? RuleQ ...}, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] := With[{
    posSubExpr = SubexpressionPositions[expr, level,
        FilterRules[{
            opts,
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All
        }, Options[SubexpressionPositions]]
    ]},
    Association @ MapIndexed[
        KeyMap[
            List /* Prepend[First @ #2],
            With[{rule =  Block[{$ModuleNumber = 1}, uniquifyPatterns[#1]]},
                iMultiBiReplace[expr, rule, iMultiBiUnify[posSubExpr, First[rule], head, FilterRules[{opts}, Options[iMultiBiUnify]]], head, TrueQ @ OptionValue[MultiBiReplace, {opts}, "ReturnTokens"]]
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

