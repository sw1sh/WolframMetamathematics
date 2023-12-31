Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["MultiCoUnify"]
PackageExport["MultiCoReplace"]
PackageExport["unifyAt"]
PackageExport["CoMatchAt"]
PackageExport["CoReplaceAt"]



Options[iMultiCoUnify] := Options[unify] ~Join~ {"Mode" -> "Tuples"};

iMultiCoUnify[posSubExpr_, subset_, head_Symbol, opts : OptionsPattern[]] := Module[{
    positions, values,
    subsets = wrap[subset, head]
},
    positions = Keys[posSubExpr];
    values = Values[posSubExpr];
    DeleteCases[_ ? FailureQ] @ Association @ Map[pos |->
        Extract[positions, pos] ->
            With[{term = Extract[values, pos]}, unify[head @@ term, subsets, opts](* & /@ orderByPattern[term, head] @ subsets*)],
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


Options[MultiCoUnify] := Join[Options[SubexpressionPositions], Options[iMultiCoUnify]];

MultiCoUnify[expr_, subset_, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] := With[{
    posSubExpr = SubexpressionPositions[expr, level,
        FilterRules[{
            opts,
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All
        }, Options[SubexpressionPositions]]
    ]},

    iMultiCoUnify[posSubExpr, subset, head, FilterRules[{opts}, Options[iMultiCoUnify]]]
]


iMultiCoReplace[expr_, rule_ ? RuleQ, multiUnification_Association, head_Symbol, returnTokens_ : False] :=
    DeleteCases[{}] @ Association @ KeyValueMap[{pos, unifications} |-> pos -> DeleteDuplicates @ Catenate @ Map[unification |->
        With[{
            newExpr = expr /. unification
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
                    wrap[First[rule], head],
                    ReplacePart[rule, 1 -> head @@ Extract[newExpr, pos]]
                ]
            ]
        ],
        unifications
    ],
    multiUnification
]


Options[MultiCoReplace] := Join[Options[MultiCoUnify], {"ReturnTokens" -> False}];

MultiCoReplace[expr_, rule_ ? RuleQ,  level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] :=
    iMultiCoReplace[expr, rule, MultiCoUnify[expr, First[rule], level, FilterRules[{opts}, Options[MultiCoUnify]]], head, TrueQ @ OptionValue[MultiBiReplace, {opts}, "ReturnTokens"]]

MultiCoReplace[expr_, rules : {_ ? RuleQ ...}, level : Except[OptionsPattern[]] : All, head_Symbol : List, opts : OptionsPattern[]] := With[{
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
            iMultiCoReplace[expr, #1, iMultiCoUnify[posSubExpr, First[#1], head, FilterRules[{opts}, Options[iMultiCoUnify]]], head, TrueQ @ OptionValue[MultiBiReplace, {opts}, "ReturnTokens"]]
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

