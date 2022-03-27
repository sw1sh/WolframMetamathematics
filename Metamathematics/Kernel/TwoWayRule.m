Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["TwoWayRuleMultiReplace"]
PackageExport["TwoWayRuleMultiReplaceList"]
PackageExport["TwoWayRuleMultiReplaceGraphList"]



Options[TwoWayRuleMultiReplace] := Normal @ Merge[First] @ Join[{
        "MaxDepth" -> Infinity,
        "MaxLeafCount" -> Infinity,
        "Deduplicate" -> False,
        "Substitution" -> True,
        "Cosubstitution" -> False,
        "Bisubstitution" -> False,
        (* rules:{_TwoWayRule..} |-> {{Subscript[i, 1], Subscript[j, 
        1]}, {Subscript[i, 2],Subscript[j, 2]}, ...} - 
        list of rule index pairs to combine with each other *)
        "RuleSelectionFunction" -> Automatic,
        Heads -> False
    },
    DeleteCases[Options[TwoWayMultiReplace], Method -> _]
];

TwoWayRuleMultiReplace[rules : {_TwoWayRule ..}, opts : OptionsPattern[]] := Module[{
    ruleIndices = (OptionValue["RuleSelectionFunction"] /. Automatic -> (Tuples[Range @ Length @ #, {2}] &))[rules],
    lemmas
},

    (* add substitution lemmas *)

    lemmas = If[
        TrueQ @ OptionValue @ "Substitution",
        Association @@ (
            KeyMap[Prepend["Substitution"] @* Prepend[{#1, #2}]] @
            TwoWayMultiReplace[rules[[#1]], rules[[#2]],  Method -> "Substitution", FilterRules[{opts}, Options[TwoWayMultiReplace]]] & @@@ ruleIndices
        ),
        <||>
    ];

    (* add cosubstitution lemmas *)

    If[ TrueQ @ OptionValue @ "Cosubstitution",
        lemmas = Association[lemmas,
            Association @@ (
                KeyMap[Prepend["Cosubstitution"] @* Prepend[{#1, #2}]]@
                TwoWayMultiReplace[rules[[#1]], rules[[#2]],  Method -> "Cosubstitution", FilterRules[{opts}, Options[TwoWayMultiReplace]]] & @@@ ruleIndices
            )
        ]
    ];

    (* add bisubstitution lemmas *)

    If[ TrueQ @ OptionValue @ "Bisubstitution",
        lemmas = Association[lemmas,
            Association @@ (
                KeyMap[Prepend["Bisubstitution"] @* Prepend[{#1, #2}]]@
                TwoWayMultiReplace[rules[[#1]], rules[[#2]], Method -> "Bisubstitution", FilterRules[{opts}, Options[TwoWayMultiReplace]]] & @@@ ruleIndices
            )
        ]
    ];

    lemmas = DeleteCases[lemmas,
        expr_ /; Depth[expr] > OptionValue["MaxDepth"] || LeafCount[expr] > OptionValue["MaxLeafCount"]
    ];

    lemmas = Association @ If[TrueQ[OptionValue["Deduplicate"]],
        With[{counts = Counts[DeleteCases[lemmas, Alternatives @@ Verbatim /@ rules]]},
            KeyValueMap[Append[#1, Lookup[counts, #2, 0]] -> #2 &]@
            DeleteDuplicatesBy[lemmas, CanonicalizePatterns @* Sort](*
            DeleteDuplicates[
                lemmas,
                MatchQ[#1,#2]&&MatchQ[#2,#1]||#1===Reverse[#2]&
            ]*)
        ],
        KeyValueMap[Append[#1, If[MatchQ[#2, Alternatives @@ Verbatim /@ rules], 0, 1]] -> #2 &, lemmas]
     ];

    lemmas
]


Options[TwoWayRuleMultiReplaceList] := Join[{"Sample" -> Infinity}, Options[TwoWayRuleMultiReplace]];

TwoWayRuleMultiReplaceList[rules : {_TwoWayRule ...}, n_Integer : 1, opts : OptionsPattern[]] :=
Rest @ NestList[
    Module[{
        newRules = Take[Values @ KeySortBy[#, Minus @* Last], UpTo[OptionValue["Sample"]]],
        result
    },
        result = TwoWayRuleMultiReplace[newRules, FilterRules[{opts}, Options[TwoWayRuleMultiReplace]]];
        Association[#, KeyMap[MapAt[DeleteDuplicates @ newRules[[#]] &, 2]] @ result]
    ] &,
    Association @ MapIndexed[{"Init", {}, #2, 0} -> #1 &, rules],
    n
]


Options[TwoWayRuleMultiReplaceGraphList] := Join[Options[TwoWayRuleMultiReplaceList], Options[Graph]];

TwoWayMultiRuleReplaceGraphList[rules : {_TwoWayRule ...}, n_Integer : 1, opts : OptionsPattern[]] :=
    Prepend[
        Graph[#,
            VertexLabels -> Placed["Name", Tooltip],
            EdgeLabels -> Placed["EdgeTag", Tooltip], AspectRatio -> 1 / 2,
            FilterRules[{opts}, Options[Graph]]
        ] & /@
        Catenate @* KeyValueMap[{info, v} |->
            MapIndexed[
                DirectedEdge[#1, v, Row[{First@#2, ":", Rest @ info}]] &,
                info[[2]]
            ]] /@ TwoWayRuleMultiReplaceList[rules, n, FilterRules[{opts}, Options[TwoWayRuleMultiReplaceList]]],

        Graph[rules, {}, VertexLabels -> Placed["Name", Tooltip], FilterRules[{opts}, Options[Graph]]]
    ]

