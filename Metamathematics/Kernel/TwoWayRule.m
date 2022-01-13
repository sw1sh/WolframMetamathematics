Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["TwoWayMultiReplace"]
PackageExport["TwoWayMultiReplaceList"]
PackageExport["TwoWayMultiReplaceGraphList"]



Options[TwoWayMultiReplace] := Normal @ Merge[First] @ Join[{
        "MaxDepth" -> Infinity,
        "MaxLeafCount" -> Infinity,
        "Deduplicate" -> False,
        "SubstitutionLemmas" -> True,
        "CoSubstitutionLemmas" -> False,
        "ParaSubstitutionLemmas" -> False,
        (* rules:{_TwoWayRule..} |-> {{Subscript[i, 1], Subscript[j, 
        1]}, {Subscript[i, 2],Subscript[j, 2]}, ...} - 
        list of rule index pairs to combine with each other *)
        "RuleSelectionFunction" -> Automatic,
        Heads -> False
    },
    Options[substitutionLemmas],
    Options[coSubstitutionLemmas],
    Options[paraSubstitutionLemmas]
];

TwoWayMultiReplace[rules : {_TwoWayRule ..}, opts : OptionsPattern[]] := Module[{
    ruleIndices = (OptionValue["RuleSelectionFunction"] /. Automatic -> (Tuples[Range @ Length @ #, {2}] &))[rules],
    lemmas
},

    (* add substitution lemmas *)

    lemmas = If[
        TrueQ @ OptionValue @ "SubstitutionLemmas",
        Association @@ (
            KeyMap[Prepend["Substitution"] @* Prepend[{#1, #2}]] @
            substitutionLemmas[rules[[#1]], rules[[#2]], FilterRules[{opts}, Options[substitutionLemmas]]] & @@@ ruleIndices
        ),
        <||>
    ];

    (* add cosubstitution lemmas *)

    If[ TrueQ @ OptionValue @ "CoSubstitutionLemmas",
        lemmas = Association[lemmas,
            Association @@ (
                KeyMap[Prepend["CoSubstitution"] @* Prepend[{#1, #2}]]@
                coSubstitutionLemmas[rules[[#1]], rules[[#2]], FilterRules[{opts}, Options[coSubstitutionLemmas]]] & @@@ ruleIndices
            )
        ]
    ];

    (* add parasubstitution lemmas *)

    If[ TrueQ @ OptionValue @ "ParaSubstitutionLemmas",
        lemmas = Association[lemmas,
            Association @@ (
                KeyMap[Prepend["ParaSubstitution"] @* Prepend[{#1, #2}]]@
                paraSubstitutionLemmas[rules[[#1]], rules[[#2]], FilterRules[{opts}, Options[paraSubstitutionLemmas]]] & @@@ ruleIndices
            )
        ]
    ];

    lemmas = DeleteCases[lemmas,
        expr_ /; Depth[expr] > OptionValue["MaxDepth"] || LeafCount[expr] > OptionValue["MaxLeafCount"]
    ];

    lemmas = Association @ If[TrueQ[OptionValue["Deduplicate"]],
        With[{counts = Counts[DeleteCases[lemmas, Alternatives @@ Verbatim /@ rules]]},
            KeyValueMap[Append[#1, Lookup[counts, #2, 0]] -> #2 &]@
            DeleteDuplicatesBy[lemmas, canonicalizePatterns @* Sort](*
            DeleteDuplicates[
                lemmas,
                MatchQ[#1,#2]&&MatchQ[#2,#1]||#1===Reverse[#2]&
            ]*)
        ],
        KeyValueMap[Append[#1, If[MatchQ[#2, Alternatives @@ Verbatim /@ rules], 0, 1]] -> #2 &, lemmas]
     ];

    lemmas
]


Options[TwoWayMultiReplaceList] := Join[{"Sample" -> Infinity}, Options[TwoWayMultiReplace]];

TwoWayMultiReplaceList[rules : {_TwoWayRule ...}, n_Integer : 1, opts : OptionsPattern[]] :=
Rest @ NestList[
    Module[{
        newRules = Take[Values @ KeySortBy[#, Minus @* Last], UpTo[OptionValue["Sample"]]],
        result
    },
        result = TwoWayMultiReplace[newRules, FilterRules[{opts}, Options[TwoWayMultiReplace]]];
        Association[#, KeyMap[MapAt[DeleteDuplicates @ newRules[[#]] &, 1]] @ result]
    ] &,
    Association@MapIndexed[{{}, #2, 0} -> #1 &, rules],
    n
]


Options[TwoWayMultiReplaceGraphList] := Join[Options[TwoWayMultiReplaceList], Options[Graph]];

TwoWayMultiReplaceGraphList[rules : {_TwoWayRule ...}, n_Integer : 1, opts : OptionsPattern[]] :=
    Prepend[
        Graph[#,
            VertexLabels -> Placed["Name", Tooltip],
            EdgeLabels -> Placed["EdgeTag", Tooltip], AspectRatio -> 1 / 2,
            FilterRules[{opts}, Options[Graph]]
        ] & /@
        Catenate @* KeyValueMap[{info, v} |->
            MapIndexed[
                DirectedEdge[#1, v, Row[{First@#2, ":", Rest @ info}]] &,
                First @ info
            ]] /@ TwoWayMultiReplaceList[rules, n, FilterRules[{opts}, Options[TwoWayMultiReplaceList]]],

        Graph[rules, {}, VertexLabels -> Placed["Name", Tooltip], FilterRules[{opts}, Options[Graph]]]
    ]

