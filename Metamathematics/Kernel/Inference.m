Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["TwoWayMultiReplace"]



Options[TwoWayMultiReplace] := {
    Heads -> False,
    "Identity" -> False,
    "Uniquify" -> True,
    "Canonicalize" -> False,
    Method -> "Substitution"
} ~Join~ Options[CanonicalizePatterns];

TwoWayMultiReplace[expr_, rule_ ? RuleQ, opts : OptionsPattern[]] := Cond[TrueQ @ OptionValue["Canonicalize"],
    CanonicalizePatterns[#, FilterRules[{opts}, Options[CanonicalizePatterns]]] &] /@
    Association @ KeyValueMap[{k, v} |-> MapIndexed[{k, First @ #2} -> #1 &, v]] @
        MultiReplace[expr,
            makeReplaceRule @@ Cond[TrueQ @ OptionValue["Uniquify"], Block[{$ModuleNumber = 1}, uniquifyPatterns[#]] &][rule],
            "InnerMatch" -> Except[_TwoWayRule] -> {},
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All,
            Method -> OptionValue[Method],
            Heads -> OptionValue[Heads]
        ]

TwoWayMultiReplace[expr_, twr_TwoWayRule, opts : OptionsPattern[]] := Association @@ {
    KeyMap[Prepend[Right]] @ TwoWayMultiReplace[expr, Rule @@ twr, opts],
    KeyMap[Prepend[Left]] @ TwoWayMultiReplace[expr, Rule @@ Reverse @ twr, opts],
    If[ TrueQ @ OptionValue["Identity"],
        {None, {}, 1} -> expr,
        Nothing
    ]
}

TwoWayMultiReplace[expr_, rules_List, opts : OptionsPattern[]] :=  Association@
    MapIndexed[{rule, pos} |->
        KeyMap[Prepend[First @ pos], TwoWayMultiReplace[expr, rule, opts]],
        rules
    ]

TwoWayMultiReplace[rule : _TwoWayRule | _ ? RuleQ | _List,  opts : OptionsPattern[]][expr_] := TwoWayMultiReplace[expr, rule, opts]

