Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["substitutionLemmas"]
PackageExport["coSubstitutionLemmas"]



Options[coSubstitutionLemmas] = {
    Heads -> False,
    "Identity" -> False,
    "Uniquify" -> False,
    "Canonicalize" -> False
};

coSubstitutionLemmas[expr_, rule_Rule, OptionsPattern[]] := Cond[TrueQ[OptionValue["Canonicalize"]], canonicalizePatterns] /@
    Association @ KeyValueMap[{k, v} |-> MapIndexed[{k, First @ #2} -> #1 &, v]] @
        MultiCoReplace[expr,
            makeReplaceRule @@ Cond[TrueQ @ OptionValue["Uniquify"], Block[{$ModuleNumber = 1}, uniquifyPatterns[#]] &][rule],
            "InnerMatch" -> Except[_TwoWayRule] -> {},
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All,
            Heads -> OptionValue[Heads]
        ]

coSubstitutionLemmas[expr_, twr_TwoWayRule, opts : OptionsPattern[]] :=
    Association @ {
        KeyMap[Prepend[Right]] @ coSubstitutionLemmas[expr, Rule @@ twr, opts],
        KeyMap[Prepend[Left]] @ coSubstitutionLemmas[expr, Rule @@ Reverse @ twr, opts],
        If[ TrueQ @ OptionValue["Identity"],
            {None, {}, 1} -> expr,
            Nothing
        ]
    }

coSubstitutionLemmas[expr_, rules_List, opts : OptionsPattern[]] :=
    Association @ MapIndexed[{rule, pos} |->
        KeyMap[Prepend[First @ pos], coSubstitutionLemmas[expr, rule, opts]],
        rules
    ]

coSubstitutionLemmas[rule : _TwoWayRule | _ ? RuleQ | _List, opts : OptionsPattern[]][expr_] := coSubstitutionLemmas[expr, rule, opts]


Options[substitutionLemmas] = {
    Heads -> False,
    "Identity" -> False,
    "Uniquify" -> False,
    "Canonicalize" -> False
};

substitutionLemmas[expr_, rule_Rule, OptionsPattern[]] := Cond[TrueQ@OptionValue["Canonicalize"], canonicalizePatterns] /@
    Association @ KeyValueMap[{k, v} |-> MapIndexed[{k, First @ #2} -> #1 &, v]] @
        MultiReplace[expr,
            makeReplaceRule @@ Cond[TrueQ @ OptionValue["Uniquify"], Block[{$ModuleNumber = 1}, uniquifyPatterns[#]] &][rule],
            "InnerMatch" -> Except[_TwoWayRule] -> {},
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All,
            Heads -> OptionValue[Heads]
        ]

substitutionLemmas[expr_, twr_TwoWayRule, opts : OptionsPattern[]] := Association @@ {
    KeyMap[Prepend[Right]] @ substitutionLemmas[expr, Rule @@ twr, opts],
    KeyMap[Prepend[Left]] @ substitutionLemmas[expr, Rule @@ Reverse @ twr, opts],
    If[ TrueQ @ OptionValue["Identity"],
        {None, {}, 1} -> expr,
        Nothing
    ]
}

substitutionLemmas[expr_, rules_List, opts : OptionsPattern[]] :=  Association@
    MapIndexed[{rule, pos} |->
        KeyMap[Prepend[First@pos], substitutionLemmas[expr, rule, opts]],
        rules
    ]

substitutionLemmas[rule : _TwoWayRule | _ ? RuleQ | _List,  opts : OptionsPattern[]][expr_] := substitutionLemmas[expr, rule, opts]

