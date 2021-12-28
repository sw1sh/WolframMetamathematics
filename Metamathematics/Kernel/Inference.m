Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["substitutionLemmas"]
PackageExport["coSubstitutionLemmas"]
PackageExport["paraSubstitutionLemmas"]



Options[paraSubstitutionLemmas] = {
    Heads -> False,
    "Identity" -> False,
    "Uniquify" -> True,
    "Canonicalize" -> False
};

paraSubstitutionLemmas[expr_, rule_Rule, OptionsPattern[]] := Cond[TrueQ[OptionValue["Canonicalize"]], canonicalizePatterns] /@
    Association @ KeyValueMap[{k, v} |-> MapIndexed[{k, First @ #2} -> #1 &, v]] @
        MultiParaReplace[expr,
            makeReplaceRule @@ Cond[TrueQ @ OptionValue["Uniquify"], Block[{$ModuleNumber = 1}, uniquifyPatterns[#]] &][rule],
            "InnerMatch" -> Except[_TwoWayRule] -> {},
            "OuterMatch" -> Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})],
            "OuterMode" -> All,
            Heads -> OptionValue[Heads]
        ]

paraSubstitutionLemmas[expr_, twr_TwoWayRule, opts : OptionsPattern[]] :=
    Association @ {
        KeyMap[Prepend[Right]] @ paraSubstitutionLemmas[expr, Rule @@ twr, opts],
        KeyMap[Prepend[Left]] @ paraSubstitutionLemmas[expr, Rule @@ Reverse @ twr, opts],
        If[ TrueQ @ OptionValue["Identity"],
            {None, {}, 1} -> expr,
            Nothing
        ]
    }

paraSubstitutionLemmas[expr_, rules_List, opts : OptionsPattern[]] :=
    Association @ MapIndexed[{rule, pos} |->
        KeyMap[Prepend[First @ pos], paraSubstitutionLemmas[expr, rule, opts]],
        rules
    ]

paraSubstitutionLemmas[rule : _TwoWayRule | _ ? RuleQ | _List, opts : OptionsPattern[]][expr_] := paraSubstitutionLemmas[expr, rule, opts]



Options[coSubstitutionLemmas] = {
    Heads -> False,
    "Identity" -> False,
    "Uniquify" -> True,
    "Canonicalize" -> False
};

coSubstitutionLemmas[expr_, rule_Rule, OptionsPattern[]] := Cond[TrueQ[OptionValue["Canonicalize"]], canonicalizePatterns] /@
    Association @ KeyValueMap[{k, v} |-> MapIndexed[{k, First @ #2} -> #1 &, v]] @
        MultiCoReplace[expr,
            makeReplaceRule @@ Cond[TrueQ @ OptionValue["Uniquify"], Block[{$ModuleNumber = 1}, uniquifyPatterns[#]] &][rule],
            "InnerMatch" -> Except[_TwoWayRule] -> {},
            "OuterMatch" -> HoldPattern[Except[((_Pattern | _Condition) -> {__}) | (_PatternTest -> {Except[1], ___})]],
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
    "Uniquify" -> True,
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

