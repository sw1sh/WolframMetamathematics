Package["Wolfram`Metamathematics`"]

PackageExport["SubexpressionPositions"]



Options[SubexpressionPositions] := {
    "OuterMatch" -> _ -> _,
    "InnerMatch" -> _ -> _,
    "OuterMode" -> "Any",
    "InnerMode" -> "Any",
    "Complement" -> False,
    Heads -> True
};

SubexpressionPositions[expr_, positions : {{_Integer ...} ...}, OptionsPattern[]] := Enclose @ Association @ Map[
    With[{
       subExpr = If[# === {}, expr, ConfirmQuiet @ Extract[expr, #]],
       outerExpressions = Extract[expr, mosts[#]]
    },
        If[
            If[OptionValue["Complement"], Not, Identity][
                If[ OptionValue["OuterMode"] === All, AllTrue, AnyTrue][
                    Thread[outerExpressions -> Reverse @ rests[#]],
                    MatchQ[OptionValue["OuterMatch"]]
                ] &&

                With[{innerPositions = Position[subExpr, _, Heads -> OptionValue[Heads]]},
                    If[ OptionValue["InnerMode"] === All, AllTrue, AnyTrue][
                        Thread[Extract[subExpr, innerPositions] -> innerPositions],
                        MatchQ[OptionValue["InnerMatch"]]
                    ]
                ]
            ],
            # -> subExpr,
            Nothing
        ]
    ] &,
    positions
]

SubexpressionPositions[expr_, levelspec : Except[OptionsPattern[]], opts : OptionsPattern[]] := SubexpressionPositions[
    expr,
    Position[expr, _, levelspec, Heads -> OptionValue[SubexpressionPositions, {opts}, Heads]],
    opts
]

SubexpressionPositions[expr_, opts : OptionsPattern[]] := SubexpressionPositions[expr, All, opts]

