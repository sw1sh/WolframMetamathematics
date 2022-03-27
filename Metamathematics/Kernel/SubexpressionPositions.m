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
       subExpr = If[# === {}, Unevaluated @@ Hold @ expr, ConfirmQuiet @ Extract[Unevaluated @ expr, #, Unevaluated]],
       outerExpressions = Extract[Unevaluated @ expr, mosts[#], Hold],
       outerMatch = OptionValue["OuterMatch"],
       innerMatch = OptionValue["InnerMatch"]
    },
        If[
            If[ OptionValue["Complement"], Not, Identity][
                If[ OptionValue["OuterMode"] === All, AllTrue, AnyTrue][
                    Thread[outerExpressions -> Reverse @ rests[#]],
                    MatchQ[FirstAt[HoldForm @ #, {1, 1}], HoldForm @ outerMatch] &
                ] &&

                With[{innerPositions = Position[subExpr, _, Heads -> OptionValue[Heads]]},
                    If[ OptionValue["InnerMode"] === All, AllTrue, AnyTrue][
                        Thread[Extract[subExpr, innerPositions, Hold] -> innerPositions],
                        MatchQ[FirstAt[HoldForm @ #, {1, 1}], HoldForm @ innerMatch] &
                    ]
                ]
            ],
            # :> subExpr,
            Nothing
        ]
    ] &,
    positions
]

SubexpressionPositions[expr_, levelspec : Except[OptionsPattern[]], opts : OptionsPattern[]] := SubexpressionPositions[
    Unevaluated @ expr,
    Position[Unevaluated @ expr, _, levelspec, Heads -> OptionValue[SubexpressionPositions, {opts}, Heads]],
    opts
]

SubexpressionPositions[expr_, opts : OptionsPattern[]] := SubexpressionPositions[Unevaluated @ expr, All, opts]

