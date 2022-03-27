Package["Wolfram`Metamathematics`"]


PackageExport["unify"]
PackageExport["lexicographicPatternSort"]
PackageExport["unifier"]
PackageExport["disagreementSet"]



Options[unify] := {Heads -> True};

unify[x_, y_, patt : Except[OptionsPattern[]] : _Pattern, opts : OptionsPattern[]] := Enclose[
Module[{
    pos = Position[x, patt, Heads -> OptionValue[unify, {opts}, Heads]],
    patts
},
    patts = DeleteDuplicates[Extract[x, pos]];

    ReleaseHold /@ Association @ DeleteCases[\[FormalX]_ -> Hold[\[FormalX]_]] @ MapThread[Rule, {patts, #}] & /@
        ConfirmBy[ReplaceList[y, With[{holdPatts = Hold /@ patts},
            makeReplaceRule[MapAt[Replace[s_Symbol :> Pattern @@ {s, Blank[]}], x, pos], holdPatts]]], Length[#] > 0 &]
],
    Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify `` with ``", "MessageParameters" -> {x, y}|>] &
]


lexicographicPatternSort[expr_] := ReverseSortBy[SortBy[expr, PatternsToSymbols], MatchQ[_Pattern]]


disagreementSet[term_ ...] := {}

disagreementSet[terms : Except[Pattern, term_][___]...] :=
    Enclose[lexicographicPatternSort[Union @@ MapThread[disagreementSet, ConfirmBy[List @@@ {terms}, Map[Length] /* Apply[Equal]]]]]

disagreementSet[terms___] := {lexicographicPatternSort @ Union @ {terms}}


iunifier[terms_List, substitution_Association] := Module[{newTerms, ds, s, t},
    newTerms = terms /. substitution;
    ds = disagreementSet @@ newTerms;
    If[ ds === {}, Return[substitution]];
    If[ FailureQ[ds],
        Return[Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify ``", "MessageParameters" -> {terms}|>]]
    ];
    {s, t} = First[ds];
    If[! MatchQ[s, _Pattern] || ! FreeQ[t, Verbatim[s]],
        Return[Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify `` and ``", "MessageParameters" -> {s, t}|>]]
    ];
    iunifier[terms, <|ReplaceAll[<|s -> t|>] /@ substitution, s -> t|>]
]

unifier[terms___] := iunifier[{terms}, <||>]

