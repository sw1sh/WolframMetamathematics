Package["Wolfram`Metamathematics`"]


PackageExport["unify"]
PackageExport["unifier"]



Options[unify] = {Heads -> True};

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


unifier[p_Pattern, expr_] := <|p -> expr|>

unifier[expr_, p_Pattern] := <|p -> expr|>

unifier[x : h1_[rest1___], y : h2_[rest2___]] /; Length[{rest1}] == Length[{rest2}] := Enclose[With[{
	u = Association @ ConfirmBy[
		DeleteDuplicates @ Prepend[Confirm @ unifier[h1, h2]] @ MapThread[Confirm @ unifier @@ Sort[{##}] &, {{rest1}, {rest2}}],
		AllTrue[#, AssociationQ] && DuplicateFreeQ @ Catenate[Keys /@ #] &
	]
},
	With[{substituion = Normal @ KeyMap[Verbatim, u]}, # /. substituion & /@ u]
],
	Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify `` and ``", "MessageParameters" -> {x, y}|>] &
]

unifier[expr_, expr_] := <||>

unifier[x_, y_] := Failure["NonUnifiable", <|"MessageTemplate" -> "Can't unify `` and ``", "MessageParameters" -> {x, y}|>]

