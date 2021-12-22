Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["rests"]
PackageExport["mosts"]
PackageExport["extract"]
PackageExport["replacePart"]
PackageExport["mapAt"]
PackageExport["replaceAllUnderHold"]
PackageExport["MapAtInplace"]
PackageExport["uniquifyPatterns"]
PackageExport["canonicalizePatterns"]
PackageExport["formalizePatterns"]
PackageExport["makeReplaceRule"]
PackageExport["makePatternRule"]
PackageExport["symbolifyPatterns"]



rests[l_List] := NestList[Rest, l, Length @ l]


mosts[l_List] := NestList[Most, l, Length @ l]


extract[expr_, pos : {_Integer ...}] :=  If[pos === {}, expr, Enclose[
	ConfirmQuiet[Extract[expr, pos], {Extract::partd, Extract::partw}],
    Missing[ReleaseHold @ #["HeldMessageName"]] &]
]


replacePart[expr_, pos : {_Integer ...} -> part_] := If[pos === {}, part, ReplacePart[expr, pos -> part]]


mapAt[f_, expr_, pos_] := If[pos === {}, f @ expr, MapAt[f, expr, pos]]

mapAt[f_, pos_][expr_] := mapAt[f, expr, pos]


Options[replaceUnderHold] = Options[Position];

replaceAllUnderHold[expr_, rule_ ? RuleQ, opts : OptionsPattern[]] := replaceAllUnderHold[expr, {rule}, opts]

replaceAllUnderHold[expr_, rules : {_ ? RuleQ...}, opts : OptionsPattern[]] := With[{
	pos = Position[Unevaluated[expr], Alternatives @@ rules[[All, 1]], opts]
},
	ReplacePart[Unevaluated[expr], Thread[pos -> Replace[rules] /@ Extract[Unevaluated[expr], pos]]]
]

replaceAllUnderHold[rules_, opts : OptionsPattern[]] := Function[expr, replaceAllUnderHold[expr, rules, opts]]


MapAtInplace[f_, expr_, pos_] := ReplacePart[expr, Extract[expr, pos, f], pos]


uniquifyPatterns[expr_] := ReplaceAll[expr,
	Union @ Cases[expr, x_Pattern, All, Heads -> True] /.
	x_Pattern :> Verbatim[x] -> Pattern @@ {Unique[Symbol @ First @ StringSplit[SymbolName @ First @ x, "$"]], Last @ x}
]

uniquifyPatterns[expr1_, expr2_] := ReplaceAll[expr1,
	Intersection[Cases[expr1, _Pattern, All, Heads -> True], Cases[expr2, _Pattern, All, Heads -> True]] /.
	x_Pattern :> Verbatim[x] -> Pattern @@ {Unique[Symbol @ First @ StringSplit[SymbolName @ First @ x, "$"]], Last @ x}
]


canonicalizePatterns[expr_] := ReplaceAll[expr,
	MapIndexed[
		With[{canonical = Pattern @@ {Symbol @ Extract[Alphabet[], #2], Last @ #1}}, Verbatim[#1] :> canonical] &,
		DeleteDuplicates @ Cases[expr, _Pattern, All, Heads -> True]
	]
]

canonicalizePatterns[expr1_, expr2_] := ReplaceAll[expr1,
	MapIndexed[
		With[{canonical = Pattern @@ {Symbol @ Extract[Alphabet[], #2], Last @ #1}}, Verbatim[#1] :> canonical] &,
		Intersection[Cases[expr1, _Pattern, All, Heads -> True], Cases[expr2, _Pattern, All, Heads -> True]]
	]
]


formalizePatterns[expr_] := replaceAllUnderHold[expr, Verbatim[Pattern][name_Symbol, _] :> ResourceFunction["FormalizeSymbols"][name]]


SetAttributes[makeReplaceRule, HoldRest]
makeReplaceRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (Verbatim[#] -> First[#] & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
	ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]


SetAttributes[makePatternRule, HoldRest]
makePatternRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (First[#] -> # & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
	ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]


symbolifyPatterns[expr_] := replaceAllUnderHold[expr, p_Pattern :> First[p]]

