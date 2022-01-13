Package["Wolfram`Metamathematics`"]

PackageImport["GeneralUtilities`"]


PackageExport["wrap"]
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
PackageExport["patternifySymbols"]



wrap[expr_, head_ : List] := Replace[expr, x : Except[_head] :> head[x]]


rests[l_List] := NestList[Rest, l, Length @ l]


mosts[l_List] := NestList[Most, l, Length @ l]


extract[expr_, pos : {_Integer ...}] :=  If[pos === {}, expr, Enclose[
	ConfirmQuiet[Extract[expr, pos], {Extract::partd, Extract::partw}],
    Missing[ReleaseHold @ #["HeldMessageName"]] &]
]


replacePart[expr_, pos : {_Integer ...} -> part_] := If[pos === {}, part, ReplacePart[expr, pos -> part]]

replacePart[expr_, rules_List] := ReplacePart[expr, MapAt[Replace[{} -> {{}}], {1}] /@ rules]


mapAt[f_, expr_, pos_] := If[pos === {}, f @ expr, MapAt[f, expr, pos]]

mapAt[f_, pos_][expr_] := mapAt[f, expr, pos]


Options[replaceUnderHold] := Options[Position];

replaceAllUnderHold[expr_, rule_ ? RuleQ, opts : OptionsPattern[]] := replaceAllUnderHold[expr, {rule}, opts]

replaceAllUnderHold[expr_, rules : {_ ? RuleQ...}, opts : OptionsPattern[]] := With[{
	pos = Position[Unevaluated[expr], Alternatives @@ rules[[All, 1]], opts]
},
	replacePart[Unevaluated[expr], Thread[pos -> Replace[rules] /@ Extract[Unevaluated[expr], pos]]]
]

replaceAllUnderHold[rules_, opts : OptionsPattern[]][expr_]:= replaceAllUnderHold[expr, rules, opts]


MapAtInplace[f_, expr_, pos_] := ReplacePart[expr, Extract[expr, pos, f], pos]

MapAtInplace[f_, pos_][expr_] := MapAtInplace[f, expr, pos]


uniquifyPatterns[expr_] := ReplaceAll[expr,
	Union @ Cases[expr, x_Pattern, All, Heads -> True] /.
	x_Pattern :> Verbatim[x] -> Pattern @@ {Unique[Symbol @ First @ StringSplit[SymbolName @ First @ x, "$"]], Last @ x}
]

uniquifyPatterns[expr1_, expr2_] := ReplaceAll[expr1,
	Intersection[Cases[expr1, _Pattern, All, Heads -> True], Cases[expr2, _Pattern, All, Heads -> True]] /.
	x_Pattern :> Verbatim[x] -> Pattern @@ {Unique[Symbol @ First @ StringSplit[SymbolName @ First @ x, "$"]], Last @ x}
]


Options[canonicalizePatterns] := {"SymbolNames" -> Automatic}

canonicalizePatterns[expr_, OptionsPattern[]] := Module[{
	chars = Replace[
		OptionValue["SymbolNames"],
		{
			Automatic -> Join[CharacterRange["\[FormalA]", "\[FormalZ]"], CharacterRange["\[FormalCapitalA]", "\[FormalCapitalZ]"]],
			"Alphabet" | Alphabet -> Alphabet[]
		}
	],
	patts = DeleteDuplicates @ Cases[expr, _Pattern, All, Heads -> True]
},
	chars = First @ NestWhile[Apply[{cs, n} |-> {Join[cs,  (# <> ToString[n]) & /@ cs], n + 1}], {chars, 1}, Length[#[[1]]] < Length[patts] &];
	ReplaceAll[expr,
		MapIndexed[
			With[{canonical = Pattern @@ {
					Symbol @ Extract[
						chars,
						#2
					],
					Last @ #1
				}},
				Verbatim[#1] :> canonical
			] &,
			patts
		]
	]
]

canonicalizePatterns[expr1_, expr2_] := ReplaceAll[expr1,
	MapIndexed[
		With[{canonical = Pattern @@ {Symbol @ Extract[Alphabet[], #2], Last @ #1}}, Verbatim[#1] :> canonical] &,
		Intersection[Cases[expr1, _Pattern, All, Heads -> True], Cases[expr2, _Pattern, All, Heads -> True]]
	]
]


formalizePatterns[expr_] := replaceAllUnderHold[expr, Verbatim[Pattern][name_Symbol, obj_] :> Pattern @@ {ResourceFunction["FormalizeSymbols"][name], obj}]


SetAttributes[makeReplaceRule, HoldRest]
makeReplaceRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (Verbatim[#] -> First[#] & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
	ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]


SetAttributes[makePatternRule, HoldRest]
makePatternRule[lhs_, rhs_] := With[{newRHS = ReplaceAll[Hold[rhs], (First[#] -> # & /@ DeleteDuplicates @ Cases[lhs, _Pattern, All, Heads -> True])]},
	ReleaseHold[RuleDelayed @@ {lhs, newRHS}]
]


symbolifyPatterns[expr_] := replaceAllUnderHold[expr, p_Pattern :> First[p]]


patternifySymbols[expr_, prefix_ : {"x", "y", "z"}] :=
	expr /. x_Symbol /; StringMatchQ[SymbolName[x], Alternatives @@ prefix ~~ DigitCharacter...] :> Pattern @@ {x, _}

